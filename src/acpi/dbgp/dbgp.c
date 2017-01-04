/*
 * Copyright (C) 2015-2017 Canonical
 *
 * Portions of this code original from the Linux-ready Firmware Developer Kit
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.
 *
 */
#include "fwts.h"

#if defined(FWTS_HAS_ACPI)

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <inttypes.h>
#include <string.h>

static fwts_acpi_table_info *table;

static int dbgp_init(fwts_framework *fw)
{

	if (fwts_acpi_find_table(fw, "DBGP", 0, &table) != FWTS_OK) {
		fwts_log_error(fw, "Cannot read ACPI tables.");
		return FWTS_ERROR;
	}
	if (table == NULL || (table && table->length == 0)) {
		fwts_log_error(fw, "ACPI DBGP table does not exist, skipping test");
		return FWTS_SKIP;
	}

	return FWTS_OK;
}

/*
 *  DBGP Table
 *   see https://msdn.microsoft.com/en-us/library/windows/hardware/dn639130%28v=vs.85%29.aspx
 */
static int dbgp_test1(fwts_framework *fw)
{
	bool passed = true;
	char *interface_type;
	fwts_acpi_table_dbgp *dbgp = (fwts_acpi_table_dbgp *)table->data;

	if (table->length < sizeof(fwts_acpi_table_dbgp)) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"DBGPTooShort",
			"DBGP table too short, expecting %zu bytes, "
			"instead got %zu bytes",
			sizeof(fwts_acpi_table_dbgp), table->length);
		goto done;
	}

	switch (dbgp->interface_type) {
	case 0:
		interface_type = "Full 16550 interface";
		break;
	case 1:
		interface_type = "16550 subset interface";
		break;
	default:
		interface_type = "Reserved";
		break;
	}

	fwts_log_info_verbatim(fw, "DBGP Table:");
	fwts_log_info_verbatim(fw, "  Interface Type            0x%2.2" PRIx8 " (%s)",
		dbgp->interface_type, interface_type);
	fwts_log_info_verbatim(fw, "  Reserved:                 0x%2.2" PRIx8, dbgp->reserved1[0]);
	fwts_log_info_verbatim(fw, "  Reserved:                 0x%2.2" PRIx8, dbgp->reserved1[1]);
	fwts_log_info_verbatim(fw, "  Reserved:                 0x%2.2" PRIx8, dbgp->reserved1[2]);
	fwts_log_info_verbatim(fw, "  Base Address:");
	fwts_log_info_verbatim(fw, "    Address Space ID:       0x%2.2" PRIx8, dbgp->base_address.address_space_id);
	fwts_log_info_verbatim(fw, "    Register Bit Width      0x%2.2" PRIx8, dbgp->base_address.register_bit_width);
	fwts_log_info_verbatim(fw, "    Register Bit Offset     0x%2.2" PRIx8, dbgp->base_address.register_bit_offset);
	fwts_log_info_verbatim(fw, "    Access Size             0x%2.2" PRIx8, dbgp->base_address.access_width);
	fwts_log_info_verbatim(fw, "    Address                 0x%16.16" PRIx64, dbgp->base_address.address);
	fwts_log_nl(fw);

	if (dbgp->interface_type > 2) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"DBGPReservedInterfaceType",
			"DBGP Interface Type is 0x%2.2" PRIx8
			" which is a reserved interface type. Expecting "
			" 0x00 (Full 16550) or 0x01 (16550 subset)",
			dbgp->interface_type);
	}
	if (dbgp->base_address.register_bit_width == 0) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"DBGPBaseAddrBitWidthZero",
			"DBGP Base Address Bit Width is zero.");
	}
	switch (dbgp->base_address.address_space_id) {
	case 0x05 ... 0x09:
	case 0x0b ... 0x7e:
	case 0x80 ... 0xbf:
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"DBGPBaseAddrAddrSpaceID",
			"DBGP Base Address, Address Space ID 0x%" PRIx8
			" which is a reserved value.",
			dbgp->base_address.address_space_id);
		break;
	default:
		break;
	}
done:
	if (passed)
		fwts_passed(fw, "No issues found in DBGP table.");

	return FWTS_OK;
}

static fwts_framework_minor_test dbgp_tests[] = {
	{ dbgp_test1, "DBGP (Debug Port) Table test." },
	{ NULL, NULL }
};

static fwts_framework_ops dbgp_ops = {
	.description = "DBGP (Debug Port) Table test.",
	.init        = dbgp_init,
	.minor_tests = dbgp_tests
};

FWTS_REGISTER("dbgp", &dbgp_ops, FWTS_TEST_ANYTIME, FWTS_FLAG_BATCH | FWTS_FLAG_TEST_ACPI)

#endif
