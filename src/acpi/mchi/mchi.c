/*
 * Copyright (C) 2015-2016 Canonical
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

#define DUMP_MCHI_TABLE		(1)	/* table is small and not used much, so dump it */

static fwts_acpi_table_info *table;

static int mchi_init(fwts_framework *fw)
{

	if (fwts_acpi_find_table(fw, "MCHI", 0, &table) != FWTS_OK) {
		fwts_log_error(fw, "Cannot read ACPI tables.");
		return FWTS_ERROR;
	}
	if (table == NULL || (table && table->length == 0)) {
		fwts_log_error(fw, "ACPI MCHI table does not exist, skipping test");
		return FWTS_SKIP;
	}

	return FWTS_OK;
}

/*
 *  MCHI Management Controller Host Interface Table
 *    http://www.dmtf.org/sites/default/files/standards/documents/DSP0256_1.0.0.pdf
 */
static int mchi_test1(fwts_framework *fw)
{
	bool passed = true;
	fwts_acpi_table_mchi *mchi = (fwts_acpi_table_mchi *)table->data;

	if (table->length < sizeof(fwts_acpi_table_mchi)) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"MCHITooShort",
			"MCHI table too short, expecting %zu bytes, "
			"instead got %zu bytes",
			sizeof(fwts_acpi_table_mchi), table->length);
		goto done;
	}

#if DUMP_MCHI_TABLE
	fwts_log_info_verbatum(fw, "MCHI Table:");
	fwts_log_info_verbatum(fw, "  Interface Type:           0x%2.2" PRIx8, mchi->interface_type);
	fwts_log_info_verbatum(fw, "  Protocol Identifier       0x%2.2" PRIx8, mchi->protocol_identifier);
	fwts_log_info_verbatum(fw, "  Protocol Data:            "
		"0x%2.2" PRIx8 " 0x%2.2" PRIx8 " 0x%2.2" PRIx8 " 0x%2.2" PRIx8,
			mchi->protocol_data[0], mchi->protocol_data[1],
			mchi->protocol_data[2], mchi->protocol_data[3]);
	fwts_log_info_verbatum(fw, "                            "
		"0x%2.2" PRIx8 " 0x%2.2" PRIx8 " 0x%2.2" PRIx8 " 0x%2.2" PRIx8,
			mchi->protocol_data[4], mchi->protocol_data[5],
			mchi->protocol_data[6], mchi->protocol_data[7]);
	fwts_log_info_verbatum(fw, "  Interrupt Type:           0x%2.2" PRIx8, mchi->interrupt_type);
	fwts_log_info_verbatum(fw, "  GPE:                      0x%2.2" PRIx8, mchi->gpe);
	fwts_log_info_verbatum(fw, "  PCI Device Flag:          0x%2.2" PRIx8, mchi->pci_device_flag);
	fwts_log_info_verbatum(fw, "  Global System Interrupt:  0x%8.8" PRIx32, mchi->global_system_interrupt);
	fwts_log_info_verbatum(fw, "  Base Address:");
	fwts_log_info_verbatum(fw, "    Address Space ID:       0x%2.2" PRIx8, mchi->base_address.address_space_id);
	fwts_log_info_verbatum(fw, "    Register Bit Width      0x%2.2" PRIx8, mchi->base_address.register_bit_width);
	fwts_log_info_verbatum(fw, "    Register Bit Offset     0x%2.2" PRIx8, mchi->base_address.register_bit_offset);
	fwts_log_info_verbatum(fw, "    Access Size             0x%2.2" PRIx8, mchi->base_address.access_width);
	fwts_log_info_verbatum(fw, "    Address                 0x%16.16" PRIx64, mchi->base_address.address);
	if ((mchi->pci_device_flag & 1) == 1) {
		fwts_log_info_verbatum(fw, "  PCI Segment Group:       0x%2.2" PRIx8, mchi->bytes[0]);
		fwts_log_info_verbatum(fw, "  PCI Bus Number:          0x%2.2" PRIx8, mchi->bytes[1]);
		fwts_log_info_verbatum(fw, "  PCI Device Number:       0x%2.2" PRIx8, mchi->bytes[2]);
		fwts_log_info_verbatum(fw, "  PCI Function Number:     0x%2.2" PRIx8, mchi->bytes[3]);
	} else {
		/* Zero -> UIDS */
		fwts_log_info_verbatum(fw, "  UID Bytes 1-4:            "
			"0x%2.2" PRIx8 " 0x%2.2" PRIx8 " 0x%2.2" PRIx8 " 0x%2.2" PRIx8,
			mchi->bytes[0], mchi->bytes[1], mchi->bytes[2], mchi->bytes[3]);
	}
	fwts_log_nl(fw);
#endif
	if ((mchi->interface_type < 2) ||
	    (mchi->interface_type > 8)) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"MCHIInvalidInterfaceType",
			"MCHI Interface Type is 0x%2.2" PRIx8 " which is reserved, "
			"allowed values are 0x02..0x08", mchi->interface_type);
	}
	if ((mchi->protocol_identifier > 2) &&
	    (mchi->protocol_identifier < 255)) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"MCHIInvalidProtocolIdentifier",
			"MCHI Protocol Identifier 0x%2.2" PRIx8 " which is reserved, "
			"allowed values are 0x00 (Unspecifier), 0x01 (MCTP), 0x02 (IPMI) or "
			"255 (OEM defined)", mchi->protocol_identifier);
	}
	if (mchi->interrupt_type & ~0x03) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"MCHIInterruptTypeReservedNonZero",
			"MCHI Interrupt Type 0x%2.2" PRIx8 " has some reserved "
			"bits [7:2] set, these should be all zero.",
			mchi->interrupt_type);
	}
	if (((mchi->interrupt_type & 0x01) == 0) &&
	    (mchi->gpe != 0)) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"MCHIGpeNonZero",
			"MCHI GPE is 0x%2.2" PRIx8 " and should be zero "
			"when bit 0 of the Interrupt Type field is 0 "
			"(SCI triggered through GPE non-supported)",
			mchi->gpe);
	}
	if (mchi->pci_device_flag & ~0x01) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"MCHIPciDeviceFlagReservedNonZero",
			"MCHI PCI Device Flag 0x%2.2" PRIx8 " has some reserved "
			"bits [7:1] set, these should be all zero.",
			mchi->pci_device_flag);
	}
	if (((mchi->interrupt_type & 0x02) == 0) &&
	    (mchi->global_system_interrupt != 0)) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"MCHIGsiNonZero",
			"MCHI Global System Interrupt is 0x%2.2" PRIx8 " and should be zero "
			"when bit 1 of the Interrupt Type field is 0",
			mchi->global_system_interrupt);
	}

	if ((mchi->base_address.address_space_id != 0x00) &&
	    (mchi->base_address.address_space_id != 0x01) &&
	    (mchi->base_address.address_space_id != 0x04)) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"MCHIAddrSpaceIdInvalid",
			"MCHI Address Space ID is 0x%2.2" PRIx8 " and should be "
			"0x00 (System Memory), 0x01 (System I/O) or 0x04 (SMBus)",
			mchi->base_address.address_space_id);
	}

	/* SMBus specific checks */
	if (mchi->base_address.address_space_id == 0x04) {
		if ((mchi->pci_device_flag & 0x01) == 1) {
			passed = false;
			fwts_failed(fw, LOG_LEVEL_HIGH,
				"MCHIPciDeviceFlagInvalid",
				"MCHI PCI Device Flag is 0x%2.2" PRIx8
				" and bit [0] should be 0 for a SMBus Address Space ID",
				mchi->pci_device_flag);
		}
		if (mchi->base_address.register_bit_width != 0) {
			passed = false;
			fwts_failed(fw, LOG_LEVEL_MEDIUM,
				"MCHISmbusRegBitWidthNonZero",
				"MCHI Base Address Register Bit Width is 0x%2.2" PRIx8
				" and should be zero for a SMBus Address Space ID",
				mchi->base_address.register_bit_width);
		}
		if (mchi->base_address.register_bit_offset != 0) {
			passed = false;
			fwts_failed(fw, LOG_LEVEL_MEDIUM,
				"MCHISmbusRegBitOffsetNonZero",
				"MCHI Base Address Register Bit Offset is 0x%2.2" PRIx8
				" and should be zero for a SMBus Address Space ID",
				mchi->base_address.register_bit_offset);
		}
		if (mchi->base_address.access_width != 1) {
			passed = false;
			fwts_failed(fw, LOG_LEVEL_MEDIUM,
				"MCHISmbusRegAddressSizeInvalid",
				"MCHI Base Address Register Address Size is 0x%2.2" PRIx8
				" and should be 1 (byte access) for a SMBus Address Space ID",
				mchi->base_address.access_width);
		}
		if (mchi->base_address.address & ~(0x7fULL)) {
			passed = false;
			fwts_failed(fw, LOG_LEVEL_MEDIUM,
				"MCHISmbusAddressInvalid",
				"MCHI Base Address is 0x%16.16" PRIx64
				" and should be 0x00..0x7f a SMBus Address Space ID",
				mchi->base_address.address);
		}
	}
	/* PCI Device field specific checks */
	if (mchi->pci_device_flag & 0x01) {
		if (mchi->bytes[2] & ~0x1f) {
			passed = false;
			fwts_failed(fw, LOG_LEVEL_MEDIUM,
				"MCHIPciDeviceNumberInvalid",
				"MCHI PCI Device Number is 0x%2.2" PRIx8
				" and reserved bits [7:5] should be zero",
				mchi->bytes[2]);
		}
		if (mchi->bytes[3] & ~0x47) {
			passed = false;
			fwts_failed(fw, LOG_LEVEL_MEDIUM,
				"MCHIPciFunctionNumberInvalid",
				"MCHI PCI Function Number is 0x%2.2" PRIx8
				" and reserved bits [7] and [5:3] should be zero",
				mchi->bytes[3]);
		}
	}

done:
	if (passed)
		fwts_passed(fw, "No issues found in MCHI table.");

	return FWTS_OK;
}

static fwts_framework_minor_test mchi_tests[] = {
	{ mchi_test1, "MCHI Management Controller Host Interface Table test." },
	{ NULL, NULL }
};

static fwts_framework_ops mchi_ops = {
	.description = "MCHI Management Controller Host Interface Table test.",
	.init        = mchi_init,
	.minor_tests = mchi_tests
};

FWTS_REGISTER("mchi", &mchi_ops, FWTS_TEST_ANYTIME, FWTS_FLAG_BATCH | FWTS_FLAG_TEST_ACPI)

#endif
