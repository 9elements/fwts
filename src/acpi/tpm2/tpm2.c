/*
 * Copyright (C) 2010-2017 Canonical
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
 */
#include "fwts.h"

#if defined(FWTS_HAS_ACPI)

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <inttypes.h>
#include <stdbool.h>

static fwts_acpi_table_info *table;

static int tpm2_init(fwts_framework *fw)
{
	if (fwts_acpi_find_table(fw, "TPM2", 0, &table) != FWTS_OK) {
		fwts_log_error(fw, "Cannot load ACPI table");
		return FWTS_ERROR;
	}
	if (table == NULL) {
		fwts_log_error(fw, "ACPI TPM2 table does not exist, skipping test");
		return FWTS_SKIP;
	}

	return FWTS_OK;
}

/*
 * TPM2 table
 *   available @ https://trustedcomputinggroup.org/tcg-acpi-specification/
 */
static int tpm2_test1(fwts_framework *fw)
{
	fwts_acpi_table_tpm2 *tpm2 = (fwts_acpi_table_tpm2*) table->data;
	bool passed = true;

	fwts_log_info_verbatim(fw, "TPM2 Table:");
	fwts_log_info_verbatim(fw, "  Platform Class:                  0x%4.4"   PRIx16, tpm2->platform_class);
	fwts_log_info_verbatim(fw, "  Reserved:                        0x%4.4"   PRIx32, tpm2->reserved);
	fwts_log_info_verbatim(fw, "  Address of Control Area:         0x%16.16" PRIx64, tpm2->address_of_control_area);
	fwts_log_info_verbatim(fw, "  Start Method:                    0x%8.8"   PRIx32, tpm2->start_method);

	if (tpm2->platform_class != 0 && tpm2->platform_class != 1) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"TPM2BadPlatformClass",
			"TPM2's platform class must be zero (client) or one (server), got 0x%" PRIx16,
			tpm2->platform_class);
	}

	fwts_acpi_reserved_zero_check(fw, "TPM2", "Reserved", tpm2->reserved, sizeof(tpm2->reserved), &passed);

	if (tpm2->start_method < 1 || tpm2->start_method >= 12) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"TPM2BadStartMethod",
			"TPM2's Start Method must be between one to eleven, got 0x%" PRIx16,
			tpm2->start_method);
	}

	if (tpm2->start_method == 2 && table->length != sizeof(fwts_acpi_table_tpm2) + 4) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"TPM2BadPlatformParameters",
			"Table length must be 0x%" PRIx32 " if Start method equals 2, got 0x%" PRIx32,
			(uint32_t) sizeof(fwts_acpi_table_tpm2) + 4,
			(uint32_t) table->length);
	}

	if (tpm2->start_method == 11 && table->length < sizeof(fwts_acpi_table_tpm2) + 12) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_HIGH,
			"TPM2BadPlatformParameters",
			"Table length must be atleast 0x%" PRIx32 " if Start method equals 11, got 0x%" PRIx32,
			(uint32_t) sizeof(fwts_acpi_table_tpm2) + 12,
			(uint32_t) table->length);
	}

	if (passed)
		fwts_passed(fw, "No issues found in TPM2 table.");

	return FWTS_OK;
}

static fwts_framework_minor_test tpm2_tests[] = {
	{ tpm2_test1, "Validate TPM2 table." },
	{ NULL, NULL }
};

static fwts_framework_ops tpm2_ops = {
	.description = "TPM2 Trusted Platform Module 2 test.",
	.init        = tpm2_init,
	.minor_tests = tpm2_tests
};

FWTS_REGISTER("tpm2", &tpm2_ops, FWTS_TEST_ANYTIME, FWTS_FLAG_BATCH | FWTS_FLAG_TEST_ACPI)

#endif
