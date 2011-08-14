/*
 * Copyright (C) 2006, Intel Corporation
 * Copyright (C) 2010-2011 Canonical
 *
 * This code was originally part of the Linux-ready Firmware Developer Kit
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

#ifdef FWTS_ARCH_INTEL

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <limits.h>

typedef struct {
	fwts_log_level level;
	const char *label;
	const char *pat1;
	const char *pat2;
	const char *message;
} dmi_pattern;

static const char *dmi_types[] = {
	"BIOS",
	"System",
	"Base Board",
	"Chassis",
	"Processor",
	"Memory Controller",
	"Memory Module",
	"Cache",
	"Port Connector",
	"System Slots",
	"On Board Devices",
	"OEM Strings",
	"System Configuration Options",
	"BIOS Language",
	"Group Associations",
	"System Event Log",
	"Physical Memory Array",
	"Memory Device",
	"32-bit Memory Error",
	"Memory Array Mapped Address",
	"Memory Device Mapped Address",
	"Built-in Pointing Device",
	"Portable Battery",
	"System Reset",
	"Hardware Security",
	"System Power Controls",
	"Voltage Probe",
	"Cooling Device",
	"Temperature Probe",
	"Electrical Current Probe",
	"Out-of-band Remote Access",
	"Boot Integrity Services",
	"System Boot",
	"64-bit Memory Error",
	"Management Device",
	"Management Device Component",
	"Management Device Threshold Data",
	"Memory Channel",
	"IPMI Device",
	"Power Supply"
};

static const dmi_pattern dmi_patterns[] = {
	{ 
		LOG_LEVEL_HIGH,
		"NoSMBIOSorDMIentry",	
		"No SMBIOS nor DMI entry point found",
		NULL,
		"Check SMBIOS or DMI entry points" 
	},
	{ 
		LOG_LEVEL_HIGH,
		"DMIBadStructCount",
		"Wrong DMI structures count",
		NULL,
		"DMI structures count"
	},
	{
		LOG_LEVEL_HIGH,
		"DMIBadStructLength",
		"Wrong DMI structures length",
		NULL,
		"DMI structures length"
	},
	{
		LOG_LEVEL_MEDIUM,
		"DMIOutOfSpec",
		"<OUT OF SPEC>",
		NULL,
		"Out of spec check"
	},
	{
		LOG_LEVEL_MEDIUM,
		"DMIBadIndex",
		"<BAD INDEX>",
		NULL,
		"Bad index check"
	},
	{
		LOG_LEVEL_HIGH,
		"DMIChecksum",
		"Bad checksum! Please report.",
		NULL,
		"Bad checksum"
	},
	{
		LOG_LEVEL_LOW,
		"DMISerialNumber",
		"Serial Number:",
		"0123456789",
		"Template Serial Number not updated"
	},
	{
		LOG_LEVEL_LOW,
		"DMIAssetTag",
		"Asset Tag",
		"1234567890",
		"Template Serial Number not updated"
	},
	{
		LOG_LEVEL_LOW,
		"DMIUUID",
		"UUID:",
		"0A0A0A0A-0A0A-0A0A-0A0A-0A0A0A0A0A0A.",
		"UUID number not updated"
	},
	{
		LOG_LEVEL_LOW,
		"DMIBadDefault",
		"To Be Filled By O.E.M.",
		NULL,
		"Value not updated"
	},
	{ 	0,
		NULL,
		NULL,
		NULL
	}
};

static int dmi_decode_init(fwts_framework *fw)
{
	if (fwts_check_executable(fw, fw->dmidecode, "dmidecode"))
		return FWTS_ERROR;

	return FWTS_OK;
}

static int dmi_decode_test1(fwts_framework *fw)
{
	fwts_list *dmi_text;
	fwts_list_link *item;
	int type;

	for (type=0; type < 40; type++) {
		int dumped = 0;
		char buffer[PATH_MAX];

		snprintf(buffer, sizeof(buffer), "%s -t %d",
			fw->dmidecode, type);

		if (fwts_pipe_exec(buffer, &dmi_text)) {
			fwts_log_error(fw, "Failed to execute dmidecode.");
			continue;
		}
		if (dmi_text == NULL) {
			fwts_log_error(fw, "Failed to read output from dmidecode (out of memory).");
			continue;
		}	

		fwts_list_foreach(item, dmi_text) {
			int i;

			for (i=0; dmi_patterns[i].pat1 != NULL; i++) {
				int match;
				char *text = fwts_text_list_text(item);
				if (dmi_patterns[i].pat2 == NULL)
					match = (strstr(text, dmi_patterns[i].pat1) != NULL);
				else {
					match = (strstr(text, dmi_patterns[i].pat1) != NULL) &&
						(strstr(text, dmi_patterns[i].pat2) != NULL);
				}
				if (match) {		
					fwts_failed(fw,
						dmi_patterns[i].level,
						dmi_patterns[i].label,
						"DMI type %s: %s.",
						dmi_types[type],
						dmi_patterns[i].message);
					fwts_tag_failed(fw, FWTS_TAG_BIOS_DMI);
					if (!dumped) {
						fwts_log_info(fw, "DMI table dump:");
						fwts_list_link *dump;
						fwts_list_foreach(dump, dmi_text)
							fwts_log_info_verbatum(fw,
								"%s", fwts_text_list_text(dump));			
						dumped = 1;
					}
				}
			}
		}
		if (!dumped)
			fwts_passed(fw, "DMI type %s.", dmi_types[type]);
		
		fwts_text_list_free(dmi_text);
	}
	return FWTS_OK;
}

static fwts_framework_minor_test dmi_decode_tests[] = {
	{ dmi_decode_test1, "Test DMI/SMBIOS tables for errors." },
	{ NULL, NULL }
};

static fwts_framework_ops dmi_decode_ops = {
	.description = "Test DMI/SMBIOS tables for errors.",
	.init        = dmi_decode_init,
	.minor_tests = dmi_decode_tests
};

FWTS_REGISTER(dmi_decode, &dmi_decode_ops, FWTS_TEST_ANYTIME, FWTS_BATCH | FWTS_ROOT_PRIV);

#endif
