/*
 * Copyright (C) 2016 Canonical
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
#include <ctype.h>

static const uint8_t guid_virtual_device[4][16] = {
	// Virtual Disk Region - Volatile
	{ 0x5a, 0x53, 0xab, 0x77, 0xfc, 0x45, 0x4b, 0x62, 0x55, 0x60, 0xf7, 0xb2, 0x81, 0xd1, 0xf9, 0x6e },
	// Virtual CD Region - Volatile
	{ 0x30, 0xbd, 0x5a, 0x3d, 0x75, 0x41, 0xce, 0x87, 0x6d, 0x64, 0xd2, 0xad, 0xe5, 0x23, 0xc4, 0xbb },
	// Virtual Disk Region - Persistent
	{ 0xc9, 0x02, 0xea, 0x5c, 0x07, 0x4d, 0xd3, 0x69, 0x26, 0x9f, 0x44, 0x96, 0xfb, 0xe0, 0x96, 0xf9 },
	// Virtual CD Region - Persistent
	{ 0x88, 0x81, 0x01, 0x08, 0xcd, 0x42, 0x48, 0xbb, 0x10, 0x0f, 0x53, 0x87, 0xd5, 0x3d, 0xed, 0x3d },
};

static fwts_acpi_table_info *table;

static int nfit_init(fwts_framework *fw)
{
	if (fwts_acpi_find_table(fw, "NFIT", 0, &table) != FWTS_OK) {
		fwts_log_error(fw, "Cannot read ACPI tables.");
		return FWTS_ERROR;
	}
	if (table == NULL || (table && table->length == 0)) {
		fwts_log_error(fw, "ACPI NFIT table does not exist, skipping test");
		return FWTS_SKIP;
	}
	return FWTS_OK;
}

/*
 *  NFIT NVDIMM Firmware Interface Table
 */
static int nfit_test1(fwts_framework *fw)
{
	fwts_acpi_table_nfit *nfit = (fwts_acpi_table_nfit*) table->data;
	fwts_acpi_table_nfit_struct_header *entry;
	uint32_t offset;
	bool passed = true;

	fwts_log_info_verbatim(fw, "NFIT NVDIMM Firmware Interface Table:");
	fwts_log_info_verbatim(fw, "  Reserved:                 0x%8.8" PRIx32, nfit->reserved);
	fwts_log_nl(fw);

	if (nfit->reserved != 0) {
		passed = false;
		fwts_failed(fw, LOG_LEVEL_LOW,
			"NFITReservedNonZero",
			"NFIT reserved field must be zero, got "
			"0x%8.8" PRIx32 " instead", nfit->reserved);
	}

	offset = sizeof(fwts_acpi_table_nfit);
	entry = (fwts_acpi_table_nfit_struct_header *) (table->data + offset);

	while (offset < table->length) {
		uint64_t reserved_passed = 0;

		fwts_log_info_verbatim(fw, "  NFIT Subtable:");
		fwts_log_info_verbatim(fw, "    Type:                                   0x%4.4" PRIx16, entry->type);
		fwts_log_info_verbatim(fw, "    Length:                                 0x%4.4" PRIx16, entry->length);

		if (entry->length == 0) {
			passed = false;
			fwts_failed(fw, LOG_LEVEL_HIGH, "NFITLengthZero",
				    "NFIT Subtable (offset 0x%4.4" PRIx32 ") "
				    "length cannot be 0", offset);
			break;
		}

		if (entry->type == FWTS_ACPI_NFIT_TYPE_SYSTEM_ADDRESS) {
			fwts_acpi_table_nfit_system_memory *nfit_struct = (fwts_acpi_table_nfit_system_memory *) entry;
			char guid_str[37];
			bool guid_skip = false;
			size_t i;

			fwts_guid_buf_to_str(nfit_struct->range_guid, guid_str, sizeof(guid_str));

			fwts_log_info_verbatim(fw, "    SPA Range Structure Index:              0x%4.4" PRIx16, nfit_struct->range_index);
			fwts_log_info_verbatim(fw, "    Flags:                                  0x%4.4" PRIx16, nfit_struct->flags);
			fwts_log_info_verbatim(fw, "    Reserved:                               0x%8.8" PRIx32, nfit_struct->reserved);
			fwts_log_info_verbatim(fw, "    Proximity Domain:                       0x%8.8" PRIx32, nfit_struct->proximity_domain);
			fwts_log_info_verbatim(fw, "    Address Range Type GUID:                %s", guid_str);
			fwts_log_info_verbatim(fw, "    System Physical Address Range Base:     0x%16.16" PRIx64, nfit_struct->address);
			fwts_log_info_verbatim(fw, "    System Physical Address Range Length:   0x%16.16" PRIx64, nfit_struct->length);
			fwts_log_info_verbatim(fw, "    Address Range Memory Mapping Attribute: 0x%16.16" PRIx64, nfit_struct->memory_mapping);

			/* SPA Range Structure Index can be 0 for Virtual CD Region and
			   Virtual Disk Region (both volatile and persistent) */
			for (i = 0; i < 4; i++) {
				if (fwts_guid_match(nfit_struct->range_guid, guid_virtual_device[i], 16)) {
					guid_skip = true;
					break;
				}
			}

			if (guid_skip == false && nfit_struct->range_index == 0) {
				passed = false;
				fwts_failed(fw, LOG_LEVEL_HIGH,
					"NFITBadRangeIndexZero",
					"NFIT SPA Range Structure Index must not be zero");
			}

			if (guid_skip) {
				if (nfit_struct->range_index != 0) {
					passed = false;
					fwts_failed(fw, LOG_LEVEL_HIGH,
						"NFITBadRangeIndexNonZero",
						"NFIT SPA Range Structure Index must "
						"be zero when region is Virtual CD or "
						"Virtual Disk, got 0x%4.4" PRIx32 " instead",
						nfit_struct->range_index);
				}

				if (nfit_struct->flags != 0) {
					passed = false;
					fwts_failed(fw, LOG_LEVEL_HIGH,
						"NFITBadFlagsNonZero",
						"NFIT Flags must be zero when "
						"region is Virtual CD or Virtual Disk, got "
						"0x%4.4" PRIx32 " instead",
						nfit_struct->flags);
				}

				if (nfit_struct->proximity_domain != 0) {
					passed = false;
					fwts_failed(fw, LOG_LEVEL_HIGH,
						"NFITBadProximityDomainNonZero",
						"NFIT Proximity Domain must be zero when "
						"region is Virtual CD or Virtual Disk, got "
						"0x%8.8" PRIx32 " instead",
						nfit_struct->proximity_domain);
				}

				if (nfit_struct->memory_mapping != 0) {
					passed = false;
					fwts_failed(fw, LOG_LEVEL_HIGH,
						"NFITBadMemoryAttributeNonZero",
						"NFIT Address Range Memory Mapping Attribute "
						"must be zero when region is Virtual CD or "
						"Virtual Disk, got 0x%16.16" PRIx64 " instead",
						nfit_struct->memory_mapping);
				}
			}

			if (nfit_struct->flags & ~0x03) {
				passed = false;
				fwts_failed(fw, LOG_LEVEL_HIGH,
					"NFITBadFlags",
					"NFIT Flags's Bits[15..2] must be zero, got "
					"0x%8.8" PRIx32 " instead", nfit_struct->flags);
			}

			if (nfit_struct->reserved != 0)
				reserved_passed = nfit_struct->reserved;

			/* TODO check Proximity Domain with SRAT table */

			if (nfit_struct->memory_mapping & ~0x01F01F) {
				passed = false;
				fwts_failed(fw, LOG_LEVEL_HIGH,
					"NFITBadMemoryMappingAttribute",
					"NFIT Memory Mapping Attribute must meet UEFI Spec, got "
					"0x%16.16" PRIx64 " instead", nfit_struct->memory_mapping);
			}

		} else if (entry->type == FWTS_ACPI_NFIT_TYPE_MEMORY_MAP) {
			fwts_acpi_table_nfit_memory_map *nfit_struct = (fwts_acpi_table_nfit_memory_map *) entry;

			fwts_log_info_verbatim(fw, "    NFIT Device Handle:                     0x%8.8" PRIx32, nfit_struct->device_handle);
			fwts_log_info_verbatim(fw, "    NVDIMM Physical ID:                     0x%4.4" PRIx16, nfit_struct->physical_id);
			fwts_log_info_verbatim(fw, "    NVDIMM Region ID:                       0x%4.4" PRIx16, nfit_struct->region_id);
			fwts_log_info_verbatim(fw, "    SPA Range Structure Index:              0x%4.4" PRIx16, nfit_struct->range_index);
			fwts_log_info_verbatim(fw, "    NVDIMM Control Region Structure Index:  0x%4.4" PRIx16, nfit_struct->region_index);
			fwts_log_info_verbatim(fw, "    NVDIMM Region Size:                     0x%16.16" PRIx64, nfit_struct->region_size);
			fwts_log_info_verbatim(fw, "    Region Offset:                          0x%16.16" PRIx64, nfit_struct->region_offset);
			fwts_log_info_verbatim(fw, "    NVDIMM Physical Address Region Base:    0x%16.16" PRIx64, nfit_struct->address);
			fwts_log_info_verbatim(fw, "    Interleave Structure Index:             0x%4.4" PRIx16, nfit_struct->interleave_index);
			fwts_log_info_verbatim(fw, "    Interleave Ways:                        0x%4.4" PRIx16, nfit_struct->interleave_ways);
			fwts_log_info_verbatim(fw, "    NVDIMM State Flags:                     0x%4.4" PRIx16, nfit_struct->flags);
			fwts_log_info_verbatim(fw, "    Reserved:                               0x%4.4" PRIx16, nfit_struct->reserved);

			if (nfit_struct->flags & ~0x7F) {
				passed = false;
				fwts_failed(fw, LOG_LEVEL_HIGH,
					"NFITBadFlags",
					"NFIT Flags's Bits[15..7] must be zero, got "
					"0x%8.8" PRIx32 " instead", nfit_struct->flags);
			}

			if (nfit_struct->reserved != 0)
				reserved_passed = nfit_struct->reserved;

		} else if (entry->type == FWTS_ACPI_NFIT_TYPE_INTERLEAVE) {
			fwts_acpi_table_nfit_interleave *nfit_struct = (fwts_acpi_table_nfit_interleave *) entry;
			uint32_t i;

			fwts_log_info_verbatim(fw, "    Interleave Structure Index:             0x%4.4" PRIx16, nfit_struct->interleave_index);
			fwts_log_info_verbatim(fw, "    Reserved:                               0x%4.4" PRIx16, nfit_struct->reserved);
			fwts_log_info_verbatim(fw, "    Number of Lines Described:              0x%8.8" PRIx32, nfit_struct->line_count);
			fwts_log_info_verbatim(fw, "    Line Size:                              0x%8.8" PRIx32, nfit_struct->line_size);

			for (i = 0; i < nfit_struct->line_count; i++) {
				fwts_log_info_verbatim(fw, "    Line Offset:                            0x%8.8"  PRIx32, nfit_struct->line_offset[i]);

				if (nfit_struct->line_offset[i] % nfit_struct->line_size)
					fwts_failed(fw, LOG_LEVEL_HIGH,
						"NFITBadLineOffsetAlignment",
						"NFIT Line Offset must be aligned nfit_struct->line_size, got "
						"0x%8.8" PRIx32 " instead", nfit_struct->line_offset[i]);
			}

			if (nfit_struct->reserved != 0)
				reserved_passed = nfit_struct->reserved;

			if (nfit_struct->line_count == 0) {
				passed = false;
				fwts_failed(fw, LOG_LEVEL_HIGH,
					"NFITBadLineCount",
					"NFIT Number of Lines must not be zero");
			}

		} else if (entry->type == FWTS_ACPI_NFIT_TYPE_SMBIOS) {
			fwts_acpi_table_nfit_smbios *nfit_struct = (fwts_acpi_table_nfit_smbios *) entry;

			fwts_log_info_verbatim(fw, "    Reserved:                               0x%8.8" PRIx32, nfit_struct->reserved);

		} else if (entry->type == FWTS_ACPI_NFIT_TYPE_CONTROL_REGION) {
			fwts_acpi_table_nfit_control_range *nfit_struct = (fwts_acpi_table_nfit_control_range *) entry;
			uint64_t reserved1;

			reserved1 = (uint64_t) nfit_struct->reserved1[0] + ((uint64_t) nfit_struct->reserved1[1] << 8) +
				   ((uint64_t) nfit_struct->reserved1[2] << 16) + ((uint64_t) nfit_struct->reserved1[3] << 24) +
				   ((uint64_t) nfit_struct->reserved1[4] << 32) + ((uint64_t) nfit_struct->reserved1[5] << 40);

			if (reserved1 != 0)
				reserved_passed = reserved1;

			fwts_log_info_verbatim(fw, "    NVDIMM Control Region Structure Index:  0x%4.4" PRIx16, nfit_struct->region_index);
			fwts_log_info_verbatim(fw, "    Vendor ID:                              0x%4.4" PRIx16, nfit_struct->vendor_id);
			fwts_log_info_verbatim(fw, "    Device ID:                              0x%4.4" PRIx16, nfit_struct->device_id);
			fwts_log_info_verbatim(fw, "    Revision ID:                            0x%4.4" PRIx16, nfit_struct->revision_id);
			fwts_log_info_verbatim(fw, "    Subsystem Vendor ID:                    0x%4.4" PRIx16, nfit_struct->subsystem_vendor_id);
			fwts_log_info_verbatim(fw, "    Subsystem Device ID:                    0x%4.4" PRIx16, nfit_struct->subsystem_device_id);
			fwts_log_info_verbatim(fw, "    Subsystem Revision ID:                  0x%4.4" PRIx16, nfit_struct->subsystem_revision_id);
			fwts_log_info_verbatim(fw, "    Valid Fields:                           0x%2.2" PRIx8, nfit_struct->valid_fields);
			fwts_log_info_verbatim(fw, "    Manufacturing Location:                 0x%2.2" PRIx8, nfit_struct->manufacturing_location);
			fwts_log_info_verbatim(fw, "    Manufacturing Date:                     0x%4.4" PRIx16, nfit_struct->manufacturing_date);
			fwts_log_info_verbatim(fw, "    Reserved:                               0x%4.4" PRIx16, nfit_struct->reserved);
			fwts_log_info_verbatim(fw, "    Serial Number:                          0x%8.8" PRIx32, nfit_struct->serial_number);
			fwts_log_info_verbatim(fw, "    Region Format Interface Code:           0x%4.4" PRIx16, nfit_struct->interface_code);
			fwts_log_info_verbatim(fw, "    Number of Block Control Windows:        0x%4.4" PRIx16, nfit_struct->windows_num);
			fwts_log_info_verbatim(fw, "    Size of Block Control Window:           0x%16.16" PRIx64, nfit_struct->window_size);
			fwts_log_info_verbatim(fw, "    Command Register Offset:                0x%16.16" PRIx64, nfit_struct->command_offset);
			fwts_log_info_verbatim(fw, "    Size of Command Register:               0x%16.16" PRIx64, nfit_struct->command_size);
			fwts_log_info_verbatim(fw, "    Status RegisterOffset:                  0x%16.16" PRIx64, nfit_struct->status_offset);
			fwts_log_info_verbatim(fw, "    Size of Status Register:                0x%16.16" PRIx64, nfit_struct->status_size);
			fwts_log_info_verbatim(fw, "    NVDIMM Control Region Flag:             0x%4.4" PRIx16, nfit_struct->flags);
			fwts_log_info_verbatim(fw, "    Reserved:                               0x%16.16" PRIx64, reserved1);

			if (nfit_struct->revision_id & 0xFF00) {
				passed = false;
				fwts_failed(fw, LOG_LEVEL_HIGH,
					"NFITBadRevisionId",
					"NFIT Revision ID's BYTE 1 must be zero, got "
					"0x%4.4" PRIx16 " instead", nfit_struct->revision_id);
			}

			if (nfit_struct->subsystem_revision_id & 0xFF00) {
				passed = false;
				fwts_failed(fw, LOG_LEVEL_HIGH,
					"NFITBadRevisionId",
					"NFIT Subsystem Revision ID's BYTE 1 must be zero, got "
					"0x%4.4" PRIx16 " instead", nfit_struct->subsystem_revision_id);
			}

			if (nfit_struct->reserved != 0)
				reserved_passed = nfit_struct->reserved;

			if (nfit_struct->valid_fields & ~0x01) {
				passed = false;
				fwts_failed(fw, LOG_LEVEL_HIGH,
					"NFITBadValidField",
					"NFIT Valid Field's Bits[7..1] must be zero, got "
					"0x%2.2" PRIx8 " instead", nfit_struct->valid_fields);
			}

			if (nfit_struct->flags & ~0x01) {
				passed = false;
				fwts_failed(fw, LOG_LEVEL_HIGH,
					"NFITBadFlags",
					"NFIT Flags's Bits[15..1] must be zero, got "
					"0x%4.4" PRIx16 " instead", nfit_struct->flags);
			}

		} else if (entry->type == FWTS_ACPI_NFIT_TYPE_DATA_REGION) {
			fwts_acpi_table_nfit_data_range *nfit_struct = (fwts_acpi_table_nfit_data_range *) entry;

			fwts_log_info_verbatim(fw, "    NVDIMM Control Region Structure Index:  0x%4.4" PRIx16, nfit_struct->region_index);
			fwts_log_info_verbatim(fw, "    Number of Block Data Windows:           0x%4.4" PRIx16, nfit_struct->window_num);
			fwts_log_info_verbatim(fw, "    Block Data Window Start Offset:         0x%16.16" PRIx64, nfit_struct->window_offset);
			fwts_log_info_verbatim(fw, "    Size of Block Data Window:              0x%16.16" PRIx64, nfit_struct->window_size);
			fwts_log_info_verbatim(fw, "    NBlock Accessible Memory Capacity:      0x%16.16" PRIx64, nfit_struct->capacity);
			fwts_log_info_verbatim(fw, "    Beginning address of First Block:       0x%16.16" PRIx64, nfit_struct->start_address);

			if (nfit_struct->region_index == 0) {
				passed = false;
				fwts_failed(fw, LOG_LEVEL_HIGH,
					"NFITBadRegionIndex",
					"NFIT NVDIMM Control Region Structure Index must not be zero");
			}

		} else if (entry->type == FWTS_ACPI_NFIT_TYPE_FLUSH_ADDRESS) {
			fwts_acpi_table_nfit_flush_addr *nfit_struct = (fwts_acpi_table_nfit_flush_addr *) entry;
			uint64_t reserved;
			uint16_t i;

			reserved = (uint64_t) nfit_struct->reserved[0] + ((uint64_t) nfit_struct->reserved[1] << 8) +
				   ((uint64_t) nfit_struct->reserved[2] << 16) + ((uint64_t) nfit_struct->reserved[3] << 24) +
				   ((uint64_t) nfit_struct->reserved[4] << 32) + ((uint64_t) nfit_struct->reserved[5] << 40);

			fwts_log_info_verbatim(fw, "    NFIT Device Handle:                     0x%8.8" PRIx32, nfit_struct->device_handle);
			fwts_log_info_verbatim(fw, "    Number of Flush Hint Addresses:         0x%4.4" PRIx16, nfit_struct->hint_count);
			fwts_log_info_verbatim(fw, "    Reserved:                               0x%16.16" PRIx64, reserved);
			for (i = 0; i < nfit_struct->hint_count; i++)
				fwts_log_info_verbatim(fw, "    Flush Hint Address:                     0x%16.16" PRIx64, nfit_struct->hint_address[i]);

			if (reserved != 0)
				reserved_passed = reserved;

		} else {
			passed = false;
			fwts_failed(fw, LOG_LEVEL_HIGH,
				"NFITBadSubType",
				"NFIT Structure supports type 0..6, got "
				"0x%4.4" PRIx16 " instead", entry->type);
		}

		if (reserved_passed != 0) {
			passed = false;
			fwts_failed(fw, LOG_LEVEL_LOW,
				"NFITReservedNonZero",
				"NFIT reserved field must be zero, got "
				"0x%16.16" PRIx64 " instead", reserved_passed);
		}

		fwts_log_nl(fw);
		offset += entry->length;
		entry = (fwts_acpi_table_nfit_struct_header *) (table->data + offset);
	}


	if (passed)
		fwts_passed(fw, "No issues found in NFIT table.");

	return FWTS_OK;
}

static fwts_framework_minor_test nfit_tests[] = {
	{ nfit_test1, "NFIT NVDIMM Firmware Interface Table test." },
	{ NULL, NULL }
};

static fwts_framework_ops nfit_ops = {
	.description = "NFIT NVDIMM Firmware Interface Table test.",
	.init        = nfit_init,
	.minor_tests = nfit_tests
};

FWTS_REGISTER("nfit", &nfit_ops, FWTS_TEST_ANYTIME, FWTS_FLAG_BATCH | FWTS_FLAG_TEST_ACPI)

#endif
