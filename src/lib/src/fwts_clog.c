 /*
 * Copyright (C) 2010-2018 Canonical
 * Copyright (C) 2018 9elements Cyber Security
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

/*
 *  coreboot logfile exposed by Google firmware module
 *  Kernel option nessesary (GOOGLE_MEMCONSOLE_COREBOOT=m/y)
 */
#define GOOGLE_MEMCONSOLE_COREBOOT_PATH	"/sys/firmware/log"

/*
 *  clog pattern matching strings data file, data stored in json format
 */
#define CLOG_DATA_JSON_FILE     "clog.json"

/*
 *  match unique strings in the coreboot log
*/
#define UNIQUE_CLOG_LABEL       "Clog"

/*
 *  free coreboot log list
 */
void fwts_clog_free(fwts_list *clog)
{
        fwts_log_free(clog);
}

/*
 *  read coreboot log and return as list of lines
 *  TODO:	1) parse coreboot logfile as argument
 *  		2) find coreboot log in /dev/mem
 */
fwts_list *fwts_clog_read(void)
{
    fwts_list *list;

    if ((list = fwts_file_open_and_read(GOOGLE_MEMCONSOLE_COREBOOT_PATH)) == NULL)
        return NULL;

    return list;
}

int fwts_clog_scan(fwts_framework *fw,
        fwts_list *clog,
        fwts_clog_scan_func scan_func,
        fwts_clog_progress_func progress_func,
        void *private,
        int *match)
{
        return fwts_log_scan(fw, clog, scan_func, progress_func, private, match, false);
}

void fwts_clog_scan_patterns(fwts_framework *fw,
        char *line,
        int  repeated,
        char *prevline,
        void *private,
        int *errors)
{
    const char *advice =
        "This is a bug picked up by coreboot, but as yet, the "
        "firmware test suite has no diagnostic advice for this particular problem.";
    fwts_log_scan_patterns(fw, line, repeated, prevline, private, errors, "coreboot", advice);
}

static int fwts_clog_check(fwts_framework *fw,
        const char *table,
        fwts_clog_progress_func progress,
        fwts_list *clog,
        int *errors)
{
        char json_data_path[PATH_MAX];

        snprintf(json_data_path, sizeof(json_data_path), "%s/%s", fw->json_data_path, CLOG_DATA_JSON_FILE);

        return fwts_log_check(fw, table, fwts_clog_scan_patterns, progress, clog, errors, json_data_path, UNIQUE_CLOG_LABEL, true);
}

int fwts_clog_firmware_check(fwts_framework *fw, fwts_clog_progress_func progress,
        fwts_list *clog, int *errors)
{
        return fwts_clog_check(fw, "firmware_error_warning_patterns",
                progress, clog, errors);
}
