 /*
 * Copyright (C) 2010-2018 Canonical
 * Copyright (C) 2017 Google Inc.
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

fwts_list* fwts_coreboot_cbmem_log(void) {

	fwts_list *console_list;
	char *console;

	console = fwts_coreboot_cbmem_console_dump();
	console_list = fwts_list_from_text(console);
	free(console);

	return console_list;
}
