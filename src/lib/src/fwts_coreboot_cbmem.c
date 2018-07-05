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

#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <errno.h>


/*  coreboot  */
#define LB_TAG_CBMEM_ENTRY	0x0031
#define LB_TAG_SERIAL		0x000f
#define LB_TAG_CBMEM_CONSOLE	0x0017
#define LB_TAG_FORWARD		0x0011
/* ========== */

/* gooole module */
#define MIN(a,b) ((a)<(b) ? (a):(b))
#define __packed __attribute__ ((__packed__))
/* ============= */

/* cbmem coreboot */
#define ARRAY_SIZE(x) (sizeof(x) / sizeof((x)[0]))

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

/* verbose output? */
static int verbose = 0;
#define debug(x...) if(verbose) printf(x)
/* ============== */

/* ###################
 * ## COREBOOT CODE ##
 * ###################*/

/* Every entry in the boot enviroment list will correspond to a boot
 * info record.  Encoding both type and size.  The type is obviously
 * so you can tell what it is.  The size allows you to skip that
 * boot enviroment record if you don't know what it easy.  This allows
 * forward compatibility with records not yet defined.
 */
struct lb_record {
        uint32_t tag;           /* tag ID */
        uint32_t size;          /* size of record (in bytes) */
};

struct lb_uint64 {
	uint32_t lo;
	uint32_t hi;
};

struct lb_memory_range {
	struct lb_uint64 start;
	struct lb_uint64 size;
	uint32_t type;
};

/*
 * There can be more than one of these records as there is one per cbmem entry.
 */
struct lb_cbmem_entry {
        uint32_t tag;
        uint32_t size;

        uint64_t address;
        uint32_t entry_size;
        uint32_t id;
};

struct lb_header {
        uint8_t  signature[4]; /* LBIO */
        uint32_t header_bytes;
        uint32_t header_checksum;
        uint32_t table_bytes;
        uint32_t table_checksum;
        uint32_t table_entries;
};

struct lb_forward {
        uint32_t tag;
        uint32_t size;
        uint64_t forward;
};

struct lb_cbmem_ref {
        uint32_t tag;
        uint32_t size;

        uint64_t cbmem_addr;
};

/*
 * Structure describing console buffer. It is overlaid on a flat memory area,
 * with body covering the extent of the memory. Once the buffer is full,
 * output will wrap back around to the start of the buffer. The high bit of the
 * cursor field gets set to indicate that this happened. If the underlying
 * storage allows this, the buffer will persist across multiple boots and append
 * to the previous log.
 *
 * NOTE: These are known implementations accessing this console that need to be
 * updated in case of structure/API changes:
 *
 * cbmem:	[coreboot]/src/util/cbmem/cbmem.c
 * libpayload:	[coreboot]/payloads/libpayload/drivers/cbmem_console.c
 * coreinfo:	[coreboot]/payloads/coreinfo/bootlog_module.c
 * Linux:	drivers/firmware/google/memconsole-coreboot.c
 * SeaBIOS:	src/firmware/coreboot.c
 * GRUB:	grub-core/term/i386/coreboot/cbmemc.c
 */
struct cbmem_console {
	u32 size;
	u32 cursor;
	u8  body[0];
}  __packed;

/* ################
 * ## CBMEM CODE ##
 * ################*/

/* Return < 0 on error, 0 on success. */
static int parse_cbtable(u64 address, size_t table_size, uint64_t *cbmen_console_addr);

void *map_memory(unsigned long long addr, size_t size)
{
	int fd;
	void *mem;
	void *phy;
	unsigned long long page_size;
	size_t page_offset;

	fd = open("/dev/mem", O_RDONLY, 0);
	if (!fd)
		return NULL;

	page_size = getpagesize();
	page_offset = addr & (page_size - 1);
	addr &= ~(page_size - 1);

	mem = malloc(size);
	phy = mmap(NULL, (size + (page_size - 1)) & ~(page_size - 1), PROT_READ, MAP_SHARED, fd, addr );

	memcpy(mem, phy + page_offset, size);
	munmap(phy, size);
	close(fd);

	return mem;
}

static inline size_t size_to_mib(size_t sz)
{
	return sz >> 20;
}

/*
 * calculate ip checksum (16 bit quantities) on a passed in buffer. In case
 * the buffer length is odd last byte is excluded from the calculation
 */
static u16 ipchcksum(const void *addr, unsigned size)
{
	const u16 *p = addr;
	unsigned i, n = size / 2; /* don't expect odd sized blocks */
	u32 sum = 0;

	for (i = 0; i < n; i++)
		sum += p[i];

	sum = (sum >> 16) + (sum & 0xffff);
	sum += (sum >> 16);
	sum = ~sum & 0xffff;
	return (u16) sum;
}

/*
 * Try finding the timestamp table and coreboot cbmem console starting from the
 * passed in memory offset.  Could be called recursively in case a forwarding
 * entry is found.
 *
 * Returns pointer to a memory buffer containg the timestamp table or zero if
 * none found.
 */

//static struct lb_memory_range cbmem;

/* This is a work-around for a nasty problem introduced by initially having
 * pointer sized entries in the lb_cbmem_ref structures. This caused problems
 * on 64bit x86 systems because coreboot is 32bit on those systems.
 * When the problem was found, it was corrected, but there are a lot of
 * systems out there with a firmware that does not produce the right
 * lb_cbmem_ref structure. Hence we try to autocorrect this issue here.
 */
static struct lb_cbmem_ref parse_cbmem_ref(const struct lb_cbmem_ref *cbmem_ref)
{
	struct lb_cbmem_ref ret;

	ret = *cbmem_ref;

	if (cbmem_ref->size < sizeof(*cbmem_ref))
		ret.cbmem_addr = (uint32_t)ret.cbmem_addr;

	debug("      cbmem_addr = %" PRIx64 "\n", ret.cbmem_addr);

	return ret;
}

/* Return < 0 on error, 0 on success, 1 if forwarding table entry found. */
static int parse_cbtable_entries(const void *lbtable, size_t table_size, uint64_t *cbmem_console_addr)
{
	size_t i;
	const struct lb_record* lbr_p;
	int forwarding_table_found = 0;

	for (i = 0; i < table_size; i += lbr_p->size) {
		lbr_p = lbtable + i;
		debug("  coreboot table entry 0x%02x\n", lbr_p->tag);
		switch (lbr_p->tag) {
		case LB_TAG_CBMEM_CONSOLE: {
			debug("    Found cbmem console.\n");
			*cbmem_console_addr = parse_cbmem_ref((struct lb_cbmem_ref *) lbr_p).cbmem_addr;
			if (cbmem_console_addr)
				return 0;
			continue;
		}
		case LB_TAG_FORWARD: {
			int ret;
			/*
			 * This is a forwarding entry - repeat the
			 * search at the new address.
			 */
			struct lb_forward lbf_p =
				*(const struct lb_forward *) lbr_p;
			debug("    Found forwarding entry.\n");
			ret = parse_cbtable(lbf_p.forward, 0, cbmem_console_addr);

			/* Assume the forwarding entry is valid. If this fails
			 * then there's a total failure. */
			if (ret < 0)
				return -1;
			forwarding_table_found = 1;
		}
		default:
			break;
		}
	}

	return forwarding_table_found;
}

/* Return < 0 on error, 0 on success. */
static int parse_cbtable(u64 address, size_t table_size, uint64_t *cbmem_console_table)
{
	void *buf;
	size_t req_size;
	size_t i;

	req_size = table_size;
	/* Default to 4 KiB search space. */
	if (req_size == 0)
		req_size = 4 * 1024;

	debug("Looking for coreboot table at %" PRIx64 " %zd bytes.\n",
		address, req_size);

	buf = map_memory(address, req_size);

	if (!buf)
		return -1;

	/* look at every 16 bytes */
	for (i = 0; i <= req_size - sizeof(struct lb_header); i += 16) {
		int ret;
		const struct lb_header *lbh;
		void *map;

		lbh = buf + i;
		if (memcmp(lbh->signature, "LBIO", sizeof(lbh->signature)) ||
		    !lbh->header_bytes ||
		    ipchcksum(lbh, sizeof(*lbh))) {
			continue;
		}

		/* Map in the whole table to parse. */
		if (!(map = map_memory(address + i + lbh->header_bytes,
				 lbh->table_bytes))) {
			debug("Couldn't map in table\n");
			continue;
		}

		if (ipchcksum(map, lbh->table_bytes) !=
		    lbh->table_checksum) {
			debug("Signature found, but wrong checksum.\n");
			free(map);
			continue;
		}

		debug("Found!\n");

		ret = parse_cbtable_entries(map,lbh->table_bytes, cbmem_console_table);

		/* Table parsing failed. */
		if (ret < 0) {
			free(map);
			continue;
		}

		free(buf);

		/*
		 * Table parsing succeeded. If forwarding table not found update
		 * coreboot table mapping for future use.
		 */
		free(map);
		return 0;
	}

	free(buf);

	return -1;
}

/* ################
 * ## LINUX CODE ##
 * ################*/

ssize_t memory_read_from_buffer(void *to, size_t count, size_t *ppos,
				const void *from, size_t available)
{
	size_t i;
	size_t pos = *ppos;

	if (pos >= available)
		return 0;
	if (count > available - pos)
		count = available - pos;
	for (i= 0; i< count; i++) {
            if (((char *)from)[i+pos] > '\0')
            ((char *)to)[i] = ((char *)from)[i+pos];
	}
	*ppos = pos + count;

	return count;
}

/* #################
 * ## GOOGLE CODE ##
 * #################*/

#define CURSOR_MASK ((1 << 28) - 1)
#define OVERFLOW (1 << 31)

//===========================================
//===========================================
//===========================================

char *fwts_coreboot_cbmem_console_dump(void)
{
	unsigned int j;
	int mem_fd;
	uint64_t cbmem_console_addr;

	mem_fd = open("/dev/mem", O_RDONLY, 0);
	if (mem_fd < 0) {
		fprintf(stderr, "Failed to gain memory access: %s\n",
			strerror(errno));
		return NULL;
	}

	unsigned long long possible_base_addresses[] = { 0, 0xf0000 };

	/* Find and parse coreboot table */
	for (j = 0; j < ARRAY_SIZE(possible_base_addresses); j++) {
		if (!parse_cbtable(possible_base_addresses[j], 0, &cbmem_console_addr))
			break;
		if (j == ARRAY_SIZE(possible_base_addresses))
			return NULL;
	}
	struct cbmem_console *console_p;

	console_p = map_memory(cbmem_console_addr, sizeof(*console_p));

	struct cbmem_console *console = map_memory(cbmem_console_addr, console_p->size);

	char *coreboot_log = malloc(console_p->size);
	memset(coreboot_log, 0x55, console_p->size);

	size_t pos = 0;
	size_t count = console_p->size;
	u32 cursor = console->cursor & CURSOR_MASK;
	u32 flags = console->cursor & ~CURSOR_MASK;
	u32 size = console_p->size;
	struct seg {	/* describes ring buffer segments in logical order */
		u32 phys;	/* physical offset from start of mem buffer */
		u32 len;	/* length of segment */
	} seg[2] = { {0}, {0} };
	size_t done = 0;
	unsigned int i;

	if (flags & OVERFLOW) {
		if (cursor > size)	/* Shouldn't really happen, but... */
			cursor = 0;
		seg[0] = (struct seg){.phys = cursor, .len = size - cursor};
		seg[1] = (struct seg){.phys = 0, .len = cursor};
	} else {
		seg[0] = (struct seg){.phys = 0, .len = MIN(cursor, size)};
	}
	debug("cursor = %x\n", (unsigned int) cursor);
	debug("size = %x\n", (unsigned int) count);

	for (i = 0; i < ARRAY_SIZE(seg) && count > done; i++) {
		done += memory_read_from_buffer(coreboot_log + done, count - done, &pos,
			console->body + seg[i].phys, seg[i].len);
		pos -= seg[i].len;
	}

	free(console_p);
	free(console);

	return coreboot_log;
}

/* for debugging */
#ifdef __MAIN__
int main(int argc, const char *argv[])
{
	char *log;
	log = fwts_coreboot_cbmem_console_dump();
	printf("%s",log);
	free(log);
	return 0;
}
#endif
