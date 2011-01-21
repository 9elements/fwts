/*
 * Copyright (C) 2010-2011 Canonical
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

#ifndef __FWTS_FRAMEWORK_H__
#define __FWTS_FRAMEWORK_H__

#include <stdio.h>
#include <string.h>
#include <stdbool.h>

#include "fwts_log.h"
#include "fwts_list.h"
#include "fwts_framework.h"

#define FWTS_FRAMEWORK_MAGIC	0x2af61aec

typedef enum {
	FWTS_FRAMEWORK_FLAGS_DEFAULT	               = 0x00000000,
	FWTS_FRAMEWORK_FLAGS_STDOUT_SUMMARY            = 0x00000001,
	FWTS_FRAMEWORK_FLAGS_SHOW_PROGRESS             = 0x00000002,
	FWTS_FRAMEWORK_FLAGS_FORCE_CLEAN               = 0x00000004,
	FWTS_FRAMEWORK_FLAGS_SHOW_TESTS	               = 0x00000008,
	FWTS_FRAMEWORK_FLAGS_SHOW_PROGRESS_DIALOG      = 0x00000010,
	FWTS_FRAMEWORK_FLAGS_BATCH	               = 0x00001000,
	FWTS_FRAMEWORK_FLAGS_INTERACTIVE               = 0x00002000,
	FWTS_FRAMEWORK_FLAGS_BATCH_EXPERIMENTAL        = 0x00004000,
	FWTS_FRAMEWORK_FLAGS_INTERACTIVE_EXPERIMENTAL  = 0x00008000,
	FWTS_FRAMEWORK_FLAGS_POWER_STATES              = 0x00010000,
	FWTS_FRAMEWORK_FLAGS_TEST_BIOS		       = 0x01000000,
	FWTS_FRAMEWORK_FLAGS_TEST_UEFI		       = 0x02000000,
	FWTS_FRAMEWORK_FLAGS_TEST_ACPI		       = 0x04000000,
	FWTS_FRAMEWORK_FLAGS_UTILS     	       	       = 0x08000000,
	FWTS_FRAMEWORK_FLAGS_QUIET		       = 0x10000000,
	FWTS_FRAMEWORK_FLAGS_LP_TAGS                   = 0x20000000,
	FWTS_FRAMEWORK_FLAGS_LP_TAGS_LOG               = 0x40000000,
	FWTS_FRAMEWORK_FLAGS_SHOW_TESTS_FULL           = 0x80000000,
} fwts_framework_flags;

#define FWTS_FRAMEWORK_FLAGS_TEST_MASK		\
	(FWTS_FRAMEWORK_FLAGS_TEST_BIOS |	\
	 FWTS_FRAMEWORK_FLAGS_TEST_UEFI |	\
	 FWTS_FRAMEWORK_FLAGS_TEST_ACPI)

/*
 *  Test results
 */
typedef struct {
	uint32_t passed;
	uint32_t failed;
	uint32_t aborted;
	uint32_t warning;
	uint32_t skipped;
} fwts_results;

static inline void fwts_results_zero(fwts_results *results)
{
	memset(results, 0, sizeof(fwts_results));
}


static inline void fwts_framework_summate_results(fwts_results *total, fwts_results *increment)
{
	total->aborted += increment->aborted;
	total->failed  += increment->failed;
	total->passed  += increment->passed;
	total->warning += increment->warning;
	total->skipped += increment->skipped;
}

/*
 *  Test framework context
 */
typedef struct {
	int magic;				/* identify struct magic */
	fwts_log *results;			/* log for test results */
	char *results_logname;			/* filename of results log */

	char *dmidecode;			/* path to dmidecode */
	char *lspci;				/* path to lspci */

	char *acpi_table_path;			/* path to raw ACPI tables */
	char *acpi_table_acpidump_file;		/* path to ACPI dump file */
	char *klog;				/* path to dump of kernel log */
	char *json_data_path;			/* path to application json data files, e.g. json klog data */
	int  s3_multiple;			/* number of s3 multiple tests to run */
	int  s3_min_delay;			/* minimum time between resume and next suspend */
	int  s3_max_delay;			/* maximum time between resume and next suspend */
	float s3_delay_delta;			/* amount to add to delay between each S3 tests */
	int  s4_multiple;			/* number of s4 multiple tests to run */
	int  s4_sleep_delay;			/* number of seconds to sleep before waking up */
	int  s4_min_delay;			/* minimum time between resume and next hibernate */
	int  s4_max_delay;			/* maximum time between resume and next hibernate */
	float s4_delay_delta;			/* amount to add to delay between each S4 tests */

	fwts_framework_flags flags;

	int current_minor_test_num;		/* Nth minor test being run in a test module */
	const char *current_minor_test_name;	/* Name of current minor test being run */
	int current_major_test_num;		/* Nth major test being currently run */
	int major_tests_total;			/* Total number of major tests */

	struct fwts_framework_test *current_major_test; /* current test */

	fwts_results	minor_tests;		/* results for each minor test */
	fwts_results	total;			/* totals over all tests */

	uint32_t	total_run;		/* total number of major tests run */

	int minor_test_progress;		/* Percentage completion of current test */
	int print_summary;			/* Print summary of results at end of test runs */
	int failed_level;			/* Bit mask of failed levels in test run */

	fwts_list *test_taglist;		/* List of tags found when running all minor tests */
	fwts_list *total_taglist;		/* List of tags found when running all tests */

	int firmware_type;			/* Type of firmware */
	int show_progress;			/* Show progress while running current test */
} fwts_framework;

typedef int (*fwts_framework_minor_test_func)(fwts_framework *framework);

typedef struct {
	fwts_framework_minor_test_func test_func;/* Minor test to run */
	const char  *name;			/* Name of minor test */
} fwts_framework_minor_test;

typedef struct fwts_framework_ops {
	char *(*headline)(void);		/* Headline description of test */
	int (*init)(fwts_framework *);		/* Initialise */
	int (*deinit)(fwts_framework *);	/* De-init */		
	fwts_framework_minor_test *minor_tests;	/* NULL terminated array of minor tests to run */
	int total_tests;			/* Number of tests to run */
} fwts_framework_ops;

typedef struct fwts_framework_test {
	const char *name;
	fwts_framework_ops *ops;
	int         priority;
	int         flags;
	fwts_results results;			/* Per test results */
	bool	    was_run;
} fwts_framework_test;

int  fwts_framework_args(const int argc, char * const *argv);
void fwts_framework_test_add(const char *name, fwts_framework_ops *ops, const int priority, const int flags);
int  fwts_framework_compare_test_name(void *, void *);

void fwts_framework_passed(fwts_framework *, const char *fmt, ...)
	__attribute__((format(printf, 2, 3)));
void fwts_framework_failed(fwts_framework *, fwts_log_level level, const char *fmt, ...)
	__attribute__((format(printf, 3, 4)));
void fwts_framework_warning(fwts_framework *, const char *fmt, ...)
	__attribute__((format(printf, 2, 3)));
void fwts_framework_advice(fwts_framework *, const char *fmt, ...)
	__attribute__((format(printf, 2, 3)));
void fwts_framework_skipped(fwts_framework *, const char *fmt, ...)
	__attribute__((format(printf, 2, 3)));
void fwts_framework_aborted(fwts_framework *, const char *fmt, ...)
	__attribute__((format(printf, 2, 3)));
void fwts_framework_minor_test_progress(fwts_framework *fw, const int percent);

#define fwts_progress(fw, percent)	fwts_framework_minor_test_progress(fw, percent)

#define fwts_passed(fw, args...)	fwts_framework_passed(fw, ## args)
#define fwts_failed(fw, args...)	fwts_framework_failed(fw, LOG_LEVEL_MEDIUM, ## args)
#define fwts_failed_level(fw, level, args...) \
					fwts_framework_failed(fw, level, ## args)
#define fwts_failed_critical(fw, args...)	\
					fwts_framework_failed(fw, LOG_LEVEL_CRITICAL, ## args)
#define fwts_failed_high(fw, args...)	\
					fwts_framework_failed(fw, LOG_LEVEL_HIGH, ## args)
#define fwts_failed_medium(fw, args...)	\
					fwts_framework_failed(fw, LOG_LEVEL_MEDIUM, ## args)
#define fwts_failed_low(fw, args...)	\
					fwts_framework_failed(fw, LOG_LEVEL_LOW, ## args)

#define fwts_warning(fw, args...)	fwts_framework_warning(fw, ## args)

#define fwts_advice(fw, args...)	fwts_framework_advice(fw, ## args)

#define fwts_skipped(fw, args...)	fwts_framework_skipped(fw, ## args)

#define fwts_aborted(fw, args...)	fwts_framework_aborted(fw, ## args)

static inline int fwts_tests_passed(const fwts_framework *fw)
{
	return ((fw->minor_tests.failed +
		 fw->minor_tests.warning +
		 fw->minor_tests.aborted) == 0);
}

/*
 *  Where to schedule a test, priority sorted lowest first, highest last
 */
#define FWTS_TEST_FIRST		0		
#define FWTS_TEST_EARLY		10
#define FWTS_TEST_ANYTIME	50
#define FWTS_TEST_LATE		75
#define FWTS_TEST_LAST		100

/*
 *  Batch (run w/o interaction) or interactive (requires user interaction) flags
 */
#define FWTS_BATCH 			FWTS_FRAMEWORK_FLAGS_BATCH
#define FWTS_INTERACTIVE 		FWTS_FRAMEWORK_FLAGS_INTERACTIVE
#define FWTS_BATCH_EXPERIMENTAL		FWTS_FRAMEWORK_FLAGS_BATCH_EXPERIMENTAL
#define FWTS_INTERACTIVE_EXPERIMENTAL	FWTS_FRAMEWORK_FLAGS_INTERACTIVE_EXPERIMENTAL
#define FWTS_POWER_STATES		FWTS_FRAMEWORK_FLAGS_POWER_STATES
#define FWTS_UTILS			FWTS_FRAMEWORK_FLAGS_UTILS

#define FWTS_TEST_BIOS			FWTS_FRAMEWORK_FLAGS_TEST_BIOS
#define FWTS_TEST_UEFI			FWTS_FRAMEWORK_FLAGS_TEST_UEFI
#define FWTS_TEST_ACPI			FWTS_FRAMEWORK_FLAGS_TEST_ACPI

#define FWTS_TEST_INTERACTIVE(flags)	\
	(flags & (FWTS_FRAMEWORK_FLAGS_INTERACTIVE | \
		  FWTS_FRAMEWORK_FLAGS_INTERACTIVE_EXPERIMENTAL))

#define FWTS_REGISTER(name, ops, priority, flags)		\
								\
void name ## init (void) __attribute__ ((constructor));		\
								\
void name ## init (void)					\
{								\
	fwts_framework_test_add(# name, ops, priority, flags);	\
}								\
							
#endif
