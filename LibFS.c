#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "LibDisk.h"
#include "LibFS.h"

#include <math.h>

// set to 1 to have detailed debug print-outs and 0 to have none
#define FSDEBUG 0

#if FSDEBUG
#define dprintf printf
#else
#define dprintf noprintf
void noprintf(char* str, ...) {}
#endif

// the file system partitions the disk into five parts:

// 1. the superblock (one sector), which contains a magic number at
// its first four bytes (integer)
#define SUPERBLOCK_START_SECTOR 0

// the magic number chosen for our file system
#define OS_MAGIC 0xdeadbeef

// 2. the inode bitmap (one or more sectors), which indicates whether
// the particular entry in the inode table (#4) is currently in use
#define INODE_BITMAP_START_SECTOR 1

// the total number of bytes and sectors needed for the inode bitmap;
// we use one bit for each inode (whether it's a file or directory) to
// indicate whether the particular inode in the inode table is in use
#define INODE_BITMAP_SIZE ((MAX_FILES+7)/8)
#define INODE_BITMAP_SECTORS ((INODE_BITMAP_SIZE+SECTOR_SIZE-1)/SECTOR_SIZE)

// 3. the sector bitmap (one or more sectors), which indicates whether
// the particular sector in the disk is currently in use
#define SECTOR_BITMAP_START_SECTOR (INODE_BITMAP_START_SECTOR+INODE_BITMAP_SECTORS)

// the total number of bytes and sectors needed for the data block
// bitmap (we call it the sector bitmap); we use one bit for each
// sector of the disk to indicate whether the sector is in use or not
#define SECTOR_BITMAP_SIZE ((TOTAL_SECTORS+7)/8)
#define SECTOR_BITMAP_SECTORS ((SECTOR_BITMAP_SIZE+SECTOR_SIZE-1)/SECTOR_SIZE)

// 4. the inode table (one or more sectors), which contains the inodes
// stored consecutively
#define INODE_TABLE_START_SECTOR (SECTOR_BITMAP_START_SECTOR+SECTOR_BITMAP_SECTORS)

// an inode is used to represent each file or directory; the data
// structure supposedly contains all necessary information about the
// corresponding file or directory
typedef struct _inode {
    int size; // the size of the file or number of directory entries
    int type; // 0 means regular file; 1 means directory
    int data[MAX_SECTORS_PER_FILE]; // indices to sectors containing data blocks
} inode_t;

// the inode structures are stored consecutively and yet they don't
// straddle accross the sector boundaries; that is, there may be
// fragmentation towards the end of each sector used by the inode
// table; each entry of the inode table is an inode structure; there
// are as many entries in the table as the number of files allowed in
// the system; the inode bitmap (#2) indicates whether the entries are
// current in use or not
#define INODES_PER_SECTOR (SECTOR_SIZE/sizeof(inode_t))
#define INODE_TABLE_SECTORS ((MAX_FILES+INODES_PER_SECTOR-1)/INODES_PER_SECTOR)

// 5. the data blocks; all the rest sectors are reserved for data
// blocks for the content of files and directories
#define DATABLOCK_START_SECTOR (INODE_TABLE_START_SECTOR+INODE_TABLE_SECTORS)

// other file related definition++

// max length of a path is 256 bytes (including the ending null)
#define MAX_PATH 256

// max length of a filename is 16 bytes (including the ending null)
#define MAX_NAME 16

// max number of open files is 256
#define MAX_OPEN_FILES 256

// each directory entry represents a file/directory in the parent
// directory, and consists of a file/directory name (less than 16
// bytes) and an integer inode number
typedef struct _dirent {
    char fname[MAX_NAME]; // name of the file
    int inode; // inode of the file
} dirent_t;

// the number of directory entries that can be contained in a sector
#define DIRENTS_PER_SECTOR (SECTOR_SIZE/sizeof(dirent_t))

// global errno value here
int osErrno;

// the name of the disk backstore file (with which the file system is booted)
static char bs_filename[1024];

/* the following functions are internal helper functions */

// check magic number in the superblock; return 1 if OK, and 0 if not
static int check_magic()
{
    char buf[SECTOR_SIZE];
    if (Disk_Read(SUPERBLOCK_START_SECTOR, buf) < 0)
        return 0;
    if (*(int*)buf == OS_MAGIC) return 1;
    else return 0;
}

// initialize a bitmap with 'num' sectors starting from 'start'
// sector; all bits should be set to zero except that the first
// 'nbits' number of bits are set to one
static void bitmap_init(int start, int num, int nbits)
{
    // static map for fast lookup: the type with first i bits set
    static unsigned char BYTE10[] =
    { 0x00, 0x80, 0xc0, 0xe0, 0xf0, 0xf8, 0xfc, 0xfe, 0xff };
    unsigned char buf[SECTOR_SIZE];
    for (int i = 0; i < num; i++) {
        if (nbits > 0) {
            for (int j = 0; j < SECTOR_SIZE; j++) {
                if (nbits > 8) { buf[j] = 0xff; nbits -= 8; }
                else { buf[j] = BYTE10[nbits]; nbits = 0; }
            }
        }
        else {
            memset(buf, 0, SECTOR_SIZE);
        }
        if (Disk_Write(start + i, (char*)buf) < 0) break;
    }
}

// set the first unused bit from a bitmap of 'nbits' bits (flip the
// first zero appeared in the bitmap to one) and return its location;
// return -1 if the bitmap is already full (no more zeros)
//NBITS is the number of bytes. 
static int bitmap_first_unused(int start, int num, int nbits)
{
    // static map for fast lookup: the byte with the i-th bit set
    static unsigned char BYTE1[] =
    { 0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01 };
    unsigned char buf[SECTOR_SIZE];
    for (int i = 0; i < num; i++) {
        if (Disk_Read(start + i, (char*)buf) < 0) return -1;
        for (int j = 0; j < SECTOR_SIZE; j++) {
            if (j >= nbits) break;
            if (buf[j] < 0xff) {
                int k = 0;
                while (k < 8) {
                    if ((BYTE1[k] & buf[j]) == '\0') {
                        buf[j] |= BYTE1[k];
                        break;
                    }
                    else k++;
                }
                if (Disk_Write(start + i, (char*)buf) < 0) return -1;
                else return i * SECTOR_SIZE * 8 + j * 8 + k;
            }
        }
        nbits -= SECTOR_SIZE;
    }
    return -1;
}

// reset the i-th bit of a bitmap with 'num' sectors starting from
// 'start' sector; return 0 if successful, -1 otherwise
static int bitmap_reset(int start, int num, int ibit)
{
    // static map for fast lookup: the byte with the i-th bit reset
    static unsigned char BYTE0[] =
    { 0x7f, 0xbf, 0xdf, 0xef, 0xf7, 0xfb, 0xfd, 0xfe };

    // load the disk sector containing the bit
    int ibyte = ibit / 8; // the byte containing the bit
    int i = ibyte / SECTOR_SIZE; // the sector containing the byte
    assert(0 <= i && i < num);
    unsigned char buf[SECTOR_SIZE];
    if (Disk_Read(start + i, (char*)buf) < 0) return -1;

    // reset the byte and write to disk
    buf[ibyte % SECTOR_SIZE] &= BYTE0[ibit % 8];
    if (Disk_Write(start + i, (char*)buf) < 0) return -1;
    return 0;
}

// return 1 if the file name is illegal; otherwise, return 0; legal
// characters for a file name include letters (case sensitive),
// numbers, dots, dashes, and underscores; and a legal file name
// should not be more than MAX_NAME-1 in length
static int illegal_filename(char* name)
{
    int name_size = strlen(name);
    if (name_size > (MAX_NAME - 1))
    {
        return 1;
    }
    int i;
    for (i = 0; i < name_size; i++)//check each character in name
    {
        int ch = (int)name[i];
        //  not upper case letters   not lower case letters       not numbers
        if ((ch < 65 && ch > 90) && (ch < 97 && ch > 122) && (ch < 48 && ch > 57)
            && (ch != 45) && (ch != 46) && (ch != 95))
        //     not a dash,     dot and     underscore
        {
            return 1;//then is illegal
        }
    }
    return 0;
}

// return the child inode of the given file name 'fname' from the
// parent inode; the parent inode is currently stored in the segment
// of inode table in the cache (we cache only one disk sector for
// this); once found, both cached_inode_sector and cached_inode_buffer
// may be updated to point to the segment of inode table containing
// the child inode; the function returns -1 if no such file is found;
// it returns -2 is something else is wrong (such as parent is not
// directory, or there's read error, etc.)
static int find_child_inode(int parent_inode, char* fname,
    int* cached_inode_sector, char* cached_inode_buffer)
{
    int cached_start_entry = ((*cached_inode_sector) - INODE_TABLE_START_SECTOR) * INODES_PER_SECTOR;
    int offset = parent_inode - cached_start_entry;
    assert(0 <= offset && offset < INODES_PER_SECTOR);
    inode_t* parent = (inode_t*)(cached_inode_buffer + offset * sizeof(inode_t));
    dprintf("... load parent inode: %d (size=%d, type=%d)\n",
        parent_inode, parent->size, parent->type);
    if (parent->type != 1) {
        dprintf("... parent not a directory\n");
        return -2;
    }

    int nentries = parent->size; // remaining number of directory entries 
    int idx = 0;
    while (nentries > 0) {
        char buf[SECTOR_SIZE]; // cached content of directory entries
        if (Disk_Read(parent->data[idx], buf) < 0) return -2;
        for (int i = 0; i < DIRENTS_PER_SECTOR; i++) {
            if (i > nentries) break;
            if (!strcmp(((dirent_t*)buf)[i].fname, fname)) {
                // found the file/directory; update inode cache
                int child_inode = ((dirent_t*)buf)[i].inode;
                dprintf("... found child_inode=%d\n", child_inode);
                int sector = INODE_TABLE_START_SECTOR + child_inode / INODES_PER_SECTOR;
                if (sector != (*cached_inode_sector)) {
                    *cached_inode_sector = sector;
                    if (Disk_Read(sector, cached_inode_buffer) < 0) return -2;
                    dprintf("... load inode table for child\n");
                }
                return child_inode;
            }
        }
        idx++; nentries -= DIRENTS_PER_SECTOR;
    }
    dprintf("... could not find child inode\n");
    return -1; // not found
}

// follow the absolute path; if successful, return the inode of the
// parent directory immediately before the last file/directory in the
// path; for example, for '/a/b/c/d.txt', the parent is '/a/b/c' and
// the child is 'd.txt'; the child's inode is returned through the
// parameter 'last_inode' and its file name is returned through the
// parameter 'last_fname' (both are references); it's possible that
// the last file/directory is not in its parent directory, in which
// case, 'last_inode' points to -1; if the function returns -1, it
// means that we cannot follow the path
static int follow_path(char* path, int* last_inode, char* last_fname)
{
    if (!path) {
        dprintf("... invalid path\n");
        return -1;
    }
    if (path[0] != '/') {
        dprintf("... '%s' not absolute path\n", path);
        return -1;
    }

    // make a copy of the path (skip leading '/'); this is necessary
    // since the path is going to be modified by strsep()
    char pathstore[MAX_PATH];
    strncpy(pathstore, path + 1, MAX_PATH - 1);
    pathstore[MAX_PATH - 1] = '\0'; // for safety
    char* lpath = pathstore;

    int parent_inode = -1, child_inode = 0; // start from root
    // cache the disk sector containing the root inode
    int cached_sector = INODE_TABLE_START_SECTOR;
    char cached_buffer[SECTOR_SIZE];
    if (Disk_Read(cached_sector, cached_buffer) < 0) return -1;
    dprintf("... load inode table for root from disk sector %d\n", cached_sector);

    // for each file/directory name separated by '/'
    char* token;
    while ((token = strsep(&lpath, "/")) != NULL) {
        dprintf("... process token: '%s'\n", token);
        if (*token == '\0') continue; // multiple '/' ignored
        if (illegal_filename(token)) {
            dprintf("... illegal file name: '%s'\n", token);
            return -1;
        }
        if (child_inode < 0) {
            // regardless whether child_inode was not found previously, or
            // there was issues related to the parent (say, not a
            // directory), or there was a read error, we abort
            dprintf("... parent inode can't be established\n");
            return -1;
        }
        parent_inode = child_inode;
        child_inode = find_child_inode(parent_inode, token,
            &cached_sector, cached_buffer);
        if (last_fname) strcpy(last_fname, token);
    }
    if (child_inode < -1) return -1; // if there was error, abort
    else {
        // there was no error, several possibilities:
        // 1) '/': parent = -1, child = 0
        // 2) '/valid-dirs.../last-valid-dir/not-found': parent=last-valid-dir, child=-1
        // 3) '/valid-dirs.../last-valid-dir/found: parent=last-valid-dir, child=found
        // in the first case, we set parent=child=0 as special case
        if (parent_inode == -1 && child_inode == 0) parent_inode = 0;
        dprintf("... found parent_inode=%d, child_inode=%d\n", parent_inode, child_inode);
        *last_inode = child_inode;
        return parent_inode;
    }
}

// add a new file or directory (determined by 'type') of given name
// 'file' under parent directory represented by 'parent_inode'
int add_inode(int type, int parent_inode, char* file)
{
    // get a new inode for child
    int child_inode = bitmap_first_unused(INODE_BITMAP_START_SECTOR, INODE_BITMAP_SECTORS, INODE_BITMAP_SIZE);
    if (child_inode < 0) {
        dprintf("... error: inode table is full\n");
        return -1;
    }
    dprintf("... new child inode %d\n", child_inode);

    // load the disk sector containing the child inode
    int inode_sector = INODE_TABLE_START_SECTOR + child_inode / INODES_PER_SECTOR;
    char inode_buffer[SECTOR_SIZE];
    if (Disk_Read(inode_sector, inode_buffer) < 0) return -1;
    dprintf("... load inode table for child inode from disk sector %d\n", inode_sector);

    // get the child inode
    int inode_start_entry = (inode_sector - INODE_TABLE_START_SECTOR) * INODES_PER_SECTOR;
    int offset = child_inode - inode_start_entry;
    assert(0 <= offset && offset < INODES_PER_SECTOR);
    inode_t* child = (inode_t*)(inode_buffer + offset * sizeof(inode_t));

    // update the new child inode and write to disk
    memset(child, 0, sizeof(inode_t));
    child->type = type;
    if (Disk_Write(inode_sector, inode_buffer) < 0) return -1;
    dprintf("... update child inode %d (size=%d, type=%d), update disk sector %d\n",
        child_inode, child->size, child->type, inode_sector);

    // get the disk sector containing the parent inode
    inode_sector = INODE_TABLE_START_SECTOR + parent_inode / INODES_PER_SECTOR;
    if (Disk_Read(inode_sector, inode_buffer) < 0) return -1;
    dprintf("... load inode table for parent inode %d from disk sector %d\n",
        parent_inode, inode_sector);

    // get the parent inode
    inode_start_entry = (inode_sector - INODE_TABLE_START_SECTOR) * INODES_PER_SECTOR;
    offset = parent_inode - inode_start_entry;
    assert(0 <= offset && offset < INODES_PER_SECTOR);
    inode_t* parent = (inode_t*)(inode_buffer + offset * sizeof(inode_t));
    dprintf("... get parent inode %d (size=%d, type=%d)\n",
        parent_inode, parent->size, parent->type);

    // get the dirent sector
    if (parent->type != 1) {
        dprintf("... error: parent inode is not directory\n");
        return -2; // parent not directory
    }
    int group = parent->size / DIRENTS_PER_SECTOR;
    char dirent_buffer[SECTOR_SIZE];
    if (group * DIRENTS_PER_SECTOR == parent->size) {
        // new disk sector is needed
        int newsec = bitmap_first_unused(SECTOR_BITMAP_START_SECTOR, SECTOR_BITMAP_SECTORS, SECTOR_BITMAP_SIZE);
        if (newsec < 0) {
            dprintf("... error: disk is full\n");
            return -1;
        }
        parent->data[group] = newsec;
        memset(dirent_buffer, 0, SECTOR_SIZE);
        dprintf("... new disk sector %d for dirent group %d\n", newsec, group);
    }
    else {
        if (Disk_Read(parent->data[group], dirent_buffer) < 0)
            return -1;
        dprintf("... load disk sector %d for dirent group %d\n", parent->data[group], group);
    }

    // add the dirent and write to disk
    int start_entry = group * DIRENTS_PER_SECTOR;
    offset = parent->size - start_entry;
    dirent_t* dirent = (dirent_t*)(dirent_buffer + offset * sizeof(dirent_t));
    strncpy(dirent->fname, file, MAX_NAME);
    dirent->inode = child_inode;
    if (Disk_Write(parent->data[group], dirent_buffer) < 0) return -1;
    dprintf("... append dirent %d (name='%s', inode=%d) to group %d, update disk sector %d\n",
        parent->size, dirent->fname, dirent->inode, group, parent->data[group]);

    // update parent inode and write to disk
    parent->size++;
    if (Disk_Write(inode_sector, inode_buffer) < 0) return -1;
    dprintf("... update parent inode on disk sector %d\n", inode_sector);

    return 0;
}

// used by both File_Create() and Dir_Create(); type=0 is file, type=1
// is directory
int create_file_or_directory(int type, char* pathname)
{
    int child_inode;
    char last_fname[MAX_NAME];
    int parent_inode = follow_path(pathname, &child_inode, last_fname);
    if (parent_inode >= 0) {
        if (child_inode >= 0) {
            dprintf("... file/directory '%s' already exists, failed to create\n", pathname);
            osErrno = E_CREATE;
            return -1;
        }
        else {
            if (add_inode(type, parent_inode, last_fname) >= 0) {
                dprintf("... successfully created file/directory: '%s'\n", pathname);
                return 0;
            }
            else {
                dprintf("... error: something wrong with adding child inode\n");
                osErrno = E_CREATE;
                return -1;
            }
        }
    }
    else {
        dprintf("... error: something wrong with the file/path: '%s'\n", pathname);
        osErrno = E_CREATE;
        return -1;
    }
}

// remove the child from parent; the function is called by both
// File_Unlink() and Dir_Unlink(); the function returns 0 if success,
// -1 if general error, -2 if directory not empty, -3 if wrong type
int remove_inode(int type, int parent_inode, int child_inode)
{
    // load the disk sector containing the child inode
    int inode_sector = INODE_TABLE_START_SECTOR + child_inode / INODES_PER_SECTOR;
    char inode_buffer[SECTOR_SIZE];
    if (Disk_Read(inode_sector, inode_buffer) < 0) return -1;
    dprintf("... load inode table for child inode from disk sector %d\n", inode_sector);

    // get the child inode
    int inode_start_entry = (inode_sector - INODE_TABLE_START_SECTOR) * INODES_PER_SECTOR;
    int offset = child_inode - inode_start_entry;
    assert(0 <= offset && offset < INODES_PER_SECTOR);
    inode_t* child = (inode_t*)(inode_buffer + offset * sizeof(inode_t));
    dprintf("... child_inode %d (size=%d, type=%d)\n",
        child_inode, child->size, child->type);

    // reclaim the file/directory sectors and child inode
    if (child->type != type) {
        dprintf("... wrong type, expecting type=%d\n", type);
        return -3;
    }
    if (type == 1 && child->size > 0) {
        dprintf("... error: trying to remove non-empty directory\n");
        return -2;
    }
    else if (type == 0) {
        // reclaim all data blocks belonging to the file
        for (int g = 0; g < child->size / SECTOR_SIZE; g++) {
            bitmap_reset(SECTOR_BITMAP_START_SECTOR, SECTOR_BITMAP_SECTORS, child->data[g]);
            dprintf("... reclaimed data block sector %d\n", child->data[g]);
        }
    }
    bitmap_reset(INODE_BITMAP_START_SECTOR, INODE_BITMAP_SECTORS, child_inode);
    dprintf("... reclaimed the child inode %d\n", child_inode);

    // now get the disk sector containing the parent inode
    inode_sector = INODE_TABLE_START_SECTOR + parent_inode / INODES_PER_SECTOR;
    if (Disk_Read(inode_sector, inode_buffer) < 0) return -1;
    dprintf("... load inode table for parent inode %d from disk sector %d\n",
        parent_inode, inode_sector);

    // get the parent inode
    inode_start_entry = (inode_sector - INODE_TABLE_START_SECTOR) * INODES_PER_SECTOR;
    offset = parent_inode - inode_start_entry;
    assert(0 <= offset && offset < INODES_PER_SECTOR);
    inode_t* parent = (inode_t*)(inode_buffer + offset * sizeof(inode_t));
    dprintf("... get parent inode %d (size=%d, type=%d)\n",
        parent_inode, parent->size, parent->type);
    assert(parent->type == 1);

    // get the last dirent
    parent->size--;
    int group = parent->size / DIRENTS_PER_SECTOR;
    char dirent_buffer[SECTOR_SIZE];
    if (Disk_Read(parent->data[group], dirent_buffer) < 0) return -1;
    dprintf("... load disk sector %d for dirent group %d containing last entry (%d)\n",
        parent->data[group], group, parent->size);
    int start_entry = group * DIRENTS_PER_SECTOR;
    offset = parent->size - start_entry;
    dirent_t last_one;
    memcpy(&last_one, dirent_buffer + offset * sizeof(dirent_t), sizeof(dirent_t));
    if (offset == 0) { // this group is no longer needed when we remove the last entry
        bitmap_reset(SECTOR_BITMAP_START_SECTOR, SECTOR_BITMAP_SECTORS, parent->data[group]);
        dprintf("... reclaimed data block sector %d\n", parent->data[group]);
    }

    // update parent inode to disk
    if (Disk_Write(inode_sector, inode_buffer) < 0) return -1;
    dprintf("... update parent inode on disk sector %d\n", inode_sector);

    // time to fix the parent directory (replacing the child entry with
    // the last entry); however, if the last one happens to the be
    // child, we already removed it, nothing more needs to be done
    if (last_one.inode == child_inode) {
        dprintf("... last entry is child inode, no need to do more\n");
        return 0;
    }

    int nentries = parent->size; // remaining number of directory entries 
    int idx = 0;
    while (nentries > 0) {
        char buf[SECTOR_SIZE]; // cached content of directory entries
        if (Disk_Read(parent->data[idx], buf) < 0) return -1;
        for (int i = 0; i < DIRENTS_PER_SECTOR; i++) {
            if (i > nentries) break;
            if (((dirent_t*)buf)[i].inode == child_inode) {
                // found the dirent for the removed child, replace it with
                // the last entry's dirent data
                memcpy(&((dirent_t*)buf)[i], &last_one, sizeof(dirent_t));

                // update the disk
                if (Disk_Write(parent->data[idx], buf) < 0) return -1;
                dprintf("... updated disk sector %d for dirent group %d replacing child\n",
                    parent->data[idx], idx);
                return 0;
            }
        }
        idx++; nentries -= DIRENTS_PER_SECTOR;
    }
    dprintf("... could not find child inode, ths cannot happen!\n");
    assert(0);
    return -1; // not found
}

// representing an open file
typedef struct _open_file {
    int inode; // pointing to the inode of the file (0 means entry not used)
    int size;  // file size cached here for convenience
    int pos;   // read/write position
} open_file_t;
static open_file_t open_files[MAX_OPEN_FILES];

// return true if the file pointed to by inode has already been open
int is_file_open(int inode)
{
    for (int i = 0; i < MAX_OPEN_FILES; i++) {
        if (open_files[i].inode == inode)
            return 1;
    }
    return 0;
}

// return a new file descriptor not used; -1 if full
int new_file_fd()
{
    for (int i = 0; i < MAX_OPEN_FILES; i++) {
        if (open_files[i].inode <= 0)
            return i;
    }
    return -1;
}

/* end of internal helper functions, start of API functions */

int FS_Boot(char* backstore_fname)
{
    dprintf("FS_Boot('%s'):\n", backstore_fname);
    // initialize a new disk (this is a simulated disk)
    if (Disk_Init() < 0) {
        dprintf("... disk init failed\n");
        osErrno = E_GENERAL;
        return -1;
    }
    dprintf("... disk initialized\n");

    // we should copy the filename down; if not, the user may change the
    // content pointed to by 'backstore_fname' after calling this function
    strncpy(bs_filename, backstore_fname, 1024);
    bs_filename[1023] = '\0'; // for safety

    // we first try to load disk from this file
    if (Disk_Load(bs_filename) < 0) {
        dprintf("... load disk from file '%s' failed\n", bs_filename);

        // if we can't open the file; it means the file does not exist, we
        // need to create a new file system on disk
        if (diskErrno == E_OPENING_FILE) {
            dprintf("... couldn't open file, create new file system\n");

            // format superblock
            char buf[SECTOR_SIZE];
            memset(buf, 0, SECTOR_SIZE);
            *(int*)buf = OS_MAGIC;
            if (Disk_Write(SUPERBLOCK_START_SECTOR, buf) < 0) {
                dprintf("... failed to format superblock\n");
                osErrno = E_GENERAL;
                return -1;
            }
            dprintf("... formatted superblock (sector %d)\n", SUPERBLOCK_START_SECTOR);

            // format inode bitmap (reserve the first inode to root)
            bitmap_init(INODE_BITMAP_START_SECTOR, INODE_BITMAP_SECTORS, 1);
            dprintf("... formatted inode bitmap (start=%d, num=%d)\n",
                (int)INODE_BITMAP_START_SECTOR, (int)INODE_BITMAP_SECTORS);

            // format sector bitmap (reserve the first few sectors to
            // superblock, inode bitmap, sector bitmap, and inode table)
            bitmap_init(SECTOR_BITMAP_START_SECTOR, SECTOR_BITMAP_SECTORS,
                DATABLOCK_START_SECTOR);
            dprintf("... formatted sector bitmap (start=%d, num=%d)\n",
                (int)SECTOR_BITMAP_START_SECTOR, (int)SECTOR_BITMAP_SECTORS);

            // format inode tables
            for (int i = 0; i < INODE_TABLE_SECTORS; i++) {
                memset(buf, 0, SECTOR_SIZE);
                if (i == 0) {
                    // the first inode table entry is the root directory
                    ((inode_t*)buf)->size = 0;
                    ((inode_t*)buf)->type = 1;
                }
                if (Disk_Write(INODE_TABLE_START_SECTOR + i, buf) < 0) {
                    dprintf("... failed to format inode table\n");
                    osErrno = E_GENERAL;
                    return -1;
                }
            }
            dprintf("... formatted inode table (start=%d, num=%d)\n",
                (int)INODE_TABLE_START_SECTOR, (int)INODE_TABLE_SECTORS);

            // we need to synchronize the disk to the backstore file (so
            // that we don't lose the formatted disk)
            if (Disk_Save(bs_filename) < 0) {
                // if can't write to file, something's wrong with the backstore
                dprintf("... failed to save disk to file '%s'\n", bs_filename);
                osErrno = E_GENERAL;
                return -1;
            }
            else {
                // everything's good now, boot is successful
                dprintf("... successfully formatted disk, boot successful\n");
                memset(open_files, 0, MAX_OPEN_FILES * sizeof(open_file_t));
                return 0;
            }
        }
        else {
            // something wrong loading the file: invalid param or error reading
            dprintf("... couldn't read file '%s', boot failed\n", bs_filename);
            osErrno = E_GENERAL;
            return -1;
        }
    }
    else {
        dprintf("... load disk from file '%s' successful\n", bs_filename);

        // we successfully loaded the disk, we need to do two more checks,
        // first the file size must be exactly the size as expected (thiis
        // supposedly should be folded in Disk_Load(); and it's not)
        int sz = 0;
        FILE* f = fopen(bs_filename, "r");
        if (f) {
            fseek(f, 0, SEEK_END);
            sz = ftell(f);
            fclose(f);
        }
        if (sz != SECTOR_SIZE * TOTAL_SECTORS) {
            dprintf("... check size of file '%s' failed\n", bs_filename);
            osErrno = E_GENERAL;
            return -1;
        }
        dprintf("... check size of file '%s' successful\n", bs_filename);

        // check magic
        if (check_magic()) {
            // everything's good by now, boot is successful
            dprintf("... check magic successful\n");
            memset(open_files, 0, MAX_OPEN_FILES * sizeof(open_file_t));
            return 0;
        }
        else {
            // mismatched magic number
            dprintf("... check magic failed, boot failed\n");
            osErrno = E_GENERAL;
            return -1;
        }
    }
}

int FS_Sync()
{
    if (Disk_Save(bs_filename) < 0) {
        // if can't write to file, something's wrong with the backstore
        dprintf("FS_Sync():\n... failed to save disk to file '%s'\n", bs_filename);
        osErrno = E_GENERAL;
        return -1;
    }
    else {
        // everything's good now, sync is successful
        dprintf("FS_Sync():\n... successfully saved disk to file '%s'\n", bs_filename);
        return 0;
    }
}

int File_Create(char* file)
{
    dprintf("File_Create('%s'):\n", file);
    return create_file_or_directory(0, file);
}

int File_Unlink(char* file)
{
    dprintf("FS_Unlink('%s'):\n", file);

    int child_inode;
    int parent_inode = follow_path(file, &child_inode, NULL);
    if (parent_inode >= 0) {
        if (child_inode >= 0) {
            dprintf("... file '%s' exists: parent_inode=%d, child_inode=%d\n",
                file, parent_inode, child_inode);
            if (is_file_open(child_inode)) {
                dprintf("... file '%s' is currently open\n", file);
                osErrno = E_FILE_IN_USE;
                return -1;
            }
            int ret = remove_inode(0, parent_inode, child_inode);
            if (ret >= 0) {
                dprintf("... successfully deleted file: '%s'\n", file);
                return 0;
            }
            else {
                dprintf("... error: something wrong with removing child inode\n");
                osErrno = E_GENERAL;
                return -1;
            }
        }
        else {
            dprintf("... file '%s' is not found\n", file);
            osErrno = E_NO_SUCH_FILE;
            return -1;
        }
    }
    else {
        dprintf("... error: something wrong with the file/path: '%s'\n", file);
        osErrno = E_GENERAL;
        return -1;
    }
}

int File_Open(char* file)
{
    dprintf("File_Open('%s'):\n", file);
    int fd = new_file_fd();
    if (fd < 0) {
        dprintf("... max open files reached\n");
        osErrno = E_TOO_MANY_OPEN_FILES;
        return -1;
    }

    int child_inode;
    follow_path(file, &child_inode, NULL);
    if (child_inode >= 0) { // child is the one
      // load the disk sector containing the inode
        int inode_sector = INODE_TABLE_START_SECTOR + child_inode / INODES_PER_SECTOR;
        char inode_buffer[SECTOR_SIZE];
        if (Disk_Read(inode_sector, inode_buffer) < 0) { osErrno = E_GENERAL; return -1; }
        dprintf("... load inode table for inode from disk sector %d\n", inode_sector);

        // get the inode
        int inode_start_entry = (inode_sector - INODE_TABLE_START_SECTOR) * INODES_PER_SECTOR;
        int offset = child_inode - inode_start_entry;
        assert(0 <= offset && offset < INODES_PER_SECTOR);
        inode_t* child = (inode_t*)(inode_buffer + offset * sizeof(inode_t));
        dprintf("... inode %d (size=%d, type=%d)\n",
            child_inode, child->size, child->type);

        if (child->type != 0) {
            dprintf("... error: '%s' is not a file\n", file);
            osErrno = E_GENERAL;
            return -1;
        }

        // initialize open file entry and return its index
        open_files[fd].inode = child_inode;
        open_files[fd].size = child->size;
        open_files[fd].pos = 0;
        return fd;
    }
    else {
        dprintf("... file '%s' is not found\n", file);
        osErrno = E_NO_SUCH_FILE;
        return -1;
    }
}

int File_Read(int fd, void* buffer, int size)
{
    dprintf("File_Read(fd=%d,size=%d):\n", fd, size);
    if (0 > fd || fd > MAX_OPEN_FILES) {
        dprintf("... fd=%d out of bound\n", fd);
        osErrno = E_BAD_FD;
        return -1;
    }
    if (open_files[fd].inode <= 0) {
        dprintf("... fd=%d not an open file\n", fd);
        osErrno = E_BAD_FD;
        return -1;
    }
    if (!buffer || size < 0) {
        dprintf("... invalid buffer or size parameter\n");
        osErrno = E_GENERAL;
        return -1;
    }
    dprintf("... file offset=%d, file size=%d\n",
        open_files[fd].pos, open_files[fd].size);

    // if we have reached the end of file or the read size is zero,
    // there isn't really anthing we need to do
    if (open_files[fd].pos == open_files[fd].size || size == 0)
        return 0;

    // load the disk sector containing the inode
    int inode_sector = INODE_TABLE_START_SECTOR + open_files[fd].inode / INODES_PER_SECTOR;
    char inode_buffer[SECTOR_SIZE];
    if (Disk_Read(inode_sector, inode_buffer) < 0) { osErrno = E_GENERAL; return -1; }
    dprintf("... load inode table for inode from disk sector %d\n", inode_sector);

    // get the inode
    int inode_start_entry = (inode_sector - INODE_TABLE_START_SECTOR) * INODES_PER_SECTOR;
    int offset = open_files[fd].inode - inode_start_entry;
    assert(0 <= offset && offset < INODES_PER_SECTOR);
    inode_t* inode = (inode_t*)(inode_buffer + offset * sizeof(inode_t));
    dprintf("... inode %d (size=%d, type=%d)\n", open_files[fd].inode,
        inode->size, inode->type);
    assert(inode->size == open_files[fd].size);
    assert(inode->type == 0);

    // calculate the necessary range to read in (less than a sector)
    int gidx = open_files[fd].pos / SECTOR_SIZE;
    int start_addr = gidx * SECTOR_SIZE;
    int end_addr = start_addr + SECTOR_SIZE;
    if (end_addr > inode->size) end_addr = inode->size;
    if (end_addr < open_files[fd].pos + size)
        size = end_addr - open_files[fd].pos;
    offset = open_files[fd].pos - start_addr;

    // load in the data block and copy data
    char data[SECTOR_SIZE];
    if (Disk_Read(inode->data[gidx], data) < 0) { osErrno = E_GENERAL; return -1; }
    dprintf("... load data from group %d disk sector %d (data range=%d..%d)\n",
        gidx, inode->data[gidx], start_addr, end_addr);
    memcpy(buffer, &data[offset], size);
    open_files[fd].pos += size;
    dprintf("... copied data from %d to %d of size %d, new pos=%d\n",
        start_addr + offset, start_addr + offset + size, size, open_files[fd].pos);
    return size;
}

int File_Write(int fd, void* buffer, int size)
{
    dprintf("File_Write(fd=%d,size=%d):\n", fd, size);
    if (0 > fd || fd > MAX_OPEN_FILES) {
        dprintf("... fd=%d out of bound\n", fd);
        osErrno = E_BAD_FD;
        return -1;
    }
    if (open_files[fd].inode <= 0) {
        dprintf("... fd=%d not an open file\n", fd);
        osErrno = E_BAD_FD;
        return -1;
    }
    if (!buffer || size < 0) {
        dprintf("... invalid buffer or size parameter\n");
        osErrno = E_GENERAL;
        return -1;
    }
    dprintf("... file offset=%d, file size=%d\n",
        open_files[fd].pos, open_files[fd].size);

    // if write size is zero, there isn't really anthing we need to do
    if (size == 0) return 0;

    // load the disk sector containing the inode
    int inode_sector = INODE_TABLE_START_SECTOR + open_files[fd].inode / INODES_PER_SECTOR;
    char inode_buffer[SECTOR_SIZE];
    if (Disk_Read(inode_sector, inode_buffer) < 0) { osErrno = E_GENERAL; return -1; }
    dprintf("... load inode table for inode from disk sector %d\n", inode_sector);

    // get the inode
    int inode_start_entry = (inode_sector - INODE_TABLE_START_SECTOR) * INODES_PER_SECTOR;
    int offset = open_files[fd].inode - inode_start_entry;
    assert(0 <= offset && offset < INODES_PER_SECTOR);
    inode_t* inode = (inode_t*)(inode_buffer + offset * sizeof(inode_t));
    dprintf("... inode %d (size=%d, type=%d)\n", open_files[fd].inode,
        inode->size, inode->type);
    assert(inode->size == open_files[fd].size);
    assert(inode->type == 0);

    // write one sector at a time
    int bidx = 0, remain = size;
    //dprintf("bidx=%d, remain=%d, size=%d, pos=%d\n", bidx, remain, size, open_files[fd].pos);
    while (remain > 0) {
        int gidx = open_files[fd].pos / SECTOR_SIZE;
        if (gidx == MAX_SECTORS_PER_FILE) {
            // this sort of in-the-middle handling may cause inconsistencies
            dprintf("... error: file too big, no more data blocks for the file\n");
            osErrno = E_FILE_TOO_BIG;
            return -1;
        }
        int start_addr = gidx * SECTOR_SIZE;
        int end_addr = start_addr + SECTOR_SIZE;
        if (end_addr < open_files[fd].pos + size)
            size = end_addr - open_files[fd].pos;
        offset = open_files[fd].pos - start_addr;
        //printf("gidx=%d, start_addr=%d, end_addr=%d, size=%d, offset=%d\n", gidx, start_addr, end_addr, size, offset);

        char data[SECTOR_SIZE];
        if (start_addr < open_files[fd].size) {
            // if the pointer is still in allocated data blocks, load from disk
            if (Disk_Read(inode->data[gidx], data) < 0) { osErrno = E_GENERAL; return -1; }
            dprintf("... load data from group %d disk sector %d (data range=%d..%d)\n",
                gidx, inode->data[gidx], start_addr, end_addr);
        }
        else {
            // the pointer has moved beyond allocated blocks, crate new sector
            int newsec = bitmap_first_unused(SECTOR_BITMAP_START_SECTOR, SECTOR_BITMAP_SECTORS, SECTOR_BITMAP_SIZE);
            if (newsec < 0) {
                // this sort of in-the-middle handling may cause inconsistencies
                dprintf("... error: disk is full\n");
                osErrno = E_NO_SPACE;
                return -1;
            }
            inode->data[gidx] = newsec;
            memset(data, 0, SECTOR_SIZE);
            dprintf("... new disk sector %d group %d (data range=%d..%d)\n",
                newsec, gidx, start_addr, end_addr);
        }

        // copy data, and move pointers
        memcpy(&data[offset], &buffer[bidx], size);
        dprintf("... copied data from %d to %d of size %d, new pos=%d\n",
            start_addr + offset, start_addr + offset + size, size, open_files[fd].pos + size);
        open_files[fd].pos += size; bidx += size; remain -= size; size = remain;
        //printf("pos=%d, bidx=%d, remain=%d, size=%d\n", open_files[fd].pos, bidx, remain, size);

        // update disk of the data block
        if (Disk_Write(inode->data[gidx], data) < 0) { osErrno = E_GENERAL; return -1; }
        dprintf("... update disk sector %d\n", inode->data[gidx]);
    }

    // written beyond origin file boundary, update inode
    if (open_files[fd].pos > open_files[fd].size) {
        open_files[fd].size = inode->size = open_files[fd].pos;
        if (Disk_Write(inode_sector, inode_buffer) < 0) { osErrno = E_GENERAL; return -1; }
        dprintf("... update inode table on disk sector %d\n", inode_sector);
    }
    return bidx;
}

int File_Seek(int fd, int offset)
{
    if (is_file_open(open_files[fd].inode) <= 0)//Error openning the file
    {
        osErrno = E_BAD_FD;
        return -1;
    }
    if (fd > 0 || fd > MAX_OPEN_FILES)
    {
        osErrno = E_GENERAL;
        return -1;
    }
    if (open_files[fd].size < offset || offset < 0)//Error with the size
    {
        osErrno = E_SEEK_OUT_OF_BOUNDS;
        return -1;
    }
    open_files[fd].pos = offset;//update location/position of the file
    return open_files[fd].pos;
}

int File_Close(int fd)
{
    dprintf("File_Close(%d):\n", fd);
    if (0 > fd || fd > MAX_OPEN_FILES) {
        dprintf("... fd=%d out of bound\n", fd);
        osErrno = E_BAD_FD;
        return -1;
    }
    if (open_files[fd].inode <= 0) {
        dprintf("... fd=%d not an open file\n", fd);
        osErrno = E_BAD_FD;
        return -1;
    }

    dprintf("... file closed successfully\n");
    open_files[fd].inode = 0;
    return 0;
}

int Dir_Create(char* path)
{
    dprintf("Dir_Create('%s'):\n", path);
    return create_file_or_directory(1, path);
}

int Dir_Unlink(char* path)
{
    if (path == NULL)//Empty path error
    {
        osErrno = E_GENERAL;
        return -1;
    }
    else if (strcmp(path, "/") == 0)//Cannot unlink the root
    {
        osErrno = E_ROOT_DIR;
        return -1;
    }
    int child_inode;
    //Getting the parent_inode and child_inode
    int parent_inode = follow_path(path, &child_inode, NULL);
    if (parent_inode < 0)//Directory not found
    {
        osErrno = E_NO_SUCH_DIR;
        return -1;
    }
    if (child_inode < 0)
    {
        osErrno = E_NO_SUCH_DIR;
        return -1;
    }
    //Remove_inode() function takes care of -1 general error, -2 directory is not
    //empty and -3 wrong type. It return 0 in a succesful case
    int remove = remove_inode(1, parent_inode, child_inode);
    return remove;
}

int Dir_Size(char* path)
{
    if (path == NULL)//Empty path error
    {
        osErrno = E_GENERAL;
        return -1;
    }
    int child_inode;
    int parent_inode = follow_path(path, &child_inode, NULL);
    if (child_inode < 0)//Directory not found
    {
        osErrno = E_NO_SUCH_DIR;
        return -1;
    }
    // load the disk sector containing the child inode
    int inode_sector = INODE_TABLE_START_SECTOR + child_inode / INODES_PER_SECTOR;
    char inode_buffer[SECTOR_SIZE];
    if (Disk_Read(inode_sector, inode_buffer) < 0)
    {
        osErrno = E_GENERAL;
        return -1;
    }
    // get the child inode
    int inode_start_entry = (inode_sector - INODE_TABLE_START_SECTOR) * INODES_PER_SECTOR;
    int offset = child_inode - inode_start_entry;
    assert(0 <= offset && offset < INODES_PER_SECTOR);
    inode_t* child = (inode_t*)(inode_buffer + offset * sizeof(inode_t));
    if (child->type != 1)//Is not a directory
    {
        osErrno = E_GENERAL;
        return -1;
    }
    /* YOUR CODE */
    return (child->size * sizeof(dirent_t));
}

int Dir_Read(char* path, void* buffer, int size)
{
    if (path == NULL)//Empty path error
    {
        osErrno = E_GENERAL;
        return -1;
    }
    int child_inode;
    int parent_inode = follow_path(path, &child_inode, NULL);
    if (child_inode < 0)//Directory not found
    {
        osErrno = E_NO_SUCH_DIR;
        return -1;
    }
    // load the disk sector containing the child inode
    int inode_sector = INODE_TABLE_START_SECTOR + child_inode / INODES_PER_SECTOR;
    char inode_buffer[SECTOR_SIZE];
    if (Disk_Read(inode_sector, inode_buffer) < 0)
    {
        osErrno = E_GENERAL;
        return -1;
    }
    // get the child inode
    int inode_start_entry = (inode_sector - INODE_TABLE_START_SECTOR) * INODES_PER_SECTOR;
    int offset = child_inode - inode_start_entry;
    assert(0 <= offset && offset < INODES_PER_SECTOR);
    inode_t* child = (inode_t*)(inode_buffer + offset * sizeof(inode_t));
    if (child->type != 1)//Is not a directory
    {
        osErrno = E_GENERAL;
        return -1;
    }
    if (child->size * sizeof(dirent_t) > size)
    {
        osErrno = E_BUFFER_TOO_SMALL;
        return -1;
    }
    int entries = child->size;//Number of directory entries
    int index = 0;//index of the buffer
    int i = 0;//index of the inode_buffer
    while(entries > 0)
    {
        char inode_buffer[SECTOR_SIZE];
        Disk_Read(child->data[i], inode_buffer);
        int copy = DIRENTS_PER_SECTOR;
        if (DIRENTS_PER_SECTOR > entries)
        {
            copy = entries;
        }
        memcpy(&buffer[index], inode_buffer, copy * sizeof(dirent_t));
        entries -= copy;
        i += 1;
        index += copy * sizeof(dirent_t);
    }
    ///* YOUR CODE */
    return child->size;
}

