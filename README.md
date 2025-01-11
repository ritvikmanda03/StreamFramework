# MP4-Group37

## Steps to Run

1. Copy paste stream.go to all 10 VMs
2. Uncomment the beginning myName, myIP, myID for the appropriate VM you are on (note introducer is hardcoded as our group's VM1)
3. Next, build and run the introducer VM, which is VM1
4. Next, you want to run the stream.go file on the rest of the VMs

5. To run the Rainstorm streaming code, first ensure that the VM you are executing locally contains op1_exec and op2_exec files
    - This can be done by simply building the op1.1.go, op1.2.go for application 1 and building op2.1.go and op2.2.go for application 2

6. Invoke Rainstorm via the following command:
##  
RainStorm <op1_exe> <op2_exe> <hydfs_src_file> <hydfs_dest_filename> <num_tasks>
##  
7. Additionally, for any VM, you can type the following commands to create and manage your hybrid distributed file system:


list_mem: list the membership list

list_self: list self’s id

join: join the group (it is ok for this command to be implicitly executed when the process starts, or you could implement the command explicitly)

leave: voluntarily leave the group (different from a failure)

enable/disable suspicion (enable_sus / disable_sus)

suspicion on/off status (status_sus)

##  

create localfilename HyDFSfilename (from local dir). 

get HyDFSfilename localfilename  (fetch to local dir)

append localfilename HyDFSfilename 

merge HyDFSfilename 

ls HyDFSfilename

store (at any process/VM)

getfromreplica VMaddress HyDFSfilename localfilename

list_mem_ids

multiappend(filename, VMi, … VMj, localfilenamei,....localfilenamej)
