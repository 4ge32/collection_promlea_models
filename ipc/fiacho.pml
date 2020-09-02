#define N 2 /* Number of threads */

typedef IPC_Prm {
	bool has_receive_part;
	bool open_wait;
	short partner;
	bool has_send_part;
};

typedef IPC_State {
	bit ready;
	bit receiving;
	bit polling;
	bit ipc_in_progress;
	bit send_in_progress;
	bit busy;
	bit cancel;
	bit polling_long;
	bit busy_long;
	bit rcvlong_in_progress;
};

typedef IPC_Output {
	short error;
	short dope;
	bool msg_copied;
	short rcv_source = -1;
};

typedef Sender_List {
	short snd_ls[N];
	byte last_index;
};

IPC_Prm ipc_g_prm[N];
IPC_State ipc_state[N];
IPC_Output ipc_output[N];
short rcv_partner[N];
short snd_partner[N];
Sender_List sender_ls[N];

short ipc_lock_owner[N] = -1;

inline dequeue_from_snd_ls(dfsl_snd_pid, dfsl_rec_pid, dfsl_i, dfsl_in_snd_ls) {
	skip
}

inline commit_ipc_success(cis_pid, cis_err) {
	printf("commit_ipc_success(pid:%d, err:%d)\n", cis_pid, cis_err);
	ipc_output[cis_pid].dope = cis_err;
}

inline commit_ipc_failure(cif_pid, cif_err) {
	printf("commit_ipc_failure(pid:%d, err:%d)\n", cif_pid, cif_err);
	/* Remove loc 71 coz' we don't model delayed_ipc */
	ipc_output[cif_pid].dope = 0;
	commit_ipc_success(cif_pid, cif_err);
}

inline do_receive(ds_pid, ds_partner, ds_ret) {
	skip
}

inline ipc_snd_regs(isr_snd_pid, isr_rec_pid, isr_ret) {
	skip
}

/* @param ds_pid : sender
 * @param ds_partner : receiver
 * @param ds_ret : sender'r IPC error code
 */
inline do_send(ds_pid, ds_partner, ds_ret) {
	printf("do_send(pid:%d, partner:%d, ret:%d)\n", ds_pid, ds_partner, ds_ret);
	if
	:: (ds_partner == -1 || ds_partner == -2 || ds_partner >= N) ->
		printf("do_send: Error Not Existent Partner\n");
		ds_ret = -2
	:: else ->
		/*** Setup phase ***/
		snd_partner[ds_pid] = ds_partner;

		/* putting the sender into state "send_prepared" */
		atomic {
			ipc_state[ds_pid].polling = 1;
			ipc_state[ds_pid].ipc_in_progress = 1;
			ipc_state[ds_pid].send_in_progress = 1;
		}
		if
		:: (ipc_state[ds_pid].cancel) ->
			atomic {
				ipc_state[ds_pid].send_in_progress = 0;
				ipc_state[ds_pid].polling = 0;
				ipc_state[ds_pid].polling_long = 0;
				ipc_state[ds_pid].ipc_in_progress = 0;
			}
			/* ds_ret = Send canceld */
			ds_ret = -6;
		:: else ->
			/* enqueue in sender list of partner */
			printf("enqueue myself (%d) in sender list of partner (partner:%d, current index:%d)\n",
					ds_pid, ds_partner, sender_ls[ds_partner].last_index);
			atomic {
				sender_ls[ds_partner].snd_ls[sender_ls[ds_partner].last_index] = ds_pid;
				sender_ls[ds_partner].last_index = sender_ls[ds_partner].last_index + 1;
			};
			/*** Rendezvous phase ***/
			/* try a rendezvous with the partner */
			ipc_snd_regs(ds_pid, ds_partner, ds_ret);
			printf("ipc_snd_regs returned %d\n", ds_ret);

			if
			/* transient error */
			:: (ds_ret == -1) ->
				/* TIMEOUT */
				atomic {
					ipc_state[ds_pid].polling = 0;
					ipc_state[ds_pid].ipc_in_progress = 0;
					ipc_state[ds_pid].send_in_progress = 0;
				}

				/* dequeue in sender list of partner */
				byte ds1_i;
				bool ds1_in_snd_ls;

				ds1_i = 0;
				ds1_in_snd_ls = false;
				dequeue_from_snd_ls(ds_pid, ds_partner, ds1_i, ds1_in_snd_ls);

				/* Send timeout */
				ds_ret = -4;

			:: else ->
               byte i;
			   bool in_snd_ls;

			   i = 0;
			   in_snd_ls = false;
			   atomic {
				   do
				   :: skip
				   od;
			   };
			fi;
		fi;
	fi
}

/* Prepare an IPC-receive operation.
 * This method must be called before do_receive() and, when carrying out
 * a combined snd-and-receive operation, also before do_send().
 * @param pr_snd_pid: IPC partner we want to receive a message from.
 *  				  -1 if we accept IPC from any partner (''open wait'').
 */
inline prepare_receive(pr_rec_pid, pr_snd_pid, pr_has_send_part) {
	printf("prepare_receive(rec:%d, snd:%d, has_send:%d)\n",
			pr_rec_pid, pr_snd_pid, pr_has_send_part);
	/* pr_snd_pid might be -1 for open_wait/receive from nil thread */
	rcv_partner[pr_rec_pid] = pr_snd_pid;
	ipc_state[pr_rec_pid].receiving = 1;

	if
	:: (!pr_has_send_part) ->
		ipc_state[pr_rec_pid].ipc_in_progress = 1;
		if
		:: (ipc_state[pr_rec_pid].cancel) -> ipc_state[pr_rec_pid].ipc_in_progress = 0
		:: else
		fi
	fi
}

/* L4 IPC system call */
active [N] proctype thread() provided(ipc_lock_owner[_pid] == -1 ||
		ipc_lock_owner[_pid] == _pid) {
	bool have_sender;
	short sender

		do
		::
				/* Initialize local var */
		have_sender = false;
		sender = -1;

		/* Initialize global var ipc_state */
		ipc_state[_pid].receiving = 0;
		ipc_state[_pid].polling = 0;
		ipc_state[_pid].ipc_in_progress = 0;
		ipc_state[_pid].send_in_progress = 0;
		ipc_state[_pid].busy = 0;
		ipc_state[_pid].cancel = 0;
		ipc_state[_pid].polling_long = 0;
		ipc_state[_pid].busy_long = 0;
		ipc_state[_pid].rcvlong_in_progress = 0;

		/* Initialize global var ipc_output */
		ipc_output[_pid].error = -10;
		ipc_output[_pid].dope = -10;
		ipc_output[_pid].msg_copied = false;
		ipc_output[_pid].rcv_source = -1;

		assert(ipc_lock_owner[_pid] != _pid);

		/* nondeterministic choice of IPC parameters */
		atomic {
			if
			:: ipc_g_prm[_pid].has_receive_part = false;
			:: ipc_g_prm[_pid].has_receive_part = true;
			fi;
			if
			:: ipc_g_prm[_pid].open_wait = false;
			:: ipc_g_prm[_pid].open_wait = true;
			fi;
			if
			:: ipc_g_prm[_pid].partner  = -2;
			:: ipc_g_prm[_pid].partner  = 0;
			:: ipc_g_prm[_pid].partner  = 1;
			:: ipc_g_prm[_pid].partner  = 2;
			fi;
			if
			:: ipc_g_prm[_pid].has_send_part = false;
			:: ipc_g_prm[_pid].has_send_part = true;
			fi;
		};

		printf("IPC thread: %d partner: %d snd:%d rcv: %d open:%d\n",
				_pid, ipc_g_prm[_pid].partner,
				ipc_g_prm[_pid].has_send_part,
				ipc_g_prm[_pid].has_receive_part,
				ipc_g_prm[_pid].open_wait);

		ipc_state[_pid].ready = 1;

		/* Skip Next Period IPC */

		if
		:: (ipc_g_prm[_pid].has_receive_part) ->
			if
			:: (ipc_g_prm[_pid].open_wait) ->
				have_sender = true
			:: else ->
				if
				/* partner == nil_thread? */
				:: (ipc_g_prm[_pid].partner == -2)
				:: else ->
				/* Skip Checking Partner is IRQ */
					if
					/* partner null or does not exist? */
					:: (ipc_g_prm[_pid].partner == -1 ||
						ipc_g_prm[_pid].partner >= N) ->
						printf("commit_ipc_failure(Enot_existent)\n");
						goto noop
					:: else ->
						/* Skip Checking Preemption IPC */
						sender = ipc_g_prm[_pid].partner;
						have_sender = true
					fi
				fi
			fi;
			if
			:: (have_sender) ->
				printf("prepare_receive(sender = %d)\n", sender);
				prepare_receive(_pid, sender, ipc_g_prm[_pid].has_send_part);
			:: else
			fi
		:: else
		fi;

		if
		:: (ipc_g_prm[_pid].has_send_part) ->
			do_send(_pid, ipc_g_prm[_pid].partner, ipc_output[_pid].error);
			printf("do_send returned %d\n", ipc_output[_pid].error)
		:: else ->
			ipc_output[_pid].dope = 0
		fi;

		/* Send Finished, Do Receive Now */
		if
		:: (ipc_g_prm[_pid].has_receive_part && ipc_output[_pid].error >= 0) ->
			if
			:: (have_sender) ->
				do_receive(_pid, sender, ipc_output[_pid].error)
				printf("do_receive returned %d\n", ipc_output[_pid].error);
				if
				:: (ipc_output[_pid].error != -3) ->
					goto success
				:: else
				fi
			:: else /* Skip Checking Partner is Valid IRQ */
			fi;

			/* Skip Checking Partner is a Free IRQ */

			printf("commit_ipc_failure(Retimeout)\n");
			commit_ipc_failure(_pid, -3);
		:: else ->
			atomic {
				ipc_state[_pid].ipc_in_progress = 0;
				ipc_state[_pid].send_in_progress = 0;
				ipc_state[_pid].polling = 0;
				ipc_state[_pid].polling_long = 0;
				ipc_state[_pid].receiving = 0;
				ipc_state[_pid].busy = 0;
				ipc_state[_pid].rcvlong_in_progress = 0;
				ipc_state[_pid].busy_long = 0
			}
		fi;

		success:
			/* commit_ipc_success */
			printf("commit_ipc_success(ret)\n");
			commit_ipc_success(_pid, ipc_output[_pid].error);
		noop:
			skip
		od
}
