Require Import Arith.
Require Import List.
Require Import Bool.
Require Import Coq.Init.Datatypes.
Require Import Nat.
Require Import Classical_Pred_Type.
Require Import Classical_Prop.
Require Import Lia.

Definition process := nat.

(* event_num := n where event is nth global event on a process p for some computation *)
Inductive event : Type :=
	| Event (proc : process)
	| Event_send (proc : process) (* not listing receiving process allows for multicasts/broadcasts *)
	| Event_receive (proc : process)
		(send_event_proc : process) (send_event_num : nat).

Definition computation := list event.

(* Returns which process an event belongs to *)
Definition event_process (comp : computation) (a : nat) : process := 
	match nth a comp (Event 0) with
	| Event p => p
	| Event_send p => p
	| Event_receive p _ _ => p
	end.

(*
	returns prop that a b in the same process and a comes before b
*)
Definition seq (comp : computation) (a b : nat) : Prop :=
	(event_process comp a = event_process comp b) /\ (a < b).
	
(*
	returns prop that a is send msg and b is receive msg for same message
*)
Definition msg (comp : computation) (a b : nat) : Prop :=
	match nth b comp (Event 0) with
	| Event_receive _ s_p s_n => a = s_n /\ (event_process comp s_n = s_p)
	| _ => False
	end.

(* well-formedness guarantees *)
Definition sender_prec (comp : computation) (a : nat) : Prop :=
	match nth a comp (Event 0) with
	| Event_receive _ _ s_n => s_n < a
	| _ => True
	end.

Definition sender_proc (comp : computation) (a : nat) : Prop :=
	match nth a comp (Event 0) with
	| Event_receive _ s_p s_n => event_process comp s_n = s_p
	| _ => True
	end.

(* remove? *)

Definition send_rec_proc (comp : computation) (a : nat) : Prop :=
	match nth a comp (Event 0) with
	| Event_receive p s_p _ => ~(p = s_p)
	| _ => True
	end.

(* sp and dp mean same process and different process
  R a b => Rtrans a b
  R a b, Rtrans b c => Rtrans a c

  apply transitive closure from library
 *)
Inductive after2 : computation -> nat -> nat -> Prop :=
	| after_sp2 (comp : computation) (a b : nat) (H : seq comp a b) : after2 comp a b
	| after_dp2 (comp : computation) (a b : nat) (H : msg comp a b) : after2 comp a b
	| after_trans2 (comp : computation) (a b c : nat) (Htrans1 : after2 comp a b) (Htrans2 : after2 comp b c) : b < length comp -> after2 comp a c.

Inductive after : computation -> nat -> nat -> Prop :=
	| after_sp (comp : computation) (a b : nat) (H : seq comp a b) : after comp a b
	| after_dp (comp : computation) (a b : nat) (H : msg comp a b) : after comp a b
	| after_trans (comp : computation) (a b c : nat) (Htrans1 : seq comp a b \/ msg comp a b) (Htrans2 : after2 comp b c) : b < length comp -> after comp a c.

	(* show after iff after2, use after 2 in main theorem statement, switch it to after when using for induction (after and after') *)

Definition event_index := nat.

Definition time := nat.

Definition vclock_time := process -> time.

Definition clocks := process -> vclock_time.

Definition time_stamps := nat -> vclock_time.

Definition state := (nat * clocks * time_stamps) % type.


Definition event_eqb (a : nat) (b : nat) : bool :=
	a =? b.

Definition update {A B} (eqA : A -> A -> bool) (f : A -> B) (i : A) (x : B)
	: A -> B :=
	fun (j : A) => if eqA i j then x else f j.

(* Define general update function *)
(* look up decidability of equality *)
(* === define a process_eqb instead of Nat.eqb? === *)
Definition update_clock (clocks_list : clocks) (update_p : process)
	: clocks :=
	update Nat.eqb clocks_list update_p 
		(update Nat.eqb (clocks_list update_p) update_p
		((clocks_list update_p update_p) + 1)).

Definition update_event_time (p : process) (update_e : nat) (event_times : time_stamps)
	(clocks: clocks) : time_stamps := 
	update event_eqb event_times update_e (clocks p).

Definition update_clock_receive (r_p : process) (s_p : process)
	(timestamp_receive : vclock_time) (clocks_list: clocks) : clocks :=
	update Nat.eqb clocks_list r_p 
		(fun (p : process) =>
			if (timestamp_receive p) <? (clocks_list r_p p) then
				if r_p =? p then (clocks_list r_p p) + 1
				else clocks_list r_p p
			else
				if (r_p =? p) || (s_p =? p) then (timestamp_receive p) + 1
				else timestamp_receive p).

Definition step (s : state) (e : event) : state :=
	let i := fst (fst s) in
	let c := snd (fst s) in
	let event_times := snd s in
	match e with
	| (Event p) =>
		let clocks' := update_clock c p in
		let event_times' := update_event_time p i event_times clocks' in
		((i+1), clocks', event_times')
	| (Event_send p) =>
		let clocks' := update_clock c p in
		let event_times' := update_event_time p i event_times clocks' in
		((i+1), clocks', event_times')
	| (Event_receive p s_p s_n) =>
		let timestamp_receive := event_times s_n in
		let clocks' := update_clock_receive p s_p timestamp_receive c in
		let event_times' := update_event_time p i event_times clocks' in
		((i+1), clocks', event_times')
	end.

(* === ask about fixpoint? === *)
(* refactor second update_clock out *)
(* refactor out general update function *)
Definition run_computation (comp : computation) (s : state)
	: state :=
	fold_left step comp s.

Definition init_clocks : clocks := fun (p1 : process) (p2 : process) => 0.
Definition init_timestamps : time_stamps := fun (e : nat) (p : process) => 0.
Definition init_state : state := (0, init_clocks, init_timestamps).

Lemma comp_step:
	forall (comp : computation) (tl : event),
	let event_timestamps_tl1 := run_computation (comp ++ tl :: nil) init_state in
	let event_timestamps_tl2 := step (run_computation comp init_state) tl in
	event_timestamps_tl1 = event_timestamps_tl2.
Proof.
	intros comp tl H1 H2.
	unfold H1. unfold H2.
	apply (fold_left_app step comp (tl :: nil) init_state).
Qed.

Lemma fold_step:
	forall (comp : computation) (tl : event),
	fold_left step (tl :: nil) (fold_left step comp init_state) =
	step (fold_left step comp init_state) tl.
Proof.
	intros comp tl. simpl. reflexivity.
Qed.

Lemma comp_tail:
	forall (comp : computation) (tl : event),
	let run_comp := 
		run_computation (comp ++ (tl :: nil)) init_state in
	let event_timestamps_tl1 := run_comp in (* change naming, bc includes all 3 state values === *)
	let event_timestamps_tl2 := (run_computation (tl :: nil) (run_computation comp init_state)) in
	event_timestamps_tl1 = event_timestamps_tl2.
Proof.
	intros comp tl H0 H1 H2.
	unfold H1. unfold H2. unfold H0.
	rewrite (comp_step comp tl).
	- unfold run_computation.
		apply (fold_step comp tl).
Qed.

Lemma list_tl:
	forall (l : list event),
	length l <> 0 ->
	exists (l' : list event) (tl : event),
	l = l' ++ (tl :: nil).
Proof.
	intros.
	exists (removelast l). exists (last l (Event 0)).
	apply app_removelast_last.
	unfold not. intros Hcompnil.
	pose proof (length_zero_iff_nil l) as Hnil.
	destruct Hnil as [Hnil1 Hnil2].
	apply Hnil2 in Hcompnil.
	rewrite Hcompnil in H.
	unfold not in H. apply H. reflexivity.
	(* not how contradiction is typically done, but works - probably fix *)
Qed.

Lemma comp'_len:
	forall (comp comp' : computation) (tl : event),
	comp = comp' ++ tl :: nil ->
	length comp' = length comp - 1.
Proof.
	intros. rewrite H. rewrite (app_length comp' (tl :: nil)). simpl. lia.
Qed.

Lemma n_value:
	forall (comp : computation),
	fst (fst (run_computation comp init_state)) = length comp.
Proof.
	intros comp. remember (length comp) as n eqn:Hn. generalize dependent comp.
	induction n.
	-	intros. symmetry in Hn. apply (length_zero_iff_nil comp) in Hn as Hcomp. rewrite Hcomp. reflexivity.
	-	intros comp Hlen. destruct (list_tl comp) as [comp' Hcomp']. {
			symmetry in Hlen. rewrite Hlen. lia.
		}
		{
			destruct Hcomp' as [tl Hcomp]. {
				pose proof (comp'_len comp comp' tl  Hcomp) as Hcomp'.
				rewrite Hcomp. rewrite (comp_step comp' tl). {
					destruct tl; unfold step; simpl; rewrite (IHn comp'); lia.
				}
			}
		}
Qed.

Lemma preserve_proc:
	forall (comp : computation) (tl : event) (a : nat),
	a < length comp ->
	event_process comp a = event_process (comp ++ tl :: nil) a.
Proof.
	intros. unfold event_process. rewrite (app_nth1 comp (tl :: nil) (Event 0)). reflexivity. apply H.
Qed.

Lemma preserve_sender_prec:
	forall (comp comp' : computation) (tl : event),
	comp = comp' ++ tl :: nil ->
	(forall a : event_index, sender_prec comp a) ->
	(forall a : event_index, sender_prec comp' a).
Proof.
	intros. unfold sender_prec.
	assert (a < length comp' \/ ~(a < length comp')). { apply classic. }
	destruct H1 as [Ha_lt | Ha_ge]. {
		rewrite <- (app_nth1 comp' (tl :: nil) (Event 0) Ha_lt).
		unfold sender_prec in H0. rewrite H in H0. apply (H0 a).
	}
	{
		apply not_lt in Ha_ge.
		rewrite (nth_overflow comp' (Event 0)). { reflexivity. } { apply Ha_ge. }
	}
Qed.

Lemma preserve_sender_proc:
	forall (comp comp' : computation) (tl : event),
	comp = comp' ++ tl :: nil ->
	(forall a : event_index, sender_prec comp a) ->
	(forall a : event_index, sender_proc comp a) ->
	(forall a : event_index, sender_proc comp' a).
Proof.
	intros. unfold sender_proc.
	assert (a < length comp' \/ ~(a < length comp')). { apply classic. }
	destruct H2 as [Ha_lt | Ha_ge]. {
		rewrite <- (app_nth1 comp' (tl :: nil) (Event 0) Ha_lt).
		unfold sender_proc in H1. rewrite H in H1. specialize (H1 a).
		unfold sender_prec in H0. rewrite H in H0. specialize (H0 a).
		destruct (nth a (comp' ++ tl :: nil) (Event 0)) eqn:Ha.
		{ reflexivity. }
		{ reflexivity. }
		{ rewrite (preserve_proc comp' tl send_event_num). apply H1. { lia. } }
	}
	{
		apply not_lt in Ha_ge.
		rewrite (nth_overflow comp' (Event 0)). { reflexivity. } { apply Ha_ge. }
	}
Qed.

Lemma preserve_send_rec_proc:
	forall (comp comp' : computation) (tl : event),
	comp = comp' ++ tl :: nil ->
	(forall a : event_index, send_rec_proc comp a) ->
	(forall a : event_index, send_rec_proc comp' a).
Proof.
	intros. unfold send_rec_proc.
	assert (a < length comp' \/ ~(a < length comp')). { apply classic. }
	destruct H1 as [Ha_lt | Ha_ge]. {
		rewrite <- (app_nth1 comp' (tl :: nil) (Event 0) Ha_lt).
		unfold sender_prec in H0. rewrite H in H0. apply (H0 a).
	}
	{
		apply not_lt in Ha_ge.
		rewrite (nth_overflow comp' (Event 0)). { reflexivity. } { apply Ha_ge. }
	}
Qed.

Lemma preserve_seq:
	forall (comp comp' : computation) (tl : event) (a b : event_index),
	a < length comp' ->
	b < length comp' ->
	comp = comp' ++ tl :: nil ->
	seq comp a b ->
	seq comp' a b.
Proof.
	intros. unfold seq. unfold seq in H2.
	rewrite (preserve_proc comp' tl a). rewrite (preserve_proc comp' tl b). rewrite H1 in H2. apply H2.
	{ apply H0. } { apply H. }
Qed.

Lemma maintain_seq:
	forall (comp comp' : computation) (tl : event) (a b : event_index),
	a < length comp' ->
	b < length comp' ->
	comp = comp' ++ tl :: nil ->
	seq comp' a b ->
	seq comp a b.
Proof.
	intros. unfold seq. unfold seq in H2. rewrite H1.
	rewrite <- (preserve_proc comp' tl a H). rewrite <- (preserve_proc comp' tl b H0).
	apply H2.
Qed.

Lemma preserve_msg:
	forall (comp comp' : computation) (tl : event) (a b : event_index),
	a < length comp' ->
	b < length comp' ->
	comp = comp' ++ tl :: nil ->
	msg comp a b ->
	msg comp' a b.
Proof.
	intros. unfold msg. unfold msg in H2.

	destruct (nth b comp (Event 0)) eqn:Hnth_b.
	{ inversion H2. }
	{ inversion H2. }
	{
		rewrite <- (app_nth1 comp' (tl :: nil) (Event 0) H0).
		rewrite H1 in Hnth_b. rewrite Hnth_b.
		rewrite (preserve_proc comp' tl send_event_num). rewrite H1 in H2. apply H2.
		{ destruct H2 as [Ha_sen Hep]. rewrite <- Ha_sen. apply H. }
	}
Qed.

Lemma maintain_msg:
	forall (comp comp' : computation) (tl : event) (a b : event_index),
	a < length comp' ->
	b < length comp' ->
	comp = comp' ++ tl :: nil ->
	(forall a : event_index, sender_prec comp' a) ->
	msg comp' a b ->
	msg comp a b.
Proof.
	intros. unfold msg in H3. unfold msg. rewrite H1.
	specialize (H2 b). unfold sender_prec in H2.
	rewrite (app_nth1 comp' (tl :: nil) (Event 0) H0).
	destruct (nth b comp' (Event 0)).
	{ inversion H3. }
	{ inversion H3. }
	{ rewrite <- (preserve_proc comp' tl send_event_num). apply H3. { lia. } }
Qed.

Lemma maintain_after2:
	forall (comp comp' : computation) (tl : event) (a b : event_index),
	a < length comp' ->
	b < length comp' ->
	comp = comp' ++ tl :: nil ->
	(forall a : event_index, sender_prec comp' a) ->
	after2 comp' a b ->
	after2 comp a b.
Proof.
	intros. induction H3.
	- apply (maintain_seq comp comp0 tl a b H H0 H1) in H3. apply (after_sp2 comp a b H3).
	- apply (maintain_msg comp comp0 tl a b H H0 H1 H2) in H3. apply (after_dp2 comp a b H3).
	- assert (after2 comp a b). { apply (IHafter2_1 H H3 H1 H2). }
		assert (after2 comp b c). { apply (IHafter2_2 H3 H0 H1 H2). }
		assert (length comp = length comp0 + 1). { rewrite H1. rewrite (app_length comp0 (tl :: nil)). simpl. lia. }
		apply (after_trans2 comp a b c H4 H5). { lia. }
Qed.

Lemma maintain_trans:
	forall (comp comp' : computation) (tl : event) (a b : event_index),
	a < length comp' ->
	b < length comp' ->
	comp = comp' ++ tl :: nil ->
	(forall a : event_index, sender_prec comp' a) ->
	(exists x : event_index, x < length comp' /\ (seq comp' a x \/ msg comp' a x) /\ after2 comp' x b) ->
	(exists x : event_index, x < length comp /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b).
Proof.
	intros. destruct H3 as [x [Hx_bound [Hbase Hafter2]]]. exists x.
	split. pose proof (comp'_len comp comp' tl H1) as Hcomp'. lia.
	split. destruct Hbase as [Hseq | Hmsg]. {
		left. apply (maintain_seq comp comp' tl a x). { lia. } { lia. } { apply H1. } { apply Hseq. }
	}
	{
		right. apply (maintain_msg comp comp' tl a x). { lia. } { lia. } { apply H1. } { apply H2. } { apply Hmsg. }
	}
	apply (maintain_after2 comp comp' tl x b).
	{ lia. }
	{ lia. }
	{ apply H1. }
	{ apply H2. }
	{ apply Hafter2. }
Qed.

Ltac simpl_step :=
	unfold update_clock; simpl; unfold update_event_time; unfold update_clock_receive; unfold update; unfold event_eqb.

Ltac preserve_ets_simpl Ha_neq :=
	simpl_step; rewrite Ha_neq; reflexivity.

Lemma preserve_ets:
	forall (comp : computation) (tl : event) (a : nat),
	a < length comp ->
	let event_timestamps : time_stamps := 
		snd (run_computation comp init_state) in
	let event_timestamps_tl : time_stamps := 
		snd (run_computation (comp ++ (tl :: nil)) init_state) in
	event_timestamps a = event_timestamps_tl a.
Proof.
	intros comp tl a Ha H0 H1.
	unfold H0. unfold H1.
	rewrite (comp_tail comp tl).
	unfold run_computation.
	rewrite (fold_step comp tl).
	assert ( (fst (fst (fold_left step comp init_state)) =? a) = false) as Ha_neq. {
		assert (
			run_computation comp init_state =
			fold_left step comp init_state
		) as Hrun_comp. {
			unfold run_computation. reflexivity.
		}
		rewrite <- Hrun_comp.
		rewrite (n_value comp). apply Nat.eqb_neq. intros Han.
		rewrite Han in Ha. apply Nat.lt_irrefl in Ha. inversion Ha.
	}
	destruct tl; preserve_ets_simpl Ha_neq. 
Qed.

Lemma le_refl_contra:
	forall (a : nat),
	~(S a <= a).
Proof.
	intros.
	induction a.
	- unfold not. intros contra.
		inversion contra.
	- unfold not. intros contra.
		apply le_S_n in contra.
		apply IHa in contra.
		inversion contra.
Qed.


Lemma comp_ef:
	forall { A } (l : list A),
	2 = length l ->
	exists (e : A) (f : A),
	l = e :: f :: nil.
Proof.
	intros. destruct l.
	- simpl in H. inversion H.
	- destruct l.
		+ simpl in H. inversion H.
		+ destruct l. {
			exists a. exists a0. reflexivity.
		}
		{
			simpl in H. apply eq_add_S in H. apply eq_add_S in H. inversion H.
		}
Qed.

Lemma list_not_nil:
	forall { A : Type } (l : list A),
	length l >= 2 -> length l <> 0.
Proof.
	unfold not. intros. rewrite H0 in H. inversion H.
Qed.

Lemma final_clocks:
	forall (comp : computation) (a : nat) (p : process),
	a < length comp ->
	p = event_process comp a ->
	snd (run_computation comp init_state) a p <=
	snd (fst (run_computation comp init_state)) p p.
Proof.
	intros comp. remember (length comp) as n. generalize dependent comp.
	induction n.
	- intros. inversion H.
	- intros comp Hlen a p Ha_bound Ha_proc.
		destruct (list_tl comp) as [comp' Hcomp']. {
			symmetry in Hlen. rewrite Hlen. lia.
		}
		{
			destruct Hcomp' as [tl Hcomp]. {
				assert (a = length comp' \/ ~(a = length comp')) as Ha. { apply classic. }
				destruct Ha as [Ha | Ha_neq]. {
					(* a is end of list *)

					rewrite Hcomp. rewrite (comp_step comp' tl). unfold step.
					unfold event_process in Ha_proc. rewrite Ha in Ha_proc. rewrite Hcomp in Ha_proc. rewrite (nth_middle comp' nil tl (Event 0)) in Ha_proc.
					destruct tl; simpl; simpl_step; rewrite (n_value comp'); rewrite Ha; rewrite Ha_proc; rewrite Nat.eqb_refl; rewrite Nat.eqb_refl; rewrite Nat.eqb_refl; lia.
				}
				{
					(* use IH *)
					pose proof (comp'_len comp comp' tl Hcomp) as Hcomp'.
					assert (a < length comp') as Ha_bound'. { lia. }
					rewrite Hcomp. rewrite <- (preserve_ets comp' tl a Ha_bound').
					

					rewrite (comp_step comp' tl). unfold step. apply Nat.eqb_neq in Ha_neq.

					destruct tl. {
						simpl. simpl_step.
						assert (proc = p \/ ~(proc = p)) as Hproc_p. { apply classic. }
						assert (
							snd (run_computation comp' init_state) a p <=
							snd (fst (run_computation comp' init_state)) p p
						) as IHn_hyp. {
							apply (IHn comp'). 
							{ lia. }
							{ lia. }
							{ rewrite Hcomp in Ha_proc. rewrite <- (preserve_proc comp' (Event proc) a) in Ha_proc. apply Ha_proc. { apply Ha_bound'. } }
						}

						destruct Hproc_p as [Hproc_p | Hproc_p_neq]. {
							rewrite Hproc_p. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.

							apply (Nat.le_trans
								(snd (run_computation comp' init_state) a p)
								(snd (fst (run_computation comp' init_state)) p p)
								(snd (fst (run_computation comp' init_state)) p p + 1)).
							{ apply IHn_hyp. }
							lia.
						}
						{
							apply Nat.eqb_neq in Hproc_p_neq. rewrite Hproc_p_neq. apply IHn_hyp.
						}
					}
					{
						simpl. simpl_step.
						assert (proc = p \/ ~(proc = p)) as Hproc_p. { apply classic. }
						assert (
							snd (run_computation comp' init_state) a p <=
							snd (fst (run_computation comp' init_state)) p p
						) as IHn_hyp. {
							apply (IHn comp'). 
							{ lia. }
							{ lia. }
							{ rewrite Hcomp in Ha_proc. rewrite <- (preserve_proc comp' (Event_send proc) a) in Ha_proc. apply Ha_proc. { apply Ha_bound'. } }
						}

						destruct Hproc_p as [Hproc_p | Hproc_p_neq]. {
							rewrite Hproc_p. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.

							apply (Nat.le_trans
								(snd (run_computation comp' init_state) a p)
								(snd (fst (run_computation comp' init_state)) p p)
								(snd (fst (run_computation comp' init_state)) p p + 1)).
							{ apply IHn_hyp. }
							lia.
						}
						{
							apply Nat.eqb_neq in Hproc_p_neq. rewrite Hproc_p_neq. apply IHn_hyp.
						}
					}
					{
						simpl. simpl_step.
						assert (proc = p \/ ~(proc = p)) as Hproc_p. { apply classic. }
						assert (
							snd (run_computation comp' init_state) a p <=
							snd (fst (run_computation comp' init_state)) p p
						) as IHn_hyp. {
							apply (IHn comp'). 
							{ lia. }
							{ lia. }
							{ rewrite Hcomp in Ha_proc. rewrite <- (preserve_proc comp' (Event_receive proc send_event_proc send_event_num) a) in Ha_proc. apply Ha_proc. { apply Ha_bound'. } }
						}

						destruct Hproc_p as [Hproc_p | Hproc_p_neq]. {
							rewrite Hproc_p. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.

							destruct (
								snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) p p
							) eqn:Hmax.
							{
								lia.
							}
							{
								rewrite orb_true_l. apply Nat.ltb_nlt in Hmax. apply Nat.nlt_ge in Hmax.
								apply (Nat.le_trans
									(snd (run_computation comp' init_state) a p)
									(snd (fst (run_computation comp' init_state)) p p)
									(snd (run_computation comp' init_state) send_event_num p + 1)).
								{ apply IHn_hyp. }
								{ lia. }
							}
						}
						{
							apply Nat.eqb_neq in Hproc_p_neq. rewrite Hproc_p_neq. apply IHn_hyp.
						}
					}
				}
			}
		}
		Qed.

Ltac seq_proc proc p Hcomp Hseq H0_proc :=
	(* form process matching hypotheses *)
	unfold seq in Hseq; destruct Hseq as [Hproc_match _];
	rewrite Hcomp in H0_proc; unfold event_process in H0_proc; simpl in H0_proc; symmetry in H0_proc;
	rewrite Hcomp in Hproc_match; unfold event_process in Hproc_match; simpl in Hproc_match; symmetry in Hproc_match;
	assert (proc = p) as Hproc_p by apply (eq_trans Hproc_match H0_proc);
	apply Nat.eqb_eq in H0_proc; symmetry in Hproc_match; apply Nat.eqb_eq in Hproc_match; apply Nat.eqb_eq in Hproc_p.

Ltac seq_simpl_nrec_nrec Hproc_match H0_proc Hproc_p :=
	(* unfold run_computation calculation *)
	unfold run_computation; unfold fold_left; unfold step; simpl; simpl_step;
	simpl; rewrite Nat.eqb_refl; rewrite Hproc_match; rewrite Hproc_match; rewrite H0_proc; rewrite Nat.eqb_refl; rewrite Hproc_p; lia.

Ltac seq_simpl_rec_nrec Hproc_match H0_proc Hproc_p :=
	(* unfold run_computation calculation *)
	unfold run_computation; unfold fold_left; unfold step; simpl; simpl_step;
	simpl; rewrite Nat.eqb_refl; rewrite H0_proc; rewrite orb_true_l; rewrite Nat.eqb_refl;
	rewrite Hproc_p; rewrite Hproc_match; rewrite Hproc_match; rewrite orb_true_l; lia.

Ltac seq_simpl_nrec_rec send_event_num Hcomp Hproc_match H0_proc Hproc_p Hsender_prec :=
	(* unfold run_computation calculation *)
	assert (send_event_num < 1) as Hsen by 
		(rewrite Hcomp in Hsender_prec;
		unfold sender_prec in Hsender_prec;
		apply (Hsender_prec 1));
	apply Nat.lt_1_r in Hsen;
	unfold run_computation; unfold fold_left; unfold step; simpl; simpl_step;
	simpl; rewrite Nat.eqb_refl; rewrite H0_proc; rewrite Nat.eqb_refl; rewrite Hsen; rewrite Hproc_match; rewrite Hproc_p; rewrite H0_proc; simpl; lia.

Lemma seq_timestamps_base:
	forall (comp : computation) (e f : event) (p : process),
	comp = e :: f :: nil ->
	p = event_process comp 0 ->
	(forall (a : event_index), sender_prec comp a) ->
	seq comp 0 1 ->
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	event_timestamps 0 p < event_timestamps 1 p.
Proof.
	intros comp e f p Hcomp H0_proc Hsender_prec Hseq. simpl. rewrite Hcomp.
	destruct f; destruct e; seq_proc proc p Hcomp Hseq H0_proc.
	seq_simpl_nrec_nrec Hproc_match H0_proc Hproc_p. seq_simpl_nrec_nrec Hproc_match H0_proc Hproc_p. seq_simpl_rec_nrec Hproc_match H0_proc Hproc_p.
	seq_simpl_nrec_nrec Hproc_match H0_proc Hproc_p. seq_simpl_nrec_nrec Hproc_match H0_proc Hproc_p. seq_simpl_rec_nrec Hproc_match H0_proc Hproc_p.
	seq_simpl_nrec_rec send_event_num Hcomp Hproc_match H0_proc Hproc_p Hsender_prec. seq_simpl_nrec_rec send_event_num Hcomp Hproc_match H0_proc Hproc_p Hsender_prec. seq_simpl_nrec_rec send_event_num Hcomp Hproc_match H0_proc Hproc_p Hsender_prec.
Qed.

Ltac seq_simpl comp' Hb_tl Hcomp' :=
	simpl; unfold update_event_time; unfold update_clock_receive; unfold update_clock; unfold update; unfold event_eqb;
	rewrite Hb_tl; rewrite (n_value comp'); rewrite Hcomp'; rewrite Nat.eqb_refl; rewrite Nat.eqb_refl.

Ltac proc_p comp' tl Ha_proc Hep_ab Hb_tl Hcomp' Hcomp :=
	rewrite <- Ha_proc in Hep_ab; unfold event_process in Hep_ab;
	rewrite Hb_tl in Hep_ab; rewrite <- Hcomp' in Hep_ab; rewrite Hcomp in Hep_ab;
	rewrite (nth_middle comp' nil tl (Event 0)) in Hep_ab; symmetry in Hep_ab.

Lemma seq_timestamps:
	forall (comp : computation) (a b : nat) (p : process),
	length comp >= 2 ->
	a < length comp ->
	b < length comp ->
	p = event_process comp a ->
	(forall (a : event_index), sender_prec comp a) ->
	seq comp a b ->
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	event_timestamps a p < event_timestamps b p.
Proof.
	intros comp. remember (length comp) as n. destruct n.
	- intros. inversion H. (* length comp = 0, not allowed *)
	- destruct n.
		+ intros. unfold ge in H. apply le_S_n in H. inversion H. (* length comp = 1, not allowed *)
		+ generalize dependent comp.
			induction n. {
				(* induction base case: comp = e :: f :: nil *)

				(* setup comp = e :: f :: nil *)
				intros comp Hlen a b p Hlen_bound Ha_bound Hb_bound Ha_proc Hsender_prec Hseq. simpl.
				apply (comp_ef comp) in Hlen as Hef.

				(* destruct e and f and apply base case lemma *)
				destruct Hef as [e He]. {
					destruct He as [f Hcomp]. {
						assert (a < b) as Hab. {
							unfold seq in Hseq. destruct Hseq as [_ Hab_lt]. apply Hab_lt.
						}
						assert (a = 0) as Ha. { lia. }
						assert (b = 1) as Hb. { lia. }
						rewrite Ha. rewrite Hb.
						rewrite Ha in Ha_proc. rewrite Ha in Hseq. rewrite Hb in Hseq.

						apply (seq_timestamps_base comp e f p Hcomp Ha_proc Hsender_prec Hseq).
					}
				}
			}
			{
				(* inductive step *)

				intros comp Hlen a b p Hlen_bound Ha_bound Hb_bound Ha_proc Hsender_prec Hseq. simpl.
				(* setup comp = comp' ++ tl :: nil for some comp', tl *)

				destruct (list_tl comp) as [comp' Hcomp']. {
					symmetry in Hlen. rewrite Hlen. lia.
				}
				{
					destruct Hcomp' as [tl Hcomp]. {

						(* setup useful hypotheses *)
						inversion Hseq as [Hep_ab Hab_bound].
						pose proof (comp'_len comp comp' tl Hcomp) as Hcomp'.
						assert (a < length comp') as Ha_bound_comp'. { rewrite Hcomp'. lia. }

						assert (b = length comp - 1 \/ ~(b = length comp - 1)) as Hb. { apply classic. }
						destruct Hb as [Hb_tl | Hb_IH]. {
							(* b is last element *)

							(* event_timestamps a p <= (final_clocks comp') p p *)
							assert (
								snd (run_computation comp init_state) a p <=
								snd (fst (run_computation comp' init_state)) p p
							) as Htrans1. {
								rewrite Hcomp.
								rewrite <- (preserve_ets comp' tl a). {
									apply (final_clocks comp' a p Ha_bound_comp').
									{ rewrite (preserve_proc comp' tl a). rewrite Hcomp in Ha_proc. apply Ha_proc. apply Ha_bound_comp'. }
								}
								{ apply Ha_bound_comp'. }
							}

							(* (final_clocks comp') p p < event_timestamps b p *)
							assert (
								snd (fst (run_computation comp' init_state)) p p <
								snd (run_computation comp init_state) b p
							) as Htrans2. {
								rewrite Hcomp. rewrite (comp_step comp' tl).
								unfold step.

								(* manual case work on tl using seq_simpl and proc_p Ltacs defined above *)
								destruct tl. {
									seq_simpl comp' Hb_tl Hcomp'.
									proc_p comp' (Event proc) Ha_proc Hep_ab Hb_tl Hcomp' Hcomp.

									rewrite Hep_ab. apply Nat.eqb_eq in Hep_ab. rewrite Nat.eqb_refl. lia.
								}
								{
									seq_simpl comp' Hb_tl Hcomp'.
									proc_p comp' (Event_send proc) Ha_proc Hep_ab Hb_tl Hcomp' Hcomp.

									rewrite Hep_ab. apply Nat.eqb_eq in Hep_ab. rewrite Nat.eqb_refl. lia.
								}
								{
									seq_simpl comp' Hb_tl Hcomp'.
									proc_p comp' (Event_receive proc send_event_proc send_event_num) Ha_proc Hep_ab Hb_tl Hcomp' Hcomp.

									rewrite Hep_ab. apply Nat.eqb_eq in Hep_ab. rewrite Nat.eqb_refl. rewrite orb_true_l.
									destruct (
										snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) p p
									) eqn:Hmax. { lia. }
									{ apply Nat.ltb_ge in Hmax. lia. }
								}
							}

							apply (Nat.le_lt_trans 
								(snd (run_computation comp init_state) a p)
								(snd (fst (run_computation comp' init_state)) p p)
								(snd (run_computation comp init_state) b p)
								Htrans1 Htrans2).
						}
						{
							(* b is not last element *)

							(* use IH *)
							rewrite Hcomp.
							rewrite <- (preserve_ets comp' tl a). {
								rewrite <- (preserve_ets comp' tl b). {
									apply (IHn comp').
									{ lia. }
									{ lia. }
									{ lia. }
									{ lia. }
									{ rewrite Hcomp in Ha_proc. rewrite (preserve_proc comp' tl a). apply Ha_proc.
										{ apply Ha_bound_comp'. } }
									{ apply (preserve_sender_prec comp comp' tl Hcomp). apply Hsender_prec. }
									{ apply (preserve_seq comp comp' tl a b).
										{ lia. }
										{ lia. }
										{ apply Hcomp. }
										{ apply Hseq. }
									}
								}
								{ lia. }
							}
							{ lia. }
						}
					}
				}
			}
Qed.

Ltac simpl_final_clocks2 comp comp' tl proc p Ha_proc Hcomp Ha :=
	unfold event_process in Ha_proc; rewrite Hcomp in Ha_proc; rewrite Ha in Ha_proc; rewrite (nth_middle comp' nil tl (Event 0)) in Ha_proc;
	rewrite Hcomp; rewrite (comp_step comp' tl); unfold step; simpl; simpl_step;
	rewrite (n_value comp'); rewrite Ha; rewrite Nat.eqb_refl; rewrite Nat.eqb_refl.

Ltac simpl_proc_p proc p Ha_proc :=
	destruct (proc =? p) eqn:Hproc_p; rewrite Ha_proc; rewrite Nat.eqb_refl; rewrite Hproc_p; lia.

Lemma final_clocks2:
	forall (comp : computation) (a : nat) (p q : process),
	a < length comp ->
	q = event_process comp a ->
	snd (run_computation comp init_state) a p <=
	snd (fst (run_computation comp init_state)) q p.
Proof.
	intros comp. remember (length comp) as n. generalize dependent comp.
	induction n.
	- intros. inversion H.
	- intros comp Hlen a p q Ha_bound Ha_proc.
		destruct (list_tl comp) as [comp' Hcomp']. {
			symmetry in Hlen. rewrite Hlen. lia.
		}
		{
			destruct Hcomp' as [tl Hcomp]. {
				pose proof (comp'_len comp comp' tl Hcomp) as Hcomp'.
				assert (a = length comp' \/ ~(a = length comp')) as Ha. { apply classic. }
				destruct Ha as [Ha | Ha_neq]. {
					(* a is end of list *)
					destruct tl.
					{ simpl_final_clocks2 comp comp' (Event proc) p proc Ha_proc Hcomp Ha; simpl_proc_p proc p Ha_proc. }
					{ simpl_final_clocks2 comp comp' (Event_send proc) p proc Ha_proc Hcomp Ha; simpl_proc_p proc p Ha_proc. }
					{ simpl_final_clocks2 comp comp' (Event_receive proc send_event_proc send_event_num) p proc Ha_proc Hcomp Ha; simpl_proc_p proc p Ha_proc. }
				}
				{
					assert (a < length comp') as Ha_bound'. { lia. }
					rewrite Hcomp. rewrite <- (preserve_ets comp' tl a Ha_bound').

					destruct tl. {
						assert (
							snd (run_computation comp' init_state) a p <=
							snd (fst (run_computation comp' init_state)) q p
						) as IHn_hyp. {
							apply (IHn comp'). 
							{ lia. }
							{ lia. }
							{ rewrite Hcomp in Ha_proc. rewrite <- (preserve_proc comp' (Event proc) a) in Ha_proc. apply Ha_proc. { apply Ha_bound'. } }
						}

						apply (Nat.le_trans
							(snd (run_computation comp' init_state) a p)
							(snd (fst (run_computation comp' init_state)) q p)
							(snd (fst (run_computation (comp' ++ (Event proc) :: nil) init_state)) q p)).
						{ apply IHn_hyp. }
						{
							rewrite (comp_step comp' (Event proc)). unfold step. apply Nat.eqb_neq in Ha_neq. simpl. simpl_step.
							destruct (proc =? q) eqn:Hproc_q. {
								destruct (proc =? p) eqn:Hproc_p. {
									apply Nat.eqb_eq in Hproc_q. rewrite <- Hproc_q.
									apply Nat.eqb_eq in Hproc_p. rewrite Hproc_p. lia.
								}
								{
									apply Nat.eqb_eq in Hproc_q. rewrite <- Hproc_q. lia.
								}
							}
							{
								lia.
							}
						}
					}
					{
						assert (
							snd (run_computation comp' init_state) a p <=
							snd (fst (run_computation comp' init_state)) q p
						) as IHn_hyp. {
							apply (IHn comp'). 
							{ lia. }
							{ lia. }
							{ rewrite Hcomp in Ha_proc. rewrite <- (preserve_proc comp' (Event_send proc) a) in Ha_proc. apply Ha_proc. { apply Ha_bound'. } }
						}

						apply (Nat.le_trans
							(snd (run_computation comp' init_state) a p)
							(snd (fst (run_computation comp' init_state)) q p)
							(snd (fst (run_computation (comp' ++ (Event_send proc) :: nil) init_state)) q p)).
						{ apply IHn_hyp. }
						{
							rewrite (comp_step comp' (Event_send proc)). unfold step. apply Nat.eqb_neq in Ha_neq. simpl. simpl_step.
							destruct (proc =? q) eqn:Hproc_q. {
								destruct (proc =? p) eqn:Hproc_p. {
									apply Nat.eqb_eq in Hproc_q. rewrite <- Hproc_q.
									apply Nat.eqb_eq in Hproc_p. rewrite Hproc_p. lia.
								}
								{
									apply Nat.eqb_eq in Hproc_q. rewrite <- Hproc_q. lia.
								}
							}
							{
								lia.
							}
						}
					}
					{
						assert (
							snd (run_computation comp' init_state) a p <=
							snd (fst (run_computation comp' init_state)) q p
						) as IHn_hyp. {
							apply (IHn comp'). 
							{ lia. }
							{ lia. }
							{ rewrite Hcomp in Ha_proc. rewrite <- (preserve_proc comp' (Event_receive proc send_event_proc send_event_num) a) in Ha_proc. apply Ha_proc. { apply Ha_bound'. } }
						}

						apply (Nat.le_trans
							(snd (run_computation comp' init_state) a p)
							(snd (fst (run_computation comp' init_state)) q p)
							(snd (fst (run_computation (comp' ++ (Event_receive proc send_event_proc send_event_num) :: nil) init_state)) q p)).
						{ apply IHn_hyp. }
						{
							rewrite (comp_step comp' (Event_receive proc send_event_proc send_event_num)). unfold step. apply Nat.eqb_neq in Ha_neq. simpl. simpl_step.
							destruct (proc =? q) eqn:Hproc_q. {
								destruct (proc =? p) eqn:Hproc_p. {
									rewrite orb_true_l.
									destruct (
										snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) proc p
									) eqn:Hmax. {
										apply Nat.eqb_eq in Hproc_q. rewrite <- Hproc_q.
										apply Nat.eqb_eq in Hproc_p. rewrite Hproc_p. lia.
									}
									{
										apply Nat.ltb_nlt in Hmax. apply Nat.nlt_ge in Hmax.
										apply Nat.eqb_eq in Hproc_q. rewrite <- Hproc_q.
										apply (Nat.le_trans
											(snd (fst (run_computation comp' init_state)) proc p)
											(snd (run_computation comp' init_state) send_event_num p)
											(snd (run_computation comp' init_state) send_event_num p + 1)).
										{ apply Hmax. }
										{ lia. }
									}
								}
								{
									destruct (
										snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) proc p
									) eqn:Hmax. {
										apply Nat.eqb_eq in Hproc_q. rewrite <- Hproc_q. lia.
									}
									{
										destruct (send_event_proc =? p). {
											rewrite orb_true_r. apply Nat.ltb_nlt in Hmax. apply Nat.nlt_ge in Hmax.
											apply Nat.eqb_eq in Hproc_q. rewrite <- Hproc_q.
											apply (Nat.le_trans
												(snd (fst (run_computation comp' init_state)) proc p)
												(snd (run_computation comp' init_state) send_event_num p)
												(snd (run_computation comp' init_state) send_event_num p + 1)).
											{ apply Hmax. }
											{ lia. }
										}
										{
											simpl. apply Nat.ltb_nlt in Hmax. apply Nat.nlt_ge in Hmax.
											apply Nat.eqb_eq in Hproc_q. rewrite <- Hproc_q. apply Hmax.
										}
									}
								}
							}
							{
								lia.
							}
						}
					}
				}
			}
		}
		Qed.

Ltac seq_simpl2 proc p Hseq Hcomp :=
	unfold seq in Hseq; rewrite Hcomp in Hseq; unfold event_process in Hseq; simpl in Hseq; destruct Hseq as [Hproc0_proc _];
	unfold run_computation; unfold fold_left; unfold step; simpl; simpl_step;
	simpl; rewrite Nat.eqb_refl; rewrite Hproc0_proc; destruct (proc =? p) eqn:Hproc_p.

Lemma seq_timestamps_base2:
	forall (comp : computation) (e f : event) (p : process),
	comp = e :: f :: nil ->
	(forall (a : event_index), sender_prec comp a) ->
	seq comp 0 1 ->
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	event_timestamps 0 p <= event_timestamps 1 p.
Proof.
	intros comp e f p Hcomp Hsender_prec Hseq. simpl. rewrite Hcomp.
	destruct f; destruct e.
	- seq_simpl2 proc p Hseq Hcomp. { rewrite Nat.eqb_refl. rewrite Hproc_p. lia. } { rewrite Nat.eqb_refl. rewrite Hproc_p. lia. }
	- seq_simpl2 proc p Hseq Hcomp. { rewrite Nat.eqb_refl. rewrite Hproc_p. lia. } { rewrite Nat.eqb_refl. rewrite Hproc_p. lia. }
	- seq_simpl2 proc p Hseq Hcomp. { rewrite Nat.eqb_refl. rewrite Hproc_p. rewrite orb_true_l. lia. } { rewrite Nat.eqb_refl. rewrite Hproc_p. destruct (send_event_proc =? p) eqn:Hsep_p; lia. }
	- seq_simpl2 proc p Hseq Hcomp. { rewrite Nat.eqb_refl. rewrite Hproc_p. lia. } { rewrite Nat.eqb_refl. rewrite Hproc_p. lia. }
	- seq_simpl2 proc p Hseq Hcomp. { rewrite Nat.eqb_refl. rewrite Hproc_p. lia. } { rewrite Nat.eqb_refl. rewrite Hproc_p. lia. }
	- seq_simpl2 proc p Hseq Hcomp. { rewrite Nat.eqb_refl. rewrite Hproc_p. rewrite orb_true_l. lia. } { rewrite Nat.eqb_refl. rewrite Hproc_p. destruct (send_event_proc =? p) eqn:Hsep_p; lia. }
	- seq_simpl2 proc p Hseq Hcomp. { 
			rewrite Nat.eqb_refl. rewrite Hproc_p. rewrite orb_true_l.
			destruct (send_event_num) eqn:Hsen. { rewrite Hproc_p. simpl. lia. } { simpl. lia. }
		}
		{
			rewrite Nat.eqb_refl. rewrite Hproc_p.
			destruct (send_event_num) eqn:Hsen. { rewrite Hproc_p. simpl. destruct (send_event_proc =? p); unfold init_clocks; lia. } { simpl. destruct (send_event_proc =? p); unfold init_clocks; lia. }
		}
	- seq_simpl2 proc p Hseq Hcomp. { 
			rewrite Nat.eqb_refl. rewrite Hproc_p. rewrite orb_true_l.
			destruct (send_event_num) eqn:Hsen. { rewrite Hproc_p. simpl. lia. } { simpl. lia. }
		}
		{
			rewrite Nat.eqb_refl. rewrite Hproc_p.
			destruct (send_event_num) eqn:Hsen. { rewrite Hproc_p. simpl. destruct (send_event_proc =? p); unfold init_clocks; lia. } { simpl. destruct (send_event_proc =? p); unfold init_clocks; lia. }
		}
	- seq_simpl2 proc p Hseq Hcomp. { 
			rewrite Nat.eqb_refl. rewrite Hproc_p. rewrite orb_true_l.
			destruct (send_event_num) eqn:Hsen. { rewrite Hproc_p. simpl. lia. } { simpl. lia. }
		}
		{
			rewrite Nat.eqb_refl. rewrite Hproc_p.
			destruct (send_event_num) eqn:Hsen. { 
				rewrite Hproc_p. simpl. destruct (send_event_proc =? p); unfold init_clocks; destruct (send_event_proc0 =? p). 
				{ simpl. lia. } { 
					destruct (init_timestamps send_event_num0 p <? init_timestamps send_event_num0 p). { unfold init_timestamps. lia. } { unfold init_timestamps. lia. }
				 } { simpl. lia. } { 
					destruct (init_timestamps send_event_num0 p <? init_timestamps send_event_num0 p). { unfold init_timestamps. lia. } { unfold init_timestamps. lia. }
				 } } { simpl. destruct (send_event_proc =? p); unfold init_clocks; 
				 	destruct (
						send_event_proc0 =? p
					). { unfold init_timestamps. simpl. lia. } { unfold init_timestamps. simpl. lia. }
					{ unfold init_timestamps. simpl. lia. }
					{ unfold init_timestamps. simpl. lia. }
			}
		}
		Qed.


Lemma seq_timestamps2:
	forall (comp : computation) (a b : nat) (p : process),
	length comp >= 2 ->
	a < length comp ->
	b < length comp ->
	(forall (a : event_index), sender_prec comp a) ->
	seq comp a b ->
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	event_timestamps a p <= event_timestamps b p.
Proof.
	intros comp. remember (length comp) as n. destruct n.
	- intros. inversion H. (* length comp = 0, not allowed *)
	- destruct n.
		+ intros. unfold ge in H. apply le_S_n in H. inversion H. (* length comp = 1, not allowed *)
		+ generalize dependent comp.
			induction n. {
				(* induction base case: comp = e :: f :: nil *)

				(* setup comp = e :: f :: nil *)
				intros comp Hlen a b p Hlen_bound Ha_bound Hb_bound Hsender_prec Hseq. simpl.
				apply (comp_ef comp) in Hlen as Hef.

				(* destruct e and f and apply base case lemma *)
				destruct Hef as [e He]. {
					destruct He as [f Hcomp]. {
						assert (a < b) as Hab. {
							unfold seq in Hseq. destruct Hseq as [_ Hab_lt]. apply Hab_lt.
						}
						assert (a = 0) as Ha. { lia. }
						assert (b = 1) as Hb. { lia. }
						rewrite Ha. rewrite Hb. rewrite Ha in Hseq. rewrite Hb in Hseq.

						apply (seq_timestamps_base2 comp e f p Hcomp Hsender_prec Hseq).
					}
				}
			}
			{
				(* inductive step *)

				intros comp Hlen a b p Hlen_bound Ha_bound Hb_bound Hsender_prec Hseq. simpl.
				(* setup comp = comp' ++ tl :: nil for some comp', tl *)

				destruct (list_tl comp) as [comp' Hcomp']. {
					symmetry in Hlen. rewrite Hlen. lia.
				}
				{
					destruct Hcomp' as [tl Hcomp]. {

						(* setup useful hypotheses *)
						inversion Hseq as [Hep_ab Hab_bound].
						pose proof (comp'_len comp comp' tl Hcomp) as Hcomp'.
						assert (a < length comp') as Ha_bound_comp'. { rewrite Hcomp'. lia. }

						(*rewrite Hcomp. rewrite (comp_step comp' tl (length comp')). unfold step.*)
						(*destruct tl. {
							simpl. simpl_step. rewrite (n_value comp'). Search lt eq not. apply Nat.lt_neq in Ha_bound_comp'. apply Nat.eqb_neq in Ha_bound_comp'. rewrite Nat.eqb_sym in Ha_bound_comp'. rewrite Ha_bound_comp'.
							destruct (length comp' =? b). {
								rewrite Nat.eqb_refl.
							}
						}*)

						assert (b = length comp - 1 \/ ~(b = length comp - 1)) as Hb. { apply classic. }
						destruct Hb as [Hb_tl | Hb_IH]. {
							(* b is last element *)


							(* event_timestamps a p <= (final_clocks comp') p p *)
							assert (
								snd (run_computation comp init_state) a p <=
								snd (fst (run_computation comp' init_state)) (event_process comp' a) p
							) as Htrans1. {
								rewrite Hcomp.
								rewrite <- (preserve_ets comp' tl a). {
									apply (final_clocks2 comp' a p (event_process comp' a) Ha_bound_comp').
									{ reflexivity. }
									(*{ rewrite (preserve_proc comp' tl a). rewrite Hcomp in Ha_proc. apply Ha_proc. apply Ha_bound_comp'. }*)
								}
								{ apply Ha_bound_comp'. }
							}

							(* (final_clocks comp') p p < event_timestamps b p *)
							assert (
								snd (fst (run_computation comp' init_state)) (event_process comp' a) p <=
								snd (run_computation comp init_state) b p
							) as Htrans2. {
								rewrite Hcomp. rewrite (comp_step comp' tl).
								unfold step.

								(* manual case work on tl using seq_simpl and proc_p Ltacs defined above *)
								remember (event_process comp b) as p_b. unfold event_process in Heqp_b. rewrite <- Hcomp' in Hb_tl. rewrite Hb_tl in Heqp_b.
								rewrite Hcomp in Heqp_b. rewrite (nth_middle comp' nil tl (Event 0)) in Heqp_b.
								rewrite Hcomp in Hep_ab. rewrite <- (preserve_proc comp' tl a) in Hep_ab.
								destruct tl. {
									seq_simpl comp' Hb_tl Hcomp'.
									rewrite Hep_ab. rewrite Heqp_b.
									destruct (proc =? p) eqn:Hproc_p. 
									{ apply Nat.eqb_eq in Hproc_p. rewrite Hproc_p. lia. }
									{ lia. }
								}
								{
									seq_simpl comp' Hb_tl Hcomp'.
									rewrite Hep_ab. rewrite Heqp_b.
									destruct (proc =? p) eqn:Hproc_p. 
									{ apply Nat.eqb_eq in Hproc_p. rewrite Hproc_p. lia. }
									{ lia. }
								}
								{
									seq_simpl comp' Hb_tl Hcomp'.
									rewrite Hep_ab. rewrite Heqp_b.
									destruct (proc =? p) eqn:Hproc_p. 
									{
										apply Nat.eqb_eq in Hproc_p. rewrite Hproc_p.
										destruct (snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) p p) eqn:Hmax. {
											lia.
										}
										{
											rewrite orb_true_l. apply Nat.ltb_nlt in Hmax. apply Nat.nlt_ge in Hmax.
											apply (Nat.le_trans
												(snd (fst (run_computation comp' init_state)) p p)
												(snd (run_computation comp' init_state) send_event_num p)
												(snd (run_computation comp' init_state) send_event_num p + 1)).
											{ apply Hmax. }
											{ lia. }
										}
									}
									{
										destruct (snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) proc p) eqn:Hmax. {
											lia.
										}
										{
											apply Nat.ltb_nlt in Hmax. apply Nat.nlt_ge in Hmax.
											destruct (send_event_proc =? p) eqn:Hsep_p. {
												simpl.
												apply (Nat.le_trans
													(snd (fst (run_computation comp' init_state)) proc p)
													(snd (run_computation comp' init_state) send_event_num p)
													(snd (run_computation comp' init_state) send_event_num p + 1)).
												{ apply Hmax. }
												{ lia. }
											}
											{ simpl. apply Hmax. }
										}
									}
								}
								{ apply Ha_bound_comp'. }
							}

							apply (Nat.le_trans
								(snd (run_computation comp init_state) a p)
								(snd (fst (run_computation comp' init_state)) (event_process comp' a) p)
								(snd (run_computation comp init_state) b p)
								Htrans1 Htrans2).
						}
						{
							(* b is not last element *)
							rewrite Hcomp.
							rewrite <- (preserve_ets comp' tl a). {
								rewrite <- (preserve_ets comp' tl b). {
									apply (IHn comp').
									{ lia. }
									{ lia. }
									{ lia. }
									{ lia. }
									{ apply (preserve_sender_prec comp comp' tl Hcomp). apply Hsender_prec. }
									{ apply (preserve_seq comp comp' tl a b).
										{ lia. }
										{ lia. }
										{ apply Hcomp. }
										{ apply Hseq. }
									}
								}
								{ lia. }
							}
							{ lia. }
						}
					}
				}
			}
		Qed.

Ltac msg_simpl proc0 proc Hmsg Hsen He_proc H0_proc Hcomp :=
	simpl in Hmsg; destruct Hmsg as [Hsen He_proc]; rewrite <- Hsen in He_proc; unfold event_process in He_proc; simpl in He_proc;
	unfold event_process in H0_proc; rewrite Hcomp in H0_proc; simpl in H0_proc; symmetry in H0_proc;

	simpl; simpl_step; simpl; rewrite Nat.eqb_refl;
	rewrite H0_proc; rewrite <- Hsen; rewrite Nat.eqb_refl; rewrite Nat.eqb_refl; rewrite Nat.eqb_refl;
	assert (proc0 = proc \/ ~(proc0 = proc)) as Hproc0_proc by ( apply classic );
	destruct Hproc0_proc as [Hproc0_proc | Hproc0_proc_neq].

Ltac msg_simpl_sp Hproc0_proc H0_proc :=
	rewrite <- Hproc0_proc; rewrite <- H0_proc; rewrite Nat.eqb_refl; rewrite Nat.eqb_refl; simpl; lia.

Ltac msg_simpl_dp Hproc0_proc_neq H0_proc He_proc :=
	apply Nat.eqb_neq in Hproc0_proc_neq; rewrite <- H0_proc; rewrite Hproc0_proc_neq; simpl;
	rewrite He_proc; rewrite Nat.eqb_refl; rewrite orb_true_r; lia.

Lemma msg_base:
	forall (comp : computation) (e f : event) (p : process),
	comp = e :: f :: nil ->
	p = event_process comp 0 ->
	msg comp 0 1 ->
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	event_timestamps 0 p < event_timestamps 1 p.
Proof.
	intros comp e f p Hcomp H0_proc Hmsg. simpl. rewrite Hcomp.
	unfold msg in Hmsg. rewrite Hcomp in Hmsg. simpl in Hmsg.
	destruct f.
	- inversion Hmsg.
	- inversion Hmsg.
	- destruct e.
		+ msg_simpl proc0 proc Hmsg Hsen He_proc H0_proc Hcomp.
			msg_simpl_sp Hproc0_proc H0_proc. msg_simpl_dp Hproc0_proc_neq H0_proc He_proc.
		+ msg_simpl proc0 proc Hmsg Hsen He_proc H0_proc Hcomp.
			msg_simpl_sp Hproc0_proc H0_proc. msg_simpl_dp Hproc0_proc_neq H0_proc He_proc.
		+ msg_simpl proc0 proc Hmsg Hsen He_proc H0_proc Hcomp.
			msg_simpl_sp Hproc0_proc H0_proc. msg_simpl_dp Hproc0_proc_neq H0_proc He_proc.
Qed.

Lemma msg_timestamps:
	forall (comp : computation) (a b : nat) (p : process),
	length comp >= 2 ->
	a < length comp ->
	b < length comp ->
	p = event_process comp a ->
	(forall (a : event_index), sender_prec comp a) ->
	msg comp a b ->
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	event_timestamps a p < event_timestamps b p.
Proof.
	intros comp. remember (length comp) as n. destruct n.
	- intros. inversion H. (* length comp = 0, not allowed *)
	- destruct n.
		+ intros. unfold ge in H. apply le_S_n in H. inversion H. (* length comp = 1, not allowed *)
		+ generalize dependent comp.
			induction n. {
				(* induction base case: comp = e :: f :: nil - inversion on impossible cases *)

				destruct a eqn:Ha. {
					destruct b. {
						(* a = 0, b = 0 - impossible *)
						intros p Hlen Ha_bound Hb_bound H0_proc Hsender_prec Hmsg. simpl.

						unfold msg in Hmsg.
						destruct (nth 0 comp (Event 0)) eqn:H0.
						{ inversion Hmsg. }
						{ inversion Hmsg. }
						{ specialize (Hsender_prec 0). unfold sender_prec in Hsender_prec. rewrite H0 in Hsender_prec. inversion Hsender_prec. }
					}
					{
						destruct b eqn:Hb. {
							(* a = 0, b = 1 - comp = e :: f :: nil -> induction base case *)

							intros p Hlen Ha_bound Hb_bound H0_proc Hsender_prec Hmsg. simpl.
							apply (comp_ef comp) in Heqn as Hef.

							(* destruct e and f and apply base case lemma *)
							destruct Hef as [e He]. destruct He as [f Hcomp]. apply (msg_base comp e f p Hcomp H0_proc Hmsg).
						}
						{
							(* a = 0, b > 1 - impossible for length comp = 2 *)
							intros. apply Nat.succ_lt_mono in H1. apply Nat.succ_lt_mono in H1. inversion H1.
						}
					}
				}
				{
					intros b p Hlen Ha_bound Hb_bound H0_proc Hsender_prec Hmsg. simpl.
					unfold msg in Hmsg.
					destruct (nth b comp (Event 0)) eqn:H0.
					{ inversion Hmsg. }
					{ inversion Hmsg. }
					{
						unfold sender_prec in Hsender_prec. specialize (Hsender_prec b). rewrite H0 in Hsender_prec.
						destruct Hmsg as [Hsen Hep]. rewrite <- Hsen in Hsender_prec. unfold lt in Hsender_prec.
						assert (S (S n) < 2) as Hcontra. { apply (Nat.le_lt_trans (S (S n)) b 2 Hsender_prec Hb_bound). }
						apply Nat.succ_lt_mono in Hcontra. apply Nat.succ_lt_mono in Hcontra. inversion Hcontra.
					}
				}
			}
			{
				(* inductive step *)

				intros comp Hlen a b p Hlen_bound Ha_bound Hb_bound Ha_proc Hsender_prec Hmsg. simpl.
				destruct (list_tl comp) as [comp' Hcomp']. {
					symmetry in Hlen. rewrite Hlen. lia.
				}
				{
					destruct Hcomp' as [tl Hcomp]. {

						pose proof (comp'_len comp comp' tl Hcomp) as Hcomp'.
						assert (a < b) as Hab_bound. {
							unfold msg in Hmsg.
							destruct (nth b comp (Event 0)) eqn:Hnth_b.
							{ inversion Hmsg. }
							{ inversion Hmsg. }
							{ destruct Hmsg as [Ha_sen Hep]. specialize (Hsender_prec b). unfold sender_prec in Hsender_prec. rewrite Hnth_b in Hsender_prec. rewrite <- Ha_sen in Hsender_prec. apply Hsender_prec. }
						}

						assert (b = length comp - 1 \/ ~(b = length comp - 1)) as Hb. { apply classic. }
						destruct Hb as [Hb_tl | Hb_IH]. {
							(* b is last element, prove manually *)

							unfold msg in Hmsg.
							destruct (nth b comp (Event 0)) eqn:Hnth_b.
							{ inversion Hmsg. }
							{ inversion Hmsg. }
							{
								(* setup useful hypotheses *)
								assert (tl = nth b comp (Event 0)) as Htl. {
									rewrite <- Hb_tl in Hcomp'. rewrite <- Hcomp'. rewrite Hcomp.
									rewrite (nth_middle comp' nil tl (Event 0)). reflexivity.
								}
								assert ((fst (fst (run_computation comp' init_state)) =? a) = false) as Ha_nvalue. {
									rewrite (n_value comp'). rewrite <- Hcomp' in Hb_tl. rewrite <- Hb_tl.
									apply Nat.eqb_neq. unfold not. intros. rewrite H in Hab_bound. apply Nat.lt_irrefl in Hab_bound. inversion Hab_bound.
								}
								destruct Hmsg as [Ha_sen Hep]. rewrite <- Ha_sen in Hep. rewrite <- Ha_proc in Hep.

								(* do manually unfold last step calculation for tl *)
								rewrite Hcomp. rewrite (comp_step comp' tl). unfold step. rewrite Htl. rewrite Hnth_b. simpl. simpl_step.
								rewrite Ha_nvalue. rewrite (n_value comp'). rewrite <- Hcomp' in Hb_tl. rewrite Hb_tl. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.

								(* case work on if statement branches - they all supported the inequality *)
								destruct (
									snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) proc p
								) eqn:Hmax. {
									destruct (proc =? p). {
										apply Nat.ltb_lt in Hmax. rewrite <- Ha_sen in Hmax.
										apply (Nat.lt_trans
											(snd (run_computation comp' init_state) a p)
											(snd (fst (run_computation comp' init_state)) proc p)
											(snd (fst (run_computation comp' init_state)) proc p + 1)
										) in Hmax. apply Hmax.
										{ lia. }
									}
									{
										rewrite <- Ha_sen in Hmax. apply Nat.ltb_lt in Hmax. apply Hmax.
									}
								}
								{
									rewrite <- Hep. rewrite Nat.eqb_refl. rewrite orb_true_r. rewrite Ha_sen. lia.
								}
							}
						}
						{
							(* b is not last element, use IH *)

							(* use IH *)
							rewrite Hcomp.
							rewrite <- (preserve_ets comp' tl a). {
								rewrite <- (preserve_ets comp' tl b). {
									apply (IHn comp').
									{ lia. }
									{ lia. }
									{ lia. }
									{ lia. }
									{ rewrite Hcomp in Ha_proc. rewrite (preserve_proc comp' tl a). apply Ha_proc.
										{ lia. } }
									{ apply (preserve_sender_prec comp comp' tl Hcomp). apply Hsender_prec. }
									{ apply (preserve_msg comp comp' tl a b).
										{ lia. }
										{ lia. }
										{ apply Hcomp. }
										{ apply Hmsg. }
									}
								}
								{ lia. }
							}
							{ lia. }
						}
					}
				}
			}
			Qed.

Lemma msg_base2:
	forall (comp : computation) (e f : event) (p : process),
	comp = e :: f :: nil ->
	msg comp 0 1 ->
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	event_timestamps 0 p <= event_timestamps 1 p.
Proof.
	intros comp e f p Hcomp Hmsg. simpl. rewrite Hcomp.
	unfold msg in Hmsg. rewrite Hcomp in Hmsg. simpl in Hmsg.
	destruct f.
	- inversion Hmsg.
	- inversion Hmsg.
	- destruct e.
		+ destruct Hmsg as [Hsen He_proc]. rewrite <- Hsen in He_proc. unfold event_process in He_proc. simpl in He_proc.
			unfold run_computation; unfold fold_left; unfold step; simpl; simpl_step;
			simpl; rewrite Nat.eqb_refl; rewrite Nat.eqb_refl; rewrite <- Hsen.

			destruct (proc0 =? p) eqn:Hproc0_p. {
				destruct (proc0 =? proc) eqn:Hproc0_proc. {
					rewrite Hproc0_p. apply Nat.eqb_eq in Hproc0_proc. rewrite <- Hproc0_proc. rewrite Hproc0_p. simpl. lia.
				}
				{
					apply Nat.eqb_eq in Hproc0_p. rewrite <- Hproc0_p. rewrite Nat.eqb_sym in Hproc0_proc. rewrite Hproc0_proc. rewrite <- He_proc. rewrite Nat.eqb_refl. simpl. lia.
				}
			}
			{
				destruct (proc0 =? proc) eqn:Hproc0_proc. {
					rewrite Hproc0_p. apply Nat.eqb_eq in Hproc0_proc. rewrite <- Hproc0_proc. rewrite Hproc0_p. simpl. rewrite <- He_proc. rewrite Hproc0_p. lia.
				}
				{
					unfold init_clocks. simpl. rewrite <- He_proc. rewrite Hproc0_p.
					destruct (proc =? p); simpl; lia.
				}
			}
		+ destruct Hmsg as [Hsen He_proc]. rewrite <- Hsen in He_proc. unfold event_process in He_proc. simpl in He_proc.
			unfold run_computation; unfold fold_left; unfold step; simpl; simpl_step;
			simpl; rewrite Nat.eqb_refl; rewrite Nat.eqb_refl; rewrite <- Hsen.

			destruct (proc0 =? p) eqn:Hproc0_p. {
				destruct (proc0 =? proc) eqn:Hproc0_proc. {
					rewrite Hproc0_p. apply Nat.eqb_eq in Hproc0_proc. rewrite <- Hproc0_proc. rewrite Hproc0_p. simpl. lia.
				}
				{
					apply Nat.eqb_eq in Hproc0_p. rewrite <- Hproc0_p. rewrite Nat.eqb_sym in Hproc0_proc. rewrite Hproc0_proc. rewrite <- He_proc. rewrite Nat.eqb_refl. simpl. lia.
				}
			}
			{
				destruct (proc0 =? proc) eqn:Hproc0_proc. {
					rewrite Hproc0_p. apply Nat.eqb_eq in Hproc0_proc. rewrite <- Hproc0_proc. rewrite Hproc0_p. simpl. rewrite <- He_proc. rewrite Hproc0_p. lia.
				}
				{
					unfold init_clocks. simpl. rewrite <- He_proc. rewrite Hproc0_p.
					destruct (proc =? p); simpl; lia.
				}
			}
		+ destruct Hmsg as [Hsen He_proc]. rewrite <- Hsen in He_proc. unfold event_process in He_proc. simpl in He_proc.
			unfold run_computation; unfold fold_left; unfold step; simpl; simpl_step;
			simpl; rewrite Nat.eqb_refl; rewrite Nat.eqb_refl; rewrite <- Hsen.

			destruct (proc0 =? p) eqn:Hproc0_p. {
				destruct (proc0 =? proc) eqn:Hproc0_proc. {
					rewrite Hproc0_p. apply Nat.eqb_eq in Hproc0_proc. rewrite <- Hproc0_proc. rewrite Hproc0_p. simpl. lia.
				}
				{
					apply Nat.eqb_eq in Hproc0_p. rewrite <- Hproc0_p. rewrite Nat.eqb_sym in Hproc0_proc. rewrite Hproc0_proc. rewrite <- He_proc. rewrite Nat.eqb_refl. simpl. lia.
				}
			}
			{
				destruct (proc0 =? proc) eqn:Hproc0_proc. {
					rewrite Hproc0_p. apply Nat.eqb_eq in Hproc0_proc. rewrite <- Hproc0_proc. rewrite Hproc0_p. simpl. rewrite <- He_proc. rewrite Hproc0_p.
					destruct (send_event_proc0 =? p).
					{ simpl. lia. }
					{ unfold init_timestamps. simpl. lia. }
				}
				{
					destruct (send_event_proc0 =? p).
					{ simpl. destruct ((proc =? p) || (send_event_proc =? p)); lia. }
					{ unfold init_timestamps. simpl. lia. }
				}
			}
Qed.

Lemma msg_timestamps2:
	forall (comp : computation) (a b : nat) (p : process),
	length comp >= 2 ->
	a < length comp ->
	b < length comp ->
	(forall (a : event_index), sender_prec comp a) ->
	msg comp a b ->
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	event_timestamps a p <= event_timestamps b p.
Proof.
	intros comp. remember (length comp) as n. destruct n.
	- intros. inversion H. (* length comp = 0, not allowed *)
	- destruct n.
		+ intros. unfold ge in H. apply le_S_n in H. inversion H. (* length comp = 1, not allowed *)
		+ generalize dependent comp.
			induction n. {
				(* induction base case: comp = e :: f :: nil - inversion on impossible cases *)

				destruct a eqn:Ha. {
					destruct b. {
						(* a = 0, b = 0 - impossible *)
						intros p Hlen Ha_bound Hb_bound Hsender_prec Hmsg. simpl.

						unfold msg in Hmsg.
						destruct (nth 0 comp (Event 0)) eqn:H0.
						{ inversion Hmsg. }
						{ inversion Hmsg. }
						{ specialize (Hsender_prec 0). unfold sender_prec in Hsender_prec. rewrite H0 in Hsender_prec. inversion Hsender_prec. }
					}
					{
						destruct b eqn:Hb. {
							(* a = 0, b = 1 - comp = e :: f :: nil -> induction base case *)

							intros p Hlen Ha_bound Hb_bound Hsender_prec Hmsg. simpl.
							apply (comp_ef comp) in Heqn as Hef.

							(* destruct e and f and apply base case lemma *)
							destruct Hef as [e He]. destruct He as [f Hcomp]. apply (msg_base2 comp e f p Hcomp Hmsg).
						}
						{
							(* a = 0, b > 1 - impossible for length comp = 2 *)
							intros. apply Nat.succ_lt_mono in H1. apply Nat.succ_lt_mono in H1. inversion H1.
						}
					}
				}
				{
					intros b p Hlen Ha_bound Hb_bound Hsender_prec Hmsg. simpl.
					unfold msg in Hmsg.
					destruct (nth b comp (Event 0)) eqn:H0.
					{ inversion Hmsg. }
					{ inversion Hmsg. }
					{
						unfold sender_prec in Hsender_prec. specialize (Hsender_prec b). rewrite H0 in Hsender_prec.
						destruct Hmsg as [Hsen Hep]. rewrite <- Hsen in Hsender_prec. unfold lt in Hsender_prec.
						assert (S (S n) < 2) as Hcontra. { apply (Nat.le_lt_trans (S (S n)) b 2 Hsender_prec Hb_bound). }
						apply Nat.succ_lt_mono in Hcontra. apply Nat.succ_lt_mono in Hcontra. inversion Hcontra.
					}
				}
			}
			{
				(* inductive step *)

				intros comp Hlen a b p Hlen_bound Ha_bound Hb_bound Hsender_prec Hmsg. simpl.
				destruct (list_tl comp) as [comp' Hcomp']. {
					symmetry in Hlen. rewrite Hlen. lia.
				}
				{
					destruct Hcomp' as [tl Hcomp]. {

						pose proof (comp'_len comp comp' tl Hcomp) as Hcomp'.
						assert (a < b) as Hab_bound. {
							unfold msg in Hmsg.
							destruct (nth b comp (Event 0)) eqn:Hnth_b.
							{ inversion Hmsg. }
							{ inversion Hmsg. }
							{ destruct Hmsg as [Ha_sen Hep]. specialize (Hsender_prec b). unfold sender_prec in Hsender_prec. rewrite Hnth_b in Hsender_prec. rewrite <- Ha_sen in Hsender_prec. apply Hsender_prec. }
						}

						assert (b = length comp - 1 \/ ~(b = length comp - 1)) as Hb. { apply classic. }
						destruct Hb as [Hb_tl | Hb_IH]. {
							(* b is last element, prove manually *)

							unfold msg in Hmsg.
							destruct (nth b comp (Event 0)) eqn:Hnth_b.
							{ inversion Hmsg. }
							{ inversion Hmsg. }
							{
								(* setup useful hypotheses *)
								assert (tl = nth b comp (Event 0)) as Htl. {
									rewrite <- Hb_tl in Hcomp'. rewrite <- Hcomp'. rewrite Hcomp.
									rewrite (nth_middle comp' nil tl (Event 0)). reflexivity.
								}
								assert ((fst (fst (run_computation comp' init_state)) =? a) = false) as Ha_nvalue. {
									rewrite (n_value comp'). rewrite <- Hcomp' in Hb_tl. rewrite <- Hb_tl.
									apply Nat.eqb_neq. unfold not. intros. rewrite H in Hab_bound. apply Nat.lt_irrefl in Hab_bound. inversion Hab_bound.
								}
								destruct Hmsg as [Ha_sen Hep]. rewrite <- Ha_sen in Hep.

								(* do manually unfold last step calculation for tl *)
								rewrite Hcomp. rewrite (comp_step comp' tl). unfold step. rewrite Htl. rewrite Hnth_b. simpl. simpl_step.
								rewrite Ha_nvalue. rewrite (n_value comp'). rewrite <- Hcomp' in Hb_tl. rewrite Hb_tl. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.

								(* case work on if statement branches - they all supported the inequality *)
								destruct (
									snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) proc p
								) eqn:Hmax. {
									destruct (proc =? p). {
										apply Nat.ltb_lt in Hmax. rewrite <- Ha_sen in Hmax.
										apply (Nat.lt_trans
											(snd (run_computation comp' init_state) a p)
											(snd (fst (run_computation comp' init_state)) proc p)
											(snd (fst (run_computation comp' init_state)) proc p + 1)
										) in Hmax; lia.
									}
									{
										rewrite <- Ha_sen in Hmax. apply Nat.ltb_lt in Hmax. lia.
									}
								}
								{
									rewrite <- Hep.
									destruct ((proc =? p) || (event_process comp a =? p)); rewrite <- Ha_sen; lia.
								}
							}
						}
						{
							(* b is not last element, use IH *)

							(* use IH *)
							rewrite Hcomp.
							rewrite <- (preserve_ets comp' tl a). {
								rewrite <- (preserve_ets comp' tl b). {
									apply (IHn comp').
									{ lia. }
									{ lia. }
									{ lia. }
									{ lia. }
									{ apply (preserve_sender_prec comp comp' tl Hcomp). apply Hsender_prec. }
									{ apply (preserve_msg comp comp' tl a b).
										{ lia. }
										{ lia. }
										{ apply Hcomp. }
										{ apply Hmsg. }
									}
								}
								{ lia. }
							}
							{ lia. }
						}
					}
				}
			}
			Qed.

Theorem order2:
	forall (comp : computation) (a b : event_index) (p : process),
	length comp >= 2 ->
	a < length comp ->
	b < length comp ->
	(forall i : event_index, sender_prec comp i) ->
	after2 comp a b ->
	let event_timestamps : time_stamps := 
		snd (run_computation comp init_state) in
	event_timestamps a p <= event_timestamps b p.
Proof.
	intros comp a b p Hlen_bound Ha_bound Hb_bound Hsender_prec Hafter. simpl.
	induction Hafter.
	- apply (seq_timestamps2 comp a b p Hlen_bound Ha_bound Hb_bound Hsender_prec H).
	- apply (msg_timestamps2 comp a b p Hlen_bound Ha_bound Hb_bound Hsender_prec H).
	- apply (Nat.le_trans
			(snd (run_computation comp init_state) a p)
			(snd (run_computation comp init_state) b p)
			(snd (run_computation comp init_state) c p)).
		+ apply (IHHafter1 Hlen_bound Ha_bound H Hsender_prec).
		+	apply (IHHafter2 Hlen_bound H Hb_bound Hsender_prec).
Qed.

Theorem order1:
	forall (comp : computation) (a b : event_index) (p : process),
	length comp >= 2 ->
	a < length comp ->
	b < length comp ->
	p = event_process comp a ->
	(forall i : event_index, sender_prec comp i) ->
	after comp a b ->
	let event_timestamps : time_stamps := 
		snd (run_computation comp init_state) in
	event_timestamps a p < event_timestamps b p.
Proof.
	intros comp a b p Hlen_bound Ha_bound Hb_bound Ha_proc Hsender_prec Hafter. simpl.
	induction Hafter.
	- apply (seq_timestamps comp a b p Hlen_bound Ha_bound Hb_bound Ha_proc Hsender_prec H).
	- apply (msg_timestamps comp a b p Hlen_bound Ha_bound Hb_bound Ha_proc Hsender_prec H).
	- apply (Nat.lt_le_trans
			(snd (run_computation comp init_state) a p)
			(snd (run_computation comp init_state) b p)
			(snd (run_computation comp init_state) c p)).
		+ destruct Htrans1.
			{ apply (seq_timestamps comp a b p Hlen_bound Ha_bound H Ha_proc Hsender_prec H0). }
			{ apply (msg_timestamps comp a b p Hlen_bound Ha_bound H Ha_proc Hsender_prec H0). }
		+ apply (order2 comp b c p Hlen_bound H Hb_bound Hsender_prec Htrans2).
Qed.

Inductive after_test : computation -> nat -> nat -> Prop :=
	| after_test_sp (comp : computation) (a b : nat) (H : seq comp a b) : after_test comp a b
	| after_test_dp (comp : computation) (a b : nat) (H : msg comp a b) : after_test comp a b
	| after_test_trans (comp : computation) (a b c : nat) : after_test comp a b -> after_test comp b c -> after_test comp a c.

Inductive concurrent : computation -> nat -> nat -> Prop :=
	| conc_base (comp : computation) (a b : nat) (H : ~ seq comp a b /\ ~ msg comp a b) : concurrent comp a b
	| conc_step (comp : computation) (a b c : nat) : concurrent comp a b -> concurrent comp b c -> concurrent comp a c.


Lemma empty_process:
	forall (comp : computation) (p q : process),
	~ (exists (e : nat), e < length comp /\ event_process comp e = p) ->
	let clocks_final : clocks :=
		snd (fst (run_computation comp init_state)) in
	clocks_final p q = 0.
Proof.
	intros comp. remember (length comp) as n. generalize dependent comp.
	induction n.
	-	intros. symmetry in Heqn. apply (length_zero_iff_nil comp) in Heqn.
		unfold clocks_final. rewrite Heqn. simpl. unfold init_clocks. reflexivity.
	- intros.
		unfold clocks_final.
		destruct (list_tl comp) as [comp' Hcomp']. {
			lia.
		}
		{
			destruct Hcomp' as [tl Hcomp]. {
				rewrite Hcomp. rewrite (comp_step comp' tl). {
					pose proof (comp'_len comp comp' tl Hcomp) as Hcomp'.
					unfold step. simpl_step. destruct tl. {
						simpl. assert ((proc =? p) = false) as Hproc_p. {
							apply Nat.eqb_neq. intros Hproc_p_contra.
							assert (
								exists e : nat, e < S n /\ event_process comp e = p
							) as Hcontra. {
								exists (length comp'). split. {
									lia.
								}
								{
									rewrite Hcomp. unfold event_process. rewrite (nth_middle comp' nil (Event proc) (Event 0)). apply Hproc_p_contra.
								}
							}
							apply H in Hcontra. inversion Hcontra.
						}
						rewrite Hproc_p. rewrite <- Heqn in Hcomp'. simpl in Hcomp'. rewrite Nat.sub_0_r in Hcomp'. symmetry in Hcomp'. simpl in IHn.
						apply (IHn comp' Hcomp' p q).
						intros Hcontra. destruct Hcontra as [x_contra Hcontra].
						assert (
							exists e : nat, e < S n /\ event_process comp e = p
						) as Hcontra2. {
							destruct Hcontra as [Hx_contra_bound Hx_contra_ep].
							exists x_contra. rewrite Hcomp. rewrite <- (preserve_proc comp' (Event proc) x_contra). split. {
								apply (Nat.lt_lt_succ_r x_contra n) in Hx_contra_bound. apply Hx_contra_bound.
							}
							{ apply Hx_contra_ep. }
							{ lia. }
						}
						apply H in Hcontra2. inversion Hcontra2.
					}
					(* strictly redundant === *)
					{
						simpl. assert ((proc =? p) = false) as Hproc_p. {
							apply Nat.eqb_neq. intros Hproc_p_contra.
							assert (
								exists e : nat, e < S n /\ event_process comp e = p
							) as Hcontra. {
								exists (length comp'). split. {
									lia.
								}
								{
									rewrite Hcomp. unfold event_process. rewrite (nth_middle comp' nil (Event_send proc) (Event 0)). apply Hproc_p_contra.
								}
							}
							apply H in Hcontra. inversion Hcontra.
						}
						rewrite Hproc_p. rewrite <- Heqn in Hcomp'. simpl in Hcomp'. rewrite Nat.sub_0_r in Hcomp'. symmetry in Hcomp'. simpl in IHn.
						apply (IHn comp' Hcomp' p q).
						intros Hcontra. destruct Hcontra as [x_contra Hcontra].
						assert (
							exists e : nat, e < S n /\ event_process comp e = p
						) as Hcontra2. {
							destruct Hcontra as [Hx_contra_bound Hx_contra_ep].
							exists x_contra. rewrite Hcomp. rewrite <- (preserve_proc comp' (Event_send proc) x_contra). split. {
								apply (Nat.lt_lt_succ_r x_contra n) in Hx_contra_bound. apply Hx_contra_bound.
							}
							{ apply Hx_contra_ep. }
							{ lia. }
						}
						apply H in Hcontra2. inversion Hcontra2.
					}
					{
						simpl. assert ((proc =? p) = false) as Hproc_p. {
							apply Nat.eqb_neq. intros Hproc_p_contra.
							assert (
								exists e : nat, e < S n /\ event_process comp e = p
							) as Hcontra. {
								exists (length comp'). split. {
									lia.
								}
								{
									rewrite Hcomp. unfold event_process. rewrite (nth_middle comp' nil (Event_receive proc send_event_proc send_event_num) (Event 0)). apply Hproc_p_contra.
								}
							}
							apply H in Hcontra. inversion Hcontra.
						}
						rewrite Hproc_p. rewrite <- Heqn in Hcomp'. simpl in Hcomp'. rewrite Nat.sub_0_r in Hcomp'. symmetry in Hcomp'. simpl in IHn.
						apply (IHn comp' Hcomp' p q).
						intros Hcontra. destruct Hcontra as [x_contra Hcontra].
						assert (
							exists e : nat, e < S n /\ event_process comp e = p
						) as Hcontra2. {
							destruct Hcontra as [Hx_contra_bound Hx_contra_ep].
							exists x_contra. rewrite Hcomp. rewrite <- (preserve_proc comp' (Event_receive proc send_event_proc send_event_num) x_contra). split. {
								apply (Nat.lt_lt_succ_r x_contra n) in Hx_contra_bound. apply Hx_contra_bound.
							}
							{ apply Hx_contra_ep. }
							{ lia. }
						}
						apply H in Hcontra2. inversion Hcontra2.
					}
				}
			}
		}
Qed.

Lemma ets_fc2:
	forall (comp : computation) (p : process),
	(exists (x : nat), x < length comp /\ event_process comp x = p) ->
	let clocks_final : clocks :=
		snd (fst (run_computation comp init_state)) in
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	exists (y : nat), y < length comp /\ event_process comp y = p /\ event_timestamps y = clocks_final p.
Proof.
	intros comp. remember (length comp) as n. generalize dependent comp.
	induction n. {
		intros. destruct H as [x [H1 H2]]. inversion H1.
	}
	{
		(*intros comp H H0 Hx_exists. *)
		intros comp Hlen p Hx_exists.
		destruct (list_tl comp) as [comp' Hcomp']. {
			symmetry in Hlen. rewrite Hlen. lia.
		}
		{
			destruct Hcomp' as [tl Hcomp]. {
				pose proof (comp'_len comp comp' tl Hcomp) as Hcomp'.
				assert (
					event_process comp (length comp - 1) = p \/
					~(event_process comp (length comp - 1) = p)
				) as Htl. {
					apply classic.
				}
				(* ==== cccccccccc ====== - afterwards, go back to fix a' < a case of trans_contra *)
				destruct Htl as [Htl_p | Htl_notp]. {
					(* should be easier *)
					exists (length comp - 1). split. lia.
					simpl. rewrite Hcomp.
					rewrite (comp_step comp' tl). {
						unfold step.
						destruct tl. {
							simpl_step.
							rewrite <- Hcomp.
							assert ((fst (fst (run_computation comp' init_state)) =? length comp - 1) = true) as Hcomp'_len. {
								rewrite (n_value comp'). rewrite Hcomp'. rewrite Nat.eqb_refl. reflexivity.
							}
							rewrite Hcomp'_len. rewrite Nat.eqb_refl.
							split. rewrite Htl_p. reflexivity.

							simpl. unfold event_process in Htl_p. rewrite <- Hcomp' in Htl_p. rewrite Hcomp in Htl_p.
							rewrite (nth_middle comp' nil (Event proc) (Event 0)) in Htl_p.
							rewrite Htl_p. rewrite Nat.eqb_refl. reflexivity.
						}
						{
							simpl_step.
							rewrite <- Hcomp.
							assert ((fst (fst (run_computation comp' init_state)) =? length comp - 1) = true) as Hcomp'_len. {
								rewrite (n_value comp'). rewrite Hcomp'. rewrite Nat.eqb_refl. reflexivity.
							}
							rewrite Hcomp'_len. rewrite Nat.eqb_refl.
							split. rewrite Htl_p. reflexivity.

							simpl. unfold event_process in Htl_p. rewrite <- Hcomp' in Htl_p. rewrite Hcomp in Htl_p.
							rewrite (nth_middle comp' nil (Event_send proc) (Event 0)) in Htl_p.
							rewrite Htl_p. rewrite Nat.eqb_refl. reflexivity.
						}
						{
							simpl_step.
							rewrite <- Hcomp.
							assert ((fst (fst (run_computation comp' init_state)) =? length comp - 1) = true) as Hcomp'_len. {
								rewrite (n_value comp'). rewrite Hcomp'. rewrite Nat.eqb_refl. reflexivity.
							}
							rewrite Hcomp'_len. rewrite Nat.eqb_refl.
							split. rewrite Htl_p. reflexivity.

							simpl. unfold event_process in Htl_p. rewrite <- Hcomp' in Htl_p. rewrite Hcomp in Htl_p.
							rewrite (nth_middle comp' nil (Event_receive proc send_event_proc send_event_num) (Event 0)) in Htl_p.
							rewrite Htl_p. rewrite Nat.eqb_refl. reflexivity.
						}
					}
				}
				{
					assert (
						let clocks_final : clocks :=
							snd (fst (run_computation comp' init_state)) in
						let event_timestamps : time_stamps :=
							snd (run_computation comp' init_state) in
						(exists (x : nat), x < length comp' /\ event_process comp' x = p) \/
						~(exists (x : nat), x < length comp' /\ event_process comp' x = p)
					) as Hx. {
						apply classic.
					}
					destruct Hx as [Hold_x | Hno_x]. {
						rewrite <- Hlen in Hcomp'. simpl in Hcomp'. rewrite Nat.sub_0_r in Hcomp'. symmetry in Hcomp'. simpl. simpl in IHn.
						rewrite <- Hcomp' in Hold_x.
						apply (IHn comp' Hcomp' p) in Hold_x as IHn_app. {
							simpl. destruct IHn_app as [y IHn_app]. exists y.
							split. {
								destruct IHn_app as [Hy_bound [Hep_y IHn_app]]. apply Nat.lt_lt_succ_r in Hy_bound. apply Hy_bound.
							}
							split. {
								destruct IHn_app as [Hy_bound [Hep_y IHn_app]]. rewrite Hcomp.
								rewrite <- (preserve_proc comp' tl y). apply Hep_y. lia.
							}
							{
								rewrite Hcomp. rewrite <- (preserve_ets comp' tl).
								rewrite (comp_step comp' tl). {
									destruct IHn_app as [Hy_bound [Hep_y IHn_app]].
									unfold event_process in Htl_notp. rewrite <- Hlen in Htl_notp. simpl in Htl_notp. rewrite Nat.sub_0_r in Htl_notp. rewrite Hcomp' in Htl_notp. rewrite Hcomp in Htl_notp.
									rewrite (nth_middle comp' nil tl (Event 0)) in Htl_notp. apply Nat.eqb_neq in Htl_notp.
									unfold step.
									destruct tl; simpl_step; rewrite Htl_notp; apply IHn_app.
								}
								{ lia. }
							}
						}
					}
					{
						(* 
							Hno_x + Htl_not p -> H1 is false
							contra - no x *)
						destruct Hx_exists as [x [Hx_bound Hx_proc]].
						assert (
							(x < length comp') \/
							~(x < length comp')
						) as Hx. { apply classic. }
						destruct Hx as [Hx_comp' | Hx_tl]. {
							assert ((exists x : nat, x < length comp' /\ event_process comp' x = p)) as Hcontra. {
								exists x. split. { apply Hx_comp'. }
								{
									rewrite (preserve_proc comp' tl x). {
										rewrite <- Hcomp. apply Hx_proc.
									}
									{
										apply Hx_comp'.
									}
								}
							}
							apply Hno_x in Hcontra. inversion Hcontra.
						}
						{
							assert (x = length comp - 1) as Hx. {
								unfold lt in Hx_bound. apply le_S_n in Hx_bound.
								apply Nat.lt_eq_cases in Hx_bound.
								destruct Hx_bound as [Hlt | Heq]. {
									rewrite <- Hlen in Hcomp'. simpl in Hcomp'. rewrite Nat.sub_0_r in Hcomp'. rewrite Hcomp' in Hx_tl.
									apply Hx_tl in Hlt. inversion Hlt.
								}
								{
									rewrite <- Hcomp'. lia.
								}
							}
							rewrite <- Hx in Htl_notp.
							apply Htl_notp in Hx_proc.
							inversion Hx_proc.
						}
					}
				}
			}
		}
	}
Qed.

Lemma fc_max_val:
	forall (comp : computation) (p q : process),
	(forall (i : event_index), sender_prec comp i) ->
	(forall (i : event_index), sender_proc comp i) ->
	let clocks_final : clocks := 
		snd (fst (run_computation comp init_state)) in
	clocks_final p p + 1 >= clocks_final q p.
Proof.
	intros comp. remember (length comp) as n. generalize dependent comp.
	induction n.
	- intros. symmetry in Heqn. apply length_zero_iff_nil in Heqn.
		unfold clocks_final. rewrite Heqn. simpl. unfold init_clocks. unfold init_timestamps. lia.
	- intros comp Hlen p q Hsender_prec Hsender_proc. simpl. simpl in IHn.
		destruct (list_tl comp) as [comp' Hcomp']. {
			symmetry in Hlen. rewrite Hlen. lia.
		}
		{
			destruct Hcomp' as [tl Hcomp]. {
				assert (p = q \/ ~(p = q)) as Hpq. { apply classic. }
				destruct Hpq as [Hpq_eq | Hpq_neq]. {
					rewrite Hpq_eq. lia.
				}
				{
					assert (
						snd (fst (run_computation comp init_state)) p p >=
						snd (fst (run_computation comp' init_state)) p p
					) as Htrans1. {
						rewrite Hcomp. rewrite (comp_step comp' tl). {
							unfold step. simpl_step.
							destruct tl. {
								simpl. destruct (proc =? p) eqn:Hproc_p.
								{ rewrite Hproc_p. apply Nat.eqb_eq in Hproc_p. rewrite Hproc_p. lia. }
								{ lia. }
							}
							{
								simpl. destruct (proc =? p) eqn:Hproc_p.
								{ rewrite Hproc_p. apply Nat.eqb_eq in Hproc_p. rewrite Hproc_p. lia. }
								{ lia. }
							}
							{
								simpl. destruct (proc =? p) eqn:Hproc_p. {
									rewrite Hproc_p. apply Nat.eqb_eq in Hproc_p. rewrite Hproc_p.
									destruct (
										snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) p p
									) eqn:Hmax.
									{ lia. }
									{ rewrite orb_true_l. rewrite Nat.ltb_nlt in Hmax. rewrite Nat.nlt_ge in Hmax. lia. }
								}
								{ lia. }
							}
						}
					}

					assert (
						snd (fst (run_computation comp' init_state)) p p + 1 >=
						snd (fst (run_computation comp init_state)) q p
					) as Htrans2. {
						rewrite Hcomp. rewrite (comp_step comp' tl). {
							pose proof (comp'_len comp comp' tl Hcomp) as Hcomp'.
							rewrite <- Hlen in Hcomp'. simpl in Hcomp'. rewrite Nat.sub_0_r in Hcomp'. symmetry in Hcomp'.
							simpl. apply Nat.eqb_neq in Hpq_neq.
							(*unfold event_process in Htl_proc. rewrite Hlen in Htl_proc. rewrite <- Hcomp' in Htl_proc. rewrite Hcomp in Htl_proc.
							rewrite (nth_middle comp' nil tl (Event 0)) in Htl_proc.*)

							unfold step. simpl_step.
							destruct tl. {
								simpl. destruct (proc =? q) eqn:Hproc_q. {
									apply Nat.eqb_eq in Hproc_q. rewrite Hproc_q. rewrite Nat.eqb_sym in Hpq_neq. rewrite Hpq_neq.
									apply (IHn comp' Hcomp' p q). 
									{ apply (preserve_sender_prec comp comp' (Event proc) Hcomp Hsender_prec). }
									{ apply (preserve_sender_proc comp comp' (Event proc) Hcomp Hsender_prec Hsender_proc). }
								}
								{
									apply (IHn comp' Hcomp' p q). 
									{ apply (preserve_sender_prec comp comp' (Event proc) Hcomp Hsender_prec). }
									{ apply (preserve_sender_proc comp comp' (Event proc) Hcomp Hsender_prec Hsender_proc). }
								}
							}
							{
								simpl. destruct (proc =? q) eqn:Hproc_q. {
									apply Nat.eqb_eq in Hproc_q. rewrite Hproc_q. rewrite Nat.eqb_sym in Hpq_neq. rewrite Hpq_neq.
									apply (IHn comp' Hcomp' p q). 
									{ apply (preserve_sender_prec comp comp' (Event_send proc) Hcomp Hsender_prec). }
									{ apply (preserve_sender_proc comp comp' (Event_send proc) Hcomp Hsender_prec Hsender_proc). }
								}
								{
									apply (IHn comp' Hcomp' p q). 
									{ apply (preserve_sender_prec comp comp' (Event_send proc) Hcomp Hsender_prec). }
									{ apply (preserve_sender_proc comp comp' (Event_send proc) Hcomp Hsender_prec Hsender_proc). }
								}
							}
							{
								simpl.
								destruct (
									snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) q p
								) eqn:Hmax. {
									destruct (proc =? q) eqn:Hproc_q. {
										apply Nat.eqb_eq in Hproc_q. rewrite Hproc_q.
										rewrite Hmax. rewrite Nat.eqb_sym in Hpq_neq. rewrite Hpq_neq.
										apply (IHn comp' Hcomp' p q). 
										{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec). }
										{ apply (preserve_sender_proc comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec Hsender_proc). }
									}
									{
										apply (IHn comp' Hcomp' p q). 
										{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec). }
										{ apply (preserve_sender_proc comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec Hsender_proc). }
									}
								}
								{
									destruct (proc =? q) eqn:Hproc_q. {
										apply Nat.eqb_eq in Hproc_q. rewrite Hproc_q.
										rewrite Hmax. rewrite Nat.eqb_sym in Hpq_neq. rewrite Hpq_neq.
										assert (send_event_num < length comp') as Hsen_bound. {
											specialize (Hsender_prec (length comp')). unfold sender_prec in Hsender_prec.
											rewrite Hcomp in Hsender_prec. rewrite (nth_middle comp' nil (Event_receive proc send_event_proc send_event_num) (Event 0)) in Hsender_prec. apply Hsender_prec.
										}
										destruct (send_event_proc =? p) eqn:Hsen_p. {
											simpl. rewrite Nat.ltb_nlt in Hmax; rewrite Nat.nlt_ge in Hmax. apply Nat.eqb_eq in Hsen_p.
											assert (
												snd (fst (run_computation comp' init_state)) p p >=
												snd (run_computation comp' init_state) send_event_num p
											) as Hfc_ets. {
												apply (final_clocks comp' send_event_num p).
												{
													apply Hsen_bound.
												}
												{
													specialize (Hsender_proc (length comp')). unfold sender_proc in Hsender_proc.
													rewrite Hcomp in Hsender_proc. rewrite (nth_middle comp' nil (Event_receive proc send_event_proc send_event_num) (Event 0)) in Hsender_proc.
													rewrite <- (preserve_proc comp' (Event_receive proc send_event_proc send_event_num) send_event_num) in Hsender_proc.
													rewrite Hsen_p in Hsender_proc. symmetry in Hsender_proc. apply Hsender_proc. { apply Hsen_bound. }
												}
											}
											lia.
										}
										{
											simpl. apply Nat.ltb_nlt in Hmax. apply Nat.nlt_ge in Hmax.

											assert (
												snd (fst (run_computation comp' init_state)) send_event_proc p >=
												snd (run_computation comp' init_state) send_event_num p
											) as Hfc. {
												apply (final_clocks2 comp' send_event_num p send_event_proc).
												{ apply Hsen_bound. }
												{
													specialize (Hsender_proc (length comp')). unfold sender_proc in Hsender_proc.
													rewrite Hcomp in Hsender_proc. rewrite (nth_middle comp' nil (Event_receive proc send_event_proc send_event_num) (Event 0)) in Hsender_proc.
													rewrite <- (preserve_proc comp' (Event_receive proc send_event_proc send_event_num) send_event_num) in Hsender_proc. symmetry. apply Hsender_proc.
													{ apply Hsen_bound. }
												}
											}

											apply (Nat.le_trans
												(snd (run_computation comp' init_state) send_event_num p)
												(snd (fst (run_computation comp' init_state)) send_event_proc p)
												(snd (fst (run_computation comp' init_state)) p p + 1)).
											{
												apply Hfc.
											}
											{
												apply (IHn comp' Hcomp' p send_event_proc).
												{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp). apply Hsender_prec. }
												{ apply (preserve_sender_proc comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec Hsender_proc). }
											}
										}
									}
									{
										apply (IHn comp' Hcomp' p q).
										{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp). apply Hsender_prec. }
										{ apply (preserve_sender_proc comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec Hsender_proc). }
									}
								}
							}
						}
					}

					apply (Nat.le_trans
						(snd (fst (run_computation comp init_state)) q p)
						(snd (fst (run_computation comp' init_state)) p p + 1)
						(snd (fst (run_computation comp init_state)) p p + 1)); lia.
				}
			}
		}
Qed.

Lemma trans_contra:
	forall (comp : computation) (a b : event_index) (p : process),
	length comp >= 2 ->
	a < length comp ->
	b < length comp ->
	p = event_process comp a ->
	(forall (i : event_index), sender_prec comp i) -> (* will be used for b = length comp - 1 i think *)
	(forall (i : event_index), sender_proc comp i) ->
	~ msg comp a b ->
	~ seq comp a b ->
	~ (exists x : event_index, x < length comp /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b) ->
	(* ~ (exists x : event_index, x < length comp /\ after2 comp x b) -> *)
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	event_timestamps a p >= event_timestamps b p.
Proof.
	intros comp. remember (length comp) as n eqn:Hn. generalize dependent comp.
	destruct n.
	- intros. inversion H.
	- destruct n.
		+ intros. apply le_S_n in H. inversion H.
		+ induction n. {
			(* contradiction because length of list is 2, can't have ~ msg and ~ seq but ets a < ets b *)
			intros comp Hlen a b p Hlen_bound Ha_bound Hb_bound Ha_proc Hsender_prec Hsender_proc Hmsg Hseq Htrans event_timestamps.
			apply (comp_ef comp) in Hlen as Hef.

			(* destruct e and f and apply base case lemma *)
			destruct Hef as [e He]. {
				destruct He as [f Hcomp]. {
					destruct a. {
						destruct b. {
							(* a = 0, b = 0 *)
							lia.
						}
						{
							destruct b. {
								(* a = 0, b = 1 *)
								unfold event_timestamps. rewrite Hcomp. unfold run_computation; unfold fold_left; unfold step; simpl; simpl_step.
								rewrite Hcomp in Ha_proc. unfold event_process in Ha_proc. simpl in Ha_proc. rewrite Ha_proc.
								destruct e; destruct f; simpl.
								{
									rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
									destruct (proc =? proc0) eqn:Hproc_proc0. {
										unfold seq in Hseq. unfold event_process in Hseq. rewrite Hcomp in Hseq. simpl in Hseq.
										rewrite Nat.eqb_sym in Hproc_proc0. apply Nat.eqb_eq in Hproc_proc0. rewrite Hproc_proc0 in Hseq. lia.
									}
									{
										rewrite Nat.eqb_sym in Hproc_proc0. rewrite Hproc_proc0. unfold init_clocks. lia.
									}
								}
								{
									rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
									destruct (proc =? proc0) eqn:Hproc_proc0. {
										unfold seq in Hseq. unfold event_process in Hseq. rewrite Hcomp in Hseq. simpl in Hseq.
										rewrite Nat.eqb_sym in Hproc_proc0. apply Nat.eqb_eq in Hproc_proc0. rewrite Hproc_proc0 in Hseq. lia.
									}
									{
										rewrite Nat.eqb_sym in Hproc_proc0. rewrite Hproc_proc0. unfold init_clocks. lia.
									}
								}
								{
									rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
									specialize (Hsender_prec 1). unfold sender_prec in Hsender_prec. rewrite Hcomp in Hsender_prec. simpl in Hsender_prec. apply Nat.lt_1_r in Hsender_prec.
									specialize (Hsender_proc 1). unfold sender_proc in Hsender_proc. rewrite Hcomp in Hsender_proc. simpl in Hsender_proc. unfold event_process in Hsender_proc. rewrite Hsender_prec in Hsender_proc. simpl in Hsender_proc.
									unfold msg in Hmsg. rewrite Hcomp in Hmsg. simpl in Hmsg. unfold event_process in Hmsg. rewrite Hsender_prec in Hmsg. simpl in Hmsg.
									assert (0 = 0 /\ proc = send_event_proc) as Hcontra. {
										split. reflexivity. apply Hsender_proc.
									}
									apply Hmsg in Hcontra. inversion Hcontra.
								}
								{
									rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
									destruct (proc =? proc0) eqn:Hproc_proc0. {
										unfold seq in Hseq. unfold event_process in Hseq. rewrite Hcomp in Hseq. simpl in Hseq.
										rewrite Nat.eqb_sym in Hproc_proc0. apply Nat.eqb_eq in Hproc_proc0. rewrite Hproc_proc0 in Hseq. lia.
									}
									{
										rewrite Nat.eqb_sym in Hproc_proc0. rewrite Hproc_proc0. unfold init_clocks. lia.
									}
								}
								{
									rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
									destruct (proc =? proc0) eqn:Hproc_proc0. {
										unfold seq in Hseq. unfold event_process in Hseq. rewrite Hcomp in Hseq. simpl in Hseq.
										rewrite Nat.eqb_sym in Hproc_proc0. apply Nat.eqb_eq in Hproc_proc0. rewrite Hproc_proc0 in Hseq. lia.
									}
									{
										rewrite Nat.eqb_sym in Hproc_proc0. rewrite Hproc_proc0. unfold init_clocks. lia.
									}
								}
								{
									rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
									specialize (Hsender_prec 1). unfold sender_prec in Hsender_prec. rewrite Hcomp in Hsender_prec. simpl in Hsender_prec. apply Nat.lt_1_r in Hsender_prec.
									specialize (Hsender_proc 1). unfold sender_proc in Hsender_proc. rewrite Hcomp in Hsender_proc. simpl in Hsender_proc. unfold event_process in Hsender_proc. rewrite Hsender_prec in Hsender_proc. simpl in Hsender_proc.
									unfold msg in Hmsg. rewrite Hcomp in Hmsg. simpl in Hmsg. unfold event_process in Hmsg. rewrite Hsender_prec in Hmsg. simpl in Hmsg.
									assert (0 = 0 /\ proc = send_event_proc) as Hcontra. {
										split. reflexivity. apply Hsender_proc.
									}
									apply Hmsg in Hcontra. inversion Hcontra.
								}
								{
									rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
									destruct (proc =? proc0) eqn:Hproc_proc0. {
										unfold seq in Hseq. unfold event_process in Hseq. rewrite Hcomp in Hseq. simpl in Hseq.
										rewrite Nat.eqb_sym in Hproc_proc0. apply Nat.eqb_eq in Hproc_proc0. rewrite Hproc_proc0 in Hseq. lia.
									}
									{
										rewrite Nat.eqb_sym in Hproc_proc0. rewrite Hproc_proc0. unfold init_clocks. lia.
									}
								}
								{
									rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
									destruct (proc =? proc0) eqn:Hproc_proc0. {
										unfold seq in Hseq. unfold event_process in Hseq. rewrite Hcomp in Hseq. simpl in Hseq.
										rewrite Nat.eqb_sym in Hproc_proc0. apply Nat.eqb_eq in Hproc_proc0. rewrite Hproc_proc0 in Hseq. lia.
									}
									{
										rewrite Nat.eqb_sym in Hproc_proc0. rewrite Hproc_proc0. unfold init_clocks. lia.
									}
								}
								{
									rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
									specialize (Hsender_prec 1). unfold sender_prec in Hsender_prec. rewrite Hcomp in Hsender_prec. simpl in Hsender_prec. apply Nat.lt_1_r in Hsender_prec.
									specialize (Hsender_proc 1). unfold sender_proc in Hsender_proc. rewrite Hcomp in Hsender_proc. simpl in Hsender_proc. unfold event_process in Hsender_proc. rewrite Hsender_prec in Hsender_proc. simpl in Hsender_proc.
									unfold msg in Hmsg. rewrite Hcomp in Hmsg. simpl in Hmsg. unfold event_process in Hmsg. rewrite Hsender_prec in Hmsg. simpl in Hmsg.
									assert (0 = 0 /\ proc = send_event_proc0) as Hcontra. {
										split. reflexivity. apply Hsender_proc.
									}
									apply Hmsg in Hcontra. inversion Hcontra.
								}
							}
							{
								unfold lt in Hb_bound. apply le_S_n in Hb_bound. apply le_S_n in Hb_bound. inversion Hb_bound.
							}
						}
					}
					destruct a. {
						destruct b. {
							(* a = 1, b = 0 *)
							destruct e; destruct f; simpl; unfold event_timestamps; rewrite Hcomp; 
							unfold event_timestamps; unfold run_computation; unfold fold_left; unfold step; simpl; simpl_step;
							rewrite Hcomp in Ha_proc; unfold event_process in Ha_proc; simpl in Ha_proc; rewrite <- Ha_proc;
							rewrite Nat.eqb_refl; rewrite Nat.eqb_refl; rewrite Nat.eqb_refl.
							{
								destruct (proc =? p) eqn:Hproc_p. {
									rewrite Hproc_p. simpl. rewrite Nat.eqb_refl. rewrite Hproc_p. lia.
								}
								{
									unfold init_clocks. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. simpl. rewrite Hproc_p. lia.
								}
							}
							{
								destruct (proc =? p) eqn:Hproc_p. {
									rewrite Hproc_p. simpl. rewrite Nat.eqb_refl. rewrite Hproc_p. lia.
								}
								{
									unfold init_clocks. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. simpl. rewrite Hproc_p. lia.
								}
							}
							{
								destruct (proc =? p) eqn:Hproc_p. {
									rewrite Hproc_p. simpl. rewrite Nat.eqb_refl. rewrite Hproc_p.
									destruct send_event_num.
									{ rewrite Hproc_p. simpl. lia. }
									{ unfold init_timestamps. simpl. lia. }
								}
								{
									unfold init_clocks. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. simpl. rewrite Hproc_p. lia.
								}
							}
							{
								destruct (proc =? p) eqn:Hproc_p. {
									rewrite Hproc_p. simpl. rewrite Nat.eqb_refl. rewrite Hproc_p. lia.
								}
								{
									unfold init_clocks. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. simpl. rewrite Hproc_p. lia.
								}
							}
							{
								destruct (proc =? p) eqn:Hproc_p. {
									rewrite Hproc_p. simpl. rewrite Nat.eqb_refl. rewrite Hproc_p. lia.
								}
								{
									unfold init_clocks. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. simpl. rewrite Hproc_p. lia.
								}
							}
							{
								destruct (proc =? p) eqn:Hproc_p. {
									rewrite Hproc_p. simpl. rewrite Nat.eqb_refl. rewrite Hproc_p.
									destruct send_event_num.
									{ rewrite Hproc_p. simpl. lia. }
									{ unfold init_timestamps. simpl. lia. }
								}
								{
									unfold init_clocks. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. simpl. rewrite Hproc_p. lia.
								}
							}
							{
								destruct (proc =? p) eqn:Hproc_p. {
									rewrite Hproc_p. simpl. rewrite Nat.eqb_refl. rewrite Hproc_p. simpl. lia.
								}
								{
									unfold init_clocks. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. simpl. rewrite Hproc_p.
									destruct (send_event_proc =? p); simpl; unfold init_timestamps; lia.
								}
							}
							{
								destruct (proc =? p) eqn:Hproc_p. {
									rewrite Hproc_p. simpl. rewrite Nat.eqb_refl. rewrite Hproc_p. simpl. lia.
								}
								{
									unfold init_clocks. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. simpl. rewrite Hproc_p.
									destruct (send_event_proc =? p); simpl; unfold init_timestamps; lia.
								}
							}
							{
								destruct (proc =? p) eqn:Hproc_p. {
									rewrite Hproc_p. simpl. rewrite Nat.eqb_refl. rewrite Hproc_p.
									destruct send_event_num0.
									{ rewrite Hproc_p. simpl. lia. }
									{ unfold init_timestamps. simpl. lia. }
								}
								{
									unfold init_clocks. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. simpl. rewrite Hproc_p.
									destruct send_event_num0. {
										rewrite Hproc_p. unfold init_timestamps. simpl.
										destruct (send_event_proc =? p) eqn:Hsen_p; lia.
									}
									{
										unfold init_timestamps. simpl.
										destruct (send_event_proc =? p) eqn:Hsen_p; lia.
									}
								}
							}
						}
						destruct b. {
							(* a = 1, b = 1 *)
							lia.
						}
						{
							unfold lt in Hb_bound. apply le_S_n in Hb_bound. apply le_S_n in Hb_bound. inversion Hb_bound.
						}
					}
					unfold lt in Ha_bound. apply le_S_n in Ha_bound. apply le_S_n in Ha_bound. inversion Ha_bound.
				}
			}
		}
		{
			intros comp Hlen a b p Hlen_bound Ha_bound Hb_bound Ha_proc Hsender_prec Hsender_proc Hmsg Hseq Htrans event_timestamps.

			destruct (list_tl comp) as [comp' Hcomp']. {
				symmetry in Hlen. rewrite Hlen. lia.
			}
			{
				destruct Hcomp' as [tl Hcomp]. {
					pose proof (comp'_len comp comp' tl Hcomp) as Hcomp'.
					assert (a = length comp' \/ ~(a = length comp')) as Ha. { apply classic. }
					destruct Ha as [Ha | Ha_neq]. {
						assert (a = b \/ ~(a = b)) as Hab. { apply classic. }
						destruct Hab as [Hab_eq | Hab_neq]. {
							rewrite Hab_eq. lia.
						}
						{
							(* a = length comp' -> ets a p = fc p p >= ets b p for all other b *)
							assert ((fst (fst (run_computation comp' init_state)) =? a) = true) as Ha_nvalue. {
								rewrite (n_value comp'). rewrite Ha. rewrite Nat.eqb_refl. reflexivity.
							}
							assert (event_timestamps a p >= snd (fst (run_computation comp' init_state)) p p + 1) as Htrans1. {
								unfold event_timestamps. rewrite Hcomp. rewrite (comp_step comp' tl).
								unfold step. simpl_step. destruct tl. {
									assert (proc = p) as Hproc_p. {
										unfold event_process in Ha_proc; rewrite Hcomp in Ha_proc; rewrite Ha in Ha_proc; rewrite (nth_middle comp' nil (Event proc) (Event 0)) in Ha_proc. symmetry. apply Ha_proc.
									}
									simpl. rewrite Ha_nvalue. rewrite Hproc_p. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. lia.
								}
								{
									assert (proc = p) as Hproc_p. {
										unfold event_process in Ha_proc; rewrite Hcomp in Ha_proc; rewrite Ha in Ha_proc; rewrite (nth_middle comp' nil (Event_send proc) (Event 0)) in Ha_proc. symmetry. apply Ha_proc.
									}
									simpl. rewrite Ha_nvalue. rewrite Hproc_p. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. lia.
								}
								{
									assert (proc = p) as Hproc_p. {
										unfold event_process in Ha_proc; rewrite Hcomp in Ha_proc; rewrite Ha in Ha_proc; rewrite (nth_middle comp' nil (Event_receive proc send_event_proc send_event_num) (Event 0)) in Ha_proc. symmetry. apply Ha_proc.
									}
									simpl. rewrite Ha_nvalue. rewrite Hproc_p. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite orb_true_l.
									destruct (
										snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) p p
									) eqn:Hmax.
									{ lia. }
									{ apply Nat.ltb_nlt in Hmax. apply Nat.nlt_ge in Hmax. lia. }
								}
							}

							assert (snd (fst (run_computation comp' init_state)) p p + 1 >= snd (fst (run_computation comp' init_state)) (event_process comp' b) p) as Htrans2. {
								apply (fc_max_val comp' p (event_process comp' b)).
								{ apply (preserve_sender_prec comp comp' tl Hcomp Hsender_prec). }
								{ apply (preserve_sender_proc comp comp' tl Hcomp Hsender_prec Hsender_proc). }
							}

							assert (snd (fst (run_computation comp' init_state)) (event_process comp' b) p >= event_timestamps b p) as Htrans3. {
								unfold event_timestamps. rewrite Hcomp. rewrite <- (preserve_ets comp' tl b).
								apply (final_clocks2 comp' b p (event_process comp' b)).
								{ lia. }
								{ reflexivity. }
								{ lia. }
							}

							apply (Nat.le_trans
								(event_timestamps b p)
								(snd (fst (run_computation comp' init_state)) (event_process comp' b) p)
								(event_timestamps a p)).
							{ apply Htrans3. }
							{
								apply (Nat.le_trans
									(snd (fst (run_computation comp' init_state)) (event_process comp' b) p)
									(snd (fst (run_computation comp' init_state)) p p + 1)
									(event_timestamps a p)).
								{ apply Htrans2. }
								{ apply Htrans1. }
							}
						}
					}
					{
						rewrite <- Hlen in Hcomp'. simpl in Hcomp'. symmetry in Hcomp'. simpl in IHn.
						assert (b = length comp' \/ ~(b = length comp')) as Hb. { apply classic. }
						destruct Hb as [Hb | Hb_neq]. {
							assert ((fst (fst (run_computation comp' init_state)) =? b) = true) as Hb_val. {
								rewrite (n_value comp'). rewrite Hb. rewrite Nat.eqb_refl. reflexivity.
							}
							assert (a < b) as Hab. {
								lia.
							}
							assert (nth b comp (Event 0) = tl) as Htl. {
								rewrite Hcomp. rewrite Hb. rewrite (nth_middle comp' nil tl (Event 0)). reflexivity.
							}

							{
								destruct tl.
								{
									assert ((proc =? p) = false) as Hp_proc. {
										apply Nat.eqb_neq. intros Hcontra.
										assert (seq comp a b) as Hseq_ab. {
											unfold seq. split. {
												rewrite <- Ha_proc.
												unfold event_process. rewrite Hb. rewrite Hcomp. rewrite (nth_middle comp' nil (Event proc) (Event 0)). symmetry. apply Hcontra.
											}
											{
												lia.
											}
										}
										apply Hseq in Hseq_ab. inversion Hseq_ab.
									}
									Check ets_fc2.
									(* Event *)
									assert (
										(exists (x : nat), x < length comp' /\ event_process comp' x = event_process comp b) \/
										~(exists (x : nat), x < length comp' /\ event_process comp' x = event_process comp b)
									) as Hx_exists. { apply classic.  }

									destruct Hx_exists as [Hx_exists | Hx_nexists]. {

										(* exists x, seq x b *) 	(* get rid of pose proof? ===*)
										pose proof ets_fc2 as Hets_fc2. simpl in Hets_fc2. unfold event_timestamps.
										apply (Hets_fc2 comp' (event_process comp b)) in Hx_exists as Hx_exists'.

										(* ets x p = fc' q p *)
										destruct Hx_exists' as [x Hx_exists'].

										(* ets x p = ets b p*)
										assert (
											let event_timestamps : time_stamps :=
												snd (run_computation comp init_state) in
											event_timestamps x p = event_timestamps b p
										) as Hxb. {

											(* fc' q p = fc q p *)
											assert (
												snd (fst (run_computation comp' init_state)) proc p =
												snd (fst (run_computation comp init_state)) proc p
											) as Htrans2. {
												rewrite Hcomp.
												rewrite (comp_step comp' (Event proc)). {
													unfold step. simpl. simpl_step. rewrite Nat.eqb_refl.
													rewrite Hp_proc. reflexivity.
												}
											}

											(* fc q p = ets b p *)
											assert (
												snd (fst (run_computation comp init_state)) proc p =
												snd (run_computation comp init_state) b p
											) as Htrans3. {
												rewrite Hcomp.
												rewrite (comp_step comp' (Event proc)). {
													unfold step. simpl. simpl_step. rewrite Nat.eqb_refl. rewrite Hb_val. rewrite Hp_proc. reflexivity.
												}
											}
											destruct Hx_exists as [x0 [Hx_bound Hx_proc]].
											destruct Hx_exists' as [Hx_bound' [Hep_xb Hx_exists']].
											unfold event_process in Hx_exists'. rewrite Htl in Hx_exists'.
											simpl. rewrite <- Htrans3. rewrite <- Htrans2. rewrite <- Hx_exists'. rewrite Hcomp.
											rewrite <- (preserve_ets comp' (Event proc) x).
											{ reflexivity. }
											{ apply Hx_bound'. }
										}

										(* ets a p >= ets x p*)
										assert (
											event_timestamps a p >= event_timestamps x p
										) as Hax. {
											(* use IH *)
											(* we know ~ after a x because otherwise, seq x b -> after a b by trans, contra *)
											unfold event_timestamps. rewrite Hcomp.
											rewrite <- (preserve_ets comp' (Event proc) a). {
												rewrite <- (preserve_ets comp' (Event proc) x). {
													assert (seq comp x b) as Hseq_xb. {
														destruct Hx_exists' as [Hx_bound' [Hep_xb Hx_exists']].
														unfold seq. split. {
															rewrite (preserve_proc comp' (Event proc) x) in Hep_xb. rewrite <- Hcomp in Hep_xb. apply Hep_xb. { lia. }
														}
														{
															rewrite Hb. apply Hx_bound'.
														}
													}
													apply (IHn comp' Hcomp' a x p).
													{ lia. }
													{ lia. }
													{ lia. }
													{ rewrite (preserve_proc comp' (Event proc)).
														rewrite <- Hcomp. apply Ha_proc. { lia. } }
													{ apply (preserve_sender_prec comp comp' (Event proc) Hcomp Hsender_prec). }
													{ apply (preserve_sender_proc comp comp' (Event proc) Hcomp Hsender_prec Hsender_proc). }
													{
														unfold not. intros Hmsg_contra. unfold not in Htrans.
														assert (
															(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
														) as Hcontra. {
															exists x. split. { lia. } split. right. { 
																apply (maintain_msg comp comp' (Event proc) a x).
																{ lia. }
																{ lia. }
																{ apply Hcomp. }
																{ apply (preserve_sender_prec comp comp' (Event proc) Hcomp Hsender_prec). }
																{ apply Hmsg_contra. }
															}
															{
																apply (after_sp2 comp x b Hseq_xb).
															}
														}
														{
															apply Htrans in Hcontra. inversion Hcontra.
														}
													}
													{
														unfold not. intros Hseq_contra. unfold not in Htrans.
														assert (
															(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
														) as Hcontra. {
															exists x. split. { lia. } split. left. { 
																apply (maintain_seq comp comp' (Event proc) a x).
																{ lia. }
																{ lia. }
																{ apply Hcomp. }
																{ apply Hseq_contra. }
															}
															{
																apply (after_sp2 comp x b Hseq_xb).
															}
														}
														{
															apply Htrans in Hcontra. inversion Hcontra.
														}
													}
													{
														unfold not. intros Htrans_contra. unfold not in Htrans.
														destruct Htrans_contra as [x_contra [Hxc_bound [Haxc_base Hxc_after2]]].
														assert (after2 comp x_contra x) as Hafter2_1. {
															apply (maintain_after2 comp comp' (Event proc) x_contra x).
															{ lia. }
															{ lia. }
															{ apply Hcomp. }
															{ apply (preserve_sender_prec comp comp' (Event proc) Hcomp). apply Hsender_prec. }
															{ apply Hxc_after2. }
														}
														assert (after2 comp x b) as Hafter2_2. {
															apply (after_sp2 comp x b Hseq_xb).
														}
														assert (after2 comp x_contra b) as Hafter2. {
															apply (after_trans2 comp x_contra x b Hafter2_1 Hafter2_2). { lia. }
														}
														assert (
															(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
														) as Hcontra. {
															exists x_contra. split. { lia. } split.
															destruct Haxc_base as [Haxc_seq | Haxc_msg].
															{
																apply (maintain_seq comp comp' (Event proc) a x_contra) in Haxc_seq.
																left. apply Haxc_seq. { lia. } { lia. } { apply Hcomp. }
															}
															{
																apply (maintain_msg comp comp' (Event proc) a x_contra) in Haxc_msg.
																right. apply Haxc_msg. { lia. } { lia. } { apply Hcomp. } {
																	apply (preserve_sender_prec comp comp' (Event proc) Hcomp). apply Hsender_prec. (* === bring outside? === *)
																}
															}
															apply (after_trans2 comp x_contra x b Hafter2_1 Hafter2_2). { lia. }
														}
														apply Htrans in Hcontra. inversion Hcontra.
													}
												}
												{ lia. }
											}
											{ lia. }
										}

										simpl in Hxb. simpl in Hax. unfold event_timestamps. rewrite <- Hxb. apply Hax.
									}
									{
										(* not exists x, seq x b *)
										(* probably need to use ets_fc2 *)
										(* === aaaaaa === *)

										assert (snd (run_computation comp init_state) b p = 0) as Hb0. {
											rewrite Hcomp. 
											rewrite (comp_step comp' (Event proc)). {
												unfold step. simpl. simpl_step.
												rewrite (n_value comp'). {
													rewrite Hb. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Hp_proc.
													assert (event_process comp b = proc) as Hb_proc. {
														unfold event_process. rewrite Htl. reflexivity.
													}
													rewrite Hb_proc in Hx_nexists. apply (empty_process comp' proc p).
													{ apply Hx_nexists. }
												} 
											}
										}
										unfold event_timestamps. rewrite Hb0. unfold ge. apply Nat.le_0_l.
									}
								}
								{
									(* Event_send *)
									assert ((proc =? p) = false) as Hp_proc. {
										apply Nat.eqb_neq. intros Hcontra.
										assert (seq comp a b) as Hseq_ab. {
											unfold seq. split. {
												rewrite <- Ha_proc.
												unfold event_process. rewrite Hb. rewrite Hcomp. rewrite (nth_middle comp' nil (Event_send proc) (Event 0)). symmetry. apply Hcontra.
											}
											{
												lia.
											}
										}
										apply Hseq in Hseq_ab. inversion Hseq_ab.
									}
									(* Event *)
									assert (
										(exists (x : nat), x < length comp' /\ event_process comp' x = event_process comp b) \/
										~(exists (x : nat), x < length comp' /\ event_process comp' x = event_process comp b)
									) as Hx_exists. { apply classic.  }

									destruct Hx_exists as [Hx_exists | Hx_nexists]. {

										(* exists x, seq x b *) 	(* get rid of pose proof? ===*)
										pose proof ets_fc2 as Hets_fc2. simpl in Hets_fc2. unfold event_timestamps.
										apply (Hets_fc2 comp' (event_process comp b)) in Hx_exists as Hx_exists'.

										(* ets x p = fc' q p *)
										destruct Hx_exists' as [x Hx_exists'].

										(* ets x p = ets b p*)
										assert (
											let event_timestamps : time_stamps :=
												snd (run_computation comp init_state) in
											event_timestamps x p = event_timestamps b p
										) as Hxb. {

											(* fc' q p = fc q p *)
											assert (
												snd (fst (run_computation comp' init_state)) proc p =
												snd (fst (run_computation comp init_state)) proc p
											) as Htrans2. {
												rewrite Hcomp.
												rewrite (comp_step comp' (Event_send proc)). {
													unfold step. simpl. simpl_step. rewrite Nat.eqb_refl.
													rewrite Hp_proc. reflexivity.
												}
											}

											(* fc q p = ets b p *)
											assert (
												snd (fst (run_computation comp init_state)) proc p =
												snd (run_computation comp init_state) b p
											) as Htrans3. {
												rewrite Hcomp.
												rewrite (comp_step comp' (Event_send proc)). {
													unfold step. simpl. simpl_step. rewrite Nat.eqb_refl. rewrite Hb_val. rewrite Hp_proc. reflexivity.
												}
											}
											destruct Hx_exists as [x0 [Hx_bound Hx_proc]].
											destruct Hx_exists' as [Hx_bound' [Hep_xb Hx_exists']].
											unfold event_process in Hx_exists'. rewrite Htl in Hx_exists'.
											simpl. rewrite <- Htrans3. rewrite <- Htrans2. rewrite <- Hx_exists'. rewrite Hcomp.
											rewrite <- (preserve_ets comp' (Event_send proc) x).
											{ reflexivity. }
											{ apply Hx_bound'. }
										}

										(* ets a p >= ets x p*)
										assert (
											event_timestamps a p >= event_timestamps x p
										) as Hax. {
											(* use IH *)
											(* we know ~ after a x because otherwise, seq x b -> after a b by trans, contra *)
											unfold event_timestamps. rewrite Hcomp.
											rewrite <- (preserve_ets comp' (Event_send proc) a). {
												rewrite <- (preserve_ets comp' (Event_send proc) x). {
													assert (seq comp x b) as Hseq_xb. {
														destruct Hx_exists' as [Hx_bound' [Hep_xb Hx_exists']].
														unfold seq. split. {
															rewrite (preserve_proc comp' (Event_send proc) x) in Hep_xb. rewrite <- Hcomp in Hep_xb. apply Hep_xb. { lia. }
														}
														{
															rewrite Hb. apply Hx_bound'.
														}
													}
													apply (IHn comp' Hcomp' a x p).
													{ lia. }
													{ lia. }
													{ lia. }
													{ rewrite (preserve_proc comp' (Event_send proc)).
														rewrite <- Hcomp. apply Ha_proc. { lia. } }
													{ apply (preserve_sender_prec comp comp' (Event_send proc) Hcomp Hsender_prec). }
													{ apply (preserve_sender_proc comp comp' (Event_send proc) Hcomp Hsender_prec Hsender_proc). }
													{
														unfold not. intros Hmsg_contra. unfold not in Htrans.
														assert (
															(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
														) as Hcontra. {
															exists x. split. { lia. } split. right. { 
																apply (maintain_msg comp comp' (Event_send proc) a x).
																{ lia. }
																{ lia. }
																{ apply Hcomp. }
																{ apply (preserve_sender_prec comp comp' (Event_send proc) Hcomp Hsender_prec). }
																{ apply Hmsg_contra. }
															}
															{
																apply (after_sp2 comp x b Hseq_xb).
															}
														}
														{
															apply Htrans in Hcontra. inversion Hcontra.
														}
													}
													{
														unfold not. intros Hseq_contra. unfold not in Htrans.
														assert (
															(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
														) as Hcontra. {
															exists x. split. { lia. } split. left. { 
																apply (maintain_seq comp comp' (Event_send proc) a x).
																{ lia. }
																{ lia. }
																{ apply Hcomp. }
																{ apply Hseq_contra. }
															}
															{
																apply (after_sp2 comp x b Hseq_xb).
															}
														}
														{
															apply Htrans in Hcontra. inversion Hcontra.
														}
													}
													{
														unfold not. intros Htrans_contra. unfold not in Htrans.
														destruct Htrans_contra as [x_contra [Hxc_bound [Haxc_base Hxc_after2]]].
														assert (after2 comp x_contra x) as Hafter2_1. {
															apply (maintain_after2 comp comp' (Event_send proc) x_contra x).
															{ lia. }
															{ lia. }
															{ apply Hcomp. }
															{ apply (preserve_sender_prec comp comp' (Event_send proc) Hcomp). apply Hsender_prec. }
															{ apply Hxc_after2. }
														}
														assert (after2 comp x b) as Hafter2_2. {
															apply (after_sp2 comp x b Hseq_xb).
														}
														assert (after2 comp x_contra b) as Hafter2. {
															apply (after_trans2 comp x_contra x b Hafter2_1 Hafter2_2). { lia. }
														}
														assert (
															(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
														) as Hcontra. {
															exists x_contra. split. { lia. } split.
															destruct Haxc_base as [Haxc_seq | Haxc_msg].
															{
																apply (maintain_seq comp comp' (Event_send proc) a x_contra) in Haxc_seq.
																left. apply Haxc_seq. { lia. } { lia. } { apply Hcomp. }
															}
															{
																apply (maintain_msg comp comp' (Event_send proc) a x_contra) in Haxc_msg.
																right. apply Haxc_msg. { lia. } { lia. } { apply Hcomp. } {
																	apply (preserve_sender_prec comp comp' (Event_send proc) Hcomp). apply Hsender_prec. (* === bring outside? === *)
																}
															}
															apply (after_trans2 comp x_contra x b Hafter2_1 Hafter2_2). { lia. }
														}
														apply Htrans in Hcontra. inversion Hcontra.
													}
												}
												{ lia. }
											}
											{ lia. }
										}

										simpl in Hxb. simpl in Hax. unfold event_timestamps. rewrite <- Hxb. apply Hax.
									
									}
									{
										(* not exists x, seq x b *)
										(* probably need to use ets_fc2 *)
										(* === aaaaaa === *)

										assert (snd (run_computation comp init_state) b p = 0) as Hb0. {
											rewrite Hcomp. 
											rewrite (comp_step comp' (Event_send proc)). {
												unfold step. simpl. simpl_step.
												rewrite (n_value comp'). {
													rewrite Hb. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Hp_proc.
													assert (event_process comp b = proc) as Hb_proc. {
														unfold event_process. rewrite Htl. reflexivity.
													}
													rewrite Hb_proc in Hx_nexists. apply (empty_process comp' proc p).
													{ apply Hx_nexists. }
												} 
											}
										}
										unfold event_timestamps. rewrite Hb0. unfold ge. apply Nat.le_0_l.
									}

								}
								{
									(* === make this a lemma === *)
									(* Event_receive *)
									assert ((proc =? p) = false) as Hp_proc. {
										apply Nat.eqb_neq. intros Hcontra.
										assert (seq comp a b) as Hseq_ab. {
											unfold seq. split. {
												rewrite <- Ha_proc.
												unfold event_process. rewrite Hb. rewrite Hcomp. rewrite (nth_middle comp' nil (Event_receive proc send_event_proc send_event_num) (Event 0)). symmetry. apply Hcontra.
											}
											{
												lia.
											}
										}
										apply Hseq in Hseq_ab. inversion Hseq_ab.
									}
									assert (msg comp send_event_num b) as Hmsg_sen_b. {
										unfold msg. rewrite Htl. split. {
											reflexivity.
										}
										{
											specialize (Hsender_proc b). unfold sender_proc in Hsender_proc. rewrite Htl in Hsender_proc. apply Hsender_proc.
										}
									}

									destruct (p =? send_event_proc) eqn:Hsend_event_proc. {
										(* send_event_proc == p *)
										destruct (send_event_num <? a) eqn:Hsend_event_num.
										{
											destruct (
												snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) proc p
											) eqn:Hmax. {
												(* ets b p = max(ets a' p, fc q p) = fc q p *)
												assert (
													(exists (x : nat), x < length comp' /\ event_process comp' x = event_process comp b) \/
													~(exists (x : nat), x < length comp' /\ event_process comp' x = event_process comp b)
												) as Hx_exists. { apply classic.  }

												destruct Hx_exists as [Hx_exists | Hx_nexists]. {

													(* exists x, seq x b *) 	(* get rid of pose proof? ===*)
													pose proof ets_fc2 as Hets_fc2. simpl in Hets_fc2. unfold event_timestamps.
													apply (Hets_fc2 comp' (event_process comp b)) in Hx_exists as Hx_exists'.

													(* ets x p = fc' q p *)
													destruct Hx_exists' as [x Hx_exists'].

													(* ets x p = ets b p*)
													assert (
														let event_timestamps : time_stamps :=
															snd (run_computation comp init_state) in
														event_timestamps x p = event_timestamps b p
													) as Hxb. {

														(* fc' q p = fc q p *)
														assert (
															snd (fst (run_computation comp' init_state)) proc p =
															snd (fst (run_computation comp init_state)) proc p
														) as Htrans2. {
															rewrite Hcomp.
															rewrite (comp_step comp' (Event_receive proc send_event_proc send_event_num)). {
																unfold step. simpl. simpl_step. rewrite Nat.eqb_refl. rewrite Hmax.
																
																rewrite Hp_proc. reflexivity.
															}
														}

														(* fc q p = ets b p *)
														assert (
															snd (fst (run_computation comp init_state)) proc p =
															snd (run_computation comp init_state) b p
														) as Htrans3. {
															rewrite Hcomp.
															rewrite (comp_step comp' (Event_receive proc send_event_proc send_event_num)). {
																unfold step. simpl. simpl_step. rewrite Nat.eqb_refl. rewrite Hb_val. rewrite Hmax. rewrite Hp_proc. reflexivity.
															}
														}
														destruct Hx_exists as [x0 [Hx_bound Hx_proc]].
														destruct Hx_exists' as [Hx_bound' [Hep_xb Hx_exists']].
														unfold event_process in Hx_exists'. rewrite Htl in Hx_exists'.
														simpl. rewrite <- Htrans3. rewrite <- Htrans2. rewrite <- Hx_exists'. rewrite Hcomp.
														rewrite <- (preserve_ets comp' (Event_receive proc send_event_proc send_event_num) x).
														{ reflexivity. }
														{ apply Hx_bound'. }
													}

													(* ets a p >= ets x p*)
													assert (
														event_timestamps a p >= event_timestamps x p
													) as Hax. {
														(* use IH *)
														(* we know ~ after a x because otherwise, seq x b -> after a b by trans, contra *)
														unfold event_timestamps. rewrite Hcomp.
														rewrite <- (preserve_ets comp' (Event_receive proc send_event_proc send_event_num) a). {
															rewrite <- (preserve_ets comp' (Event_receive proc send_event_proc send_event_num) x). {
																assert (seq comp x b) as Hseq_xb. {
																	destruct Hx_exists' as [Hx_bound' [Hep_xb Hx_exists']].
																	unfold seq. split. {
																		rewrite (preserve_proc comp' (Event_receive proc send_event_proc send_event_num) x) in Hep_xb. rewrite <- Hcomp in Hep_xb. apply Hep_xb. { lia. }
																	}
																	{
																		rewrite Hb. apply Hx_bound'.
																	}
																}
																apply (IHn comp' Hcomp' a x p).
																{ lia. }
																{ lia. }
																{ lia. }
																{ rewrite (preserve_proc comp' (Event_receive proc send_event_proc send_event_num)).
																	rewrite <- Hcomp. apply Ha_proc. { lia. } }
																{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec). }
																{ apply (preserve_sender_proc comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec Hsender_proc). }
																{
																	unfold not. intros Hmsg_contra. unfold not in Htrans.
																	assert (
																		(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
																	) as Hcontra. {
																		exists x. split. { lia. } split. right. { 
																			apply (maintain_msg comp comp' (Event_receive proc send_event_proc send_event_num) a x).
																			{ lia. }
																			{ lia. }
																			{ apply Hcomp. }
																			{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec). }
																			{ apply Hmsg_contra. }
																		}
																		{
																			apply (after_sp2 comp x b Hseq_xb).
																		}
																	}
																	{
																		apply Htrans in Hcontra. inversion Hcontra.
																	}
																}
																{
																	unfold not. intros Hseq_contra. unfold not in Htrans.
																	assert (
																		(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
																	) as Hcontra. {
																		exists x. split. { lia. } split. left. { 
																			apply (maintain_seq comp comp' (Event_receive proc send_event_proc send_event_num) a x).
																			{ lia. }
																			{ lia. }
																			{ apply Hcomp. }
																			{ apply Hseq_contra. }
																		}
																		{
																			apply (after_sp2 comp x b Hseq_xb).
																		}
																	}
																	{
																		apply Htrans in Hcontra. inversion Hcontra.
																	}
																}
																{
																	unfold not. intros Htrans_contra. unfold not in Htrans.
																	destruct Htrans_contra as [x_contra [Hxc_bound [Haxc_base Hxc_after2]]].
																	assert (after2 comp x_contra x) as Hafter2_1. {
																		apply (maintain_after2 comp comp' (Event_receive proc send_event_proc send_event_num) x_contra x).
																		{ lia. }
																		{ lia. }
																		{ apply Hcomp. }
																		{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp). apply Hsender_prec. }
																		{ apply Hxc_after2. }
																	}
																	assert (after2 comp x b) as Hafter2_2. {
																		apply (after_sp2 comp x b Hseq_xb).
																	}
																	assert (after2 comp x_contra b) as Hafter2. {
																		apply (after_trans2 comp x_contra x b Hafter2_1 Hafter2_2). { lia. }
																	}
																	assert (
																		(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
																	) as Hcontra. {
																		exists x_contra. split. { lia. } split.
																		destruct Haxc_base as [Haxc_seq | Haxc_msg].
																		{
																			apply (maintain_seq comp comp' (Event_receive proc send_event_proc send_event_num) a x_contra) in Haxc_seq.
																			left. apply Haxc_seq. { lia. } { lia. } { apply Hcomp. }
																		}
																		{
																			apply (maintain_msg comp comp' (Event_receive proc send_event_proc send_event_num) a x_contra) in Haxc_msg.
																			right. apply Haxc_msg. { lia. } { lia. } { apply Hcomp. } {
																				apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp). apply Hsender_prec. (* === bring outside? === *)
																			}
																		}
																		apply (after_trans2 comp x_contra x b Hafter2_1 Hafter2_2). { lia. }
																	}
																	apply Htrans in Hcontra. inversion Hcontra.
																}
															}
															{ lia. }
														}
														{ lia. }
													}

													simpl in Hxb. simpl in Hax. unfold event_timestamps. rewrite <- Hxb. apply Hax.
												
												}
												{
													(* not exists x, seq x b *)
													(* probably need to use ets_fc2 *)
													(* === aaaaaa === *)

													assert (snd (run_computation comp init_state) b p = 0) as Hb0. {
														rewrite Hcomp. 
														rewrite (comp_step comp' (Event_receive proc send_event_proc send_event_num)). {
															unfold step. simpl. simpl_step.
															rewrite (n_value comp'). {
																rewrite Hb. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Hmax. rewrite Hp_proc.
																assert (event_process comp b = proc) as Hb_proc. {
																	unfold event_process. rewrite Htl. reflexivity.
																}
																rewrite Hb_proc in Hx_nexists. apply (empty_process comp' proc p).
																{ apply Hx_nexists. }
															} 
														}
													}
													unfold event_timestamps. rewrite Hb0. unfold ge. apply Nat.le_0_l.
												}
											}
											{
												(* p = p', ets b p = ets a' p *)

												(* ets a p > ets a' p*)
												assert (event_timestamps a p > event_timestamps send_event_num p) as Htrans_1. {
													assert (p = event_process comp send_event_num) as Hp_sep. {
														specialize (Hsender_proc (length comp')). unfold sender_proc in Hsender_proc.
														rewrite Hcomp in Hsender_proc. rewrite (nth_middle comp' nil (Event_receive proc send_event_proc send_event_num) (Event 0)) in Hsender_proc.
														rewrite <- Hcomp in Hsender_proc. rewrite Hsender_proc. apply Nat.eqb_eq in Hsend_event_proc. apply Hsend_event_proc.
													}
													(* follows from seq a' a *)
													assert (send_event_num < length comp') as Hsen_bound. {
														specialize (Hsender_prec (length comp')). unfold sender_prec in Hsender_prec.
														rewrite Hcomp in Hsender_prec. rewrite (nth_middle comp' nil (Event_receive proc send_event_proc send_event_num) (Event 0)) in Hsender_prec. apply Hsender_prec.
													}
													apply (seq_timestamps comp send_event_num a p).
													{ lia. }
													{ lia. }
													{ lia. }
													{ apply Hp_sep. }
													{ apply Hsender_prec. }
													{
														unfold seq. split. {
															symmetry. rewrite <- Ha_proc. apply Hp_sep.
														}
														{
															apply Nat.ltb_lt in Hsend_event_num. apply Hsend_event_num.
														}
													}
												}

												(* ets b p = ets a' p + 1*)
												assert (event_timestamps b p = event_timestamps send_event_num p + 1) as Htrans_2. {
													unfold event_timestamps. rewrite Hcomp.
													rewrite (comp_step comp' (Event_receive proc send_event_proc send_event_num)). {
														unfold step. simpl. simpl_step.
														rewrite (n_value comp'). {
															rewrite Hb. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Hmax.
															rewrite Nat.eqb_sym in Hsend_event_proc. rewrite Hsend_event_proc. rewrite orb_true_r.
															specialize (Hsender_prec b). unfold sender_prec in Hsender_prec. rewrite Htl in Hsender_prec. rewrite Hb in Hsender_prec. apply Nat.eqb_eq in Hcomp'.
															apply Nat.lt_neq in Hsender_prec. apply not_eq_sym in Hsender_prec. apply Nat.eqb_neq in Hsender_prec. rewrite Hsender_prec. reflexivity.
														}
													}
												}

												rewrite Htrans_2. unfold ge. rewrite Nat.add_comm. simpl. apply Nat.le_succ_l. apply Htrans_1.

											}
										}
										{
											(* a' > a*)
											assert (seq comp a send_event_num) as Hseq_a_sen. {
												unfold seq. split. {
													specialize (Hsender_proc b). unfold sender_proc in Hsender_proc. rewrite Htl in Hsender_proc. rewrite Hsender_proc. apply Nat.eqb_eq. rewrite <- Ha_proc. apply Hsend_event_proc.
												}
												{
													assert (send_event_num <> a) as Hneq_asen. {
														unfold msg in Hmsg. rewrite Htl in Hmsg. 
														apply not_and_or in Hmsg.
														destruct Hmsg. {
															apply not_eq_sym. apply H.
														}
														{
															specialize (Hsender_proc b). unfold sender_proc in Hsender_proc. rewrite Htl in Hsender_proc. apply H in Hsender_proc. inversion Hsender_proc.
														}
													}
													apply Nat.ltb_ge in Hsend_event_num. apply Nat.lt_eq_cases in Hsend_event_num.
													destruct Hsend_event_num as [Hsen_lt | Hsen_eq]. {
														apply Hsen_lt.
													}
													{
														symmetry in Hsen_eq. apply Hneq_asen in Hsen_eq. inversion Hsen_eq.
													}
												}
											}

											assert (after2 comp send_event_num b) as Hafter2_sen_b. { apply (after_dp2 comp send_event_num b Hmsg_sen_b). }

											assert (exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b) as Hcontra. {
												exists send_event_num.
												split. specialize (Hsender_prec b). unfold sender_prec in Hsender_prec. rewrite Htl in Hsender_prec. lia.
												split. left. apply Hseq_a_sen.
												apply Hafter2_sen_b.
											}

											apply Htrans in Hcontra. inversion Hcontra.

										}
									}
									{
										(* send_event_proc != p *)
										destruct (
											snd (run_computation comp' init_state) send_event_num p <? snd (fst (run_computation comp' init_state)) proc p
										) eqn:Hmax. {

											(* re-used from p = p' case above *)
											assert (
												(exists (x : nat), x < length comp' /\ event_process comp' x = event_process comp b) \/
												~(exists (x : nat), x < length comp' /\ event_process comp' x = event_process comp b)
											) as Hx_exists. { apply classic.  }

											destruct Hx_exists as [Hx_exists | Hx_nexists]. {

												(* exists x, seq x b *) 	(* get rid of pose proof? ===*)
												pose proof ets_fc2 as Hets_fc2. simpl in Hets_fc2. unfold event_timestamps.
												apply (Hets_fc2 comp' (event_process comp b)) in Hx_exists as Hx_exists'.

												(* ets x p = fc' q p *)
												destruct Hx_exists' as [x Hx_exists'].

												(* ets x p = ets b p*)
												assert (
													let event_timestamps : time_stamps :=
														snd (run_computation comp init_state) in
													event_timestamps x p = event_timestamps b p
												) as Hxb. {

													(* fc' q p = fc q p *)
													assert (
														snd (fst (run_computation comp' init_state)) proc p =
														snd (fst (run_computation comp init_state)) proc p
													) as Htrans2. {
														rewrite Hcomp.
														rewrite (comp_step comp' (Event_receive proc send_event_proc send_event_num)). {
															unfold step. simpl. simpl_step. rewrite Nat.eqb_refl. rewrite Hmax. rewrite Hp_proc. reflexivity.
														}
													}

													(* fc q p = ets b p *)
													assert (
														snd (fst (run_computation comp init_state)) proc p =
														snd (run_computation comp init_state) b p
													) as Htrans3. {
														rewrite Hcomp.
														rewrite (comp_step comp' (Event_receive proc send_event_proc send_event_num)). {
															unfold step. simpl. simpl_step. rewrite Nat.eqb_refl. rewrite Hb_val. rewrite Hmax. rewrite Hp_proc. reflexivity.
														}
													}
													destruct Hx_exists as [x0 [Hx_bound Hx_proc]].
													destruct Hx_exists' as [Hx_bound' [Hep_xb Hx_exists']].
													unfold event_process in Hx_exists'. rewrite Htl in Hx_exists'.
													simpl. rewrite <- Htrans3. rewrite <- Htrans2. rewrite <- Hx_exists'. rewrite Hcomp.
													rewrite <- (preserve_ets comp' (Event_receive proc send_event_proc send_event_num) x).
													{ reflexivity. }
													{ apply Hx_bound'. }
												}

												(* ets a p >= ets x p*)
												assert (
													event_timestamps a p >= event_timestamps x p
												) as Hax. {
													(* use IH *)
													(* we know ~ after a x because otherwise, seq x b -> after a b by trans, contra *)
													unfold event_timestamps. rewrite Hcomp.
													rewrite <- (preserve_ets comp' (Event_receive proc send_event_proc send_event_num) a). {
														rewrite <- (preserve_ets comp' (Event_receive proc send_event_proc send_event_num) x). {
															assert (seq comp x b) as Hseq_xb. {
																destruct Hx_exists' as [Hx_bound' [Hep_xb Hx_exists']].
																unfold seq. split. {
																	rewrite (preserve_proc comp' (Event_receive proc send_event_proc send_event_num) x) in Hep_xb. rewrite <- Hcomp in Hep_xb. apply Hep_xb. { lia. }
																}
																{
																	rewrite Hb. apply Hx_bound'.
																}
															}
															apply (IHn comp' Hcomp' a x p).
															{ lia. }
															{ lia. }
															{ lia. }
															{ rewrite (preserve_proc comp' (Event_receive proc send_event_proc send_event_num)).
																rewrite <- Hcomp. apply Ha_proc. { lia. } }
															{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec). }
															{ apply (preserve_sender_proc comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec Hsender_proc). }
															{
																unfold not. intros Hmsg_contra. unfold not in Htrans.
																assert (
																	(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
																) as Hcontra. {
																	exists x. split. { lia. } split. right. { 
																		apply (maintain_msg comp comp' (Event_receive proc send_event_proc send_event_num) a x).
																		{ lia. }
																		{ lia. }
																		{ apply Hcomp. }
																		{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec). }
																		{ apply Hmsg_contra. }
																	}
																	{
																		apply (after_sp2 comp x b Hseq_xb).
																	}
																}
																{
																	apply Htrans in Hcontra. inversion Hcontra.
																}
															}
															{
																unfold not. intros Hseq_contra. unfold not in Htrans.
																assert (
																	(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
																) as Hcontra. {
																	exists x. split. { lia. } split. left. { 
																		apply (maintain_seq comp comp' (Event_receive proc send_event_proc send_event_num) a x).
																		{ lia. }
																		{ lia. }
																		{ apply Hcomp. }
																		{ apply Hseq_contra. }
																	}
																	{
																		apply (after_sp2 comp x b Hseq_xb).
																	}
																}
																{
																	apply Htrans in Hcontra. inversion Hcontra.
																}
															}
															{
																unfold not. intros Htrans_contra. unfold not in Htrans.
																destruct Htrans_contra as [x_contra [Hxc_bound [Haxc_base Hxc_after2]]].
																assert (after2 comp x_contra x) as Hafter2_1. {
																	apply (maintain_after2 comp comp' (Event_receive proc send_event_proc send_event_num) x_contra x).
																	{ lia. }
																	{ lia. }
																	{ apply Hcomp. }
																	{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp). apply Hsender_prec. }
																	{ apply Hxc_after2. }
																}
																assert (after2 comp x b) as Hafter2_2. {
																	apply (after_sp2 comp x b Hseq_xb).
																}
																assert (after2 comp x_contra b) as Hafter2. {
																	apply (after_trans2 comp x_contra x b Hafter2_1 Hafter2_2). { lia. }
																}
																assert (
																	(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
																) as Hcontra. {
																	exists x_contra. split. { lia. } split.
																	destruct Haxc_base as [Haxc_seq | Haxc_msg].
																	{
																		apply (maintain_seq comp comp' (Event_receive proc send_event_proc send_event_num) a x_contra) in Haxc_seq.
																		left. apply Haxc_seq. { lia. } { lia. } { apply Hcomp. }
																	}
																	{
																		apply (maintain_msg comp comp' (Event_receive proc send_event_proc send_event_num) a x_contra) in Haxc_msg.
																		right. apply Haxc_msg. { lia. } { lia. } { apply Hcomp. } {
																			apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp). apply Hsender_prec. (* === bring outside? === *)
																		}
																	}
																	apply (after_trans2 comp x_contra x b Hafter2_1 Hafter2_2). { lia. }
																}
																apply Htrans in Hcontra. inversion Hcontra.
															}
														}
														{ lia. }
													}
													{ lia. }
												}

												simpl in Hxb. simpl in Hax. unfold event_timestamps. rewrite <- Hxb. apply Hax.
											
											}
											{
												(* not exists x, seq x b *)
												(* probably need to use ets_fc2 *)
												(* === aaaaaa === *)

												assert (snd (run_computation comp init_state) b p = 0) as Hb0. {
													rewrite Hcomp. 
													rewrite (comp_step comp' (Event_receive proc send_event_proc send_event_num)). {
														unfold step. simpl. simpl_step.
														rewrite (n_value comp'). {
															rewrite Hb. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Hmax. rewrite Hp_proc.
															assert (event_process comp b = proc) as Hb_proc. {
																unfold event_process. rewrite Htl. reflexivity.
															}
															rewrite Hb_proc in Hx_nexists. apply (empty_process comp' proc p).
															{ apply Hx_nexists. }
														} 
													}
												}
												unfold event_timestamps. rewrite Hb0. unfold ge. apply Nat.le_0_l.
											}
										}

										{
											(* p = p', ets b p = ets a' p *)

											(* ets a p >= ets a' p*)
											assert (send_event_num < length comp') as Hsen_bound. {
												specialize (Hsender_prec (length comp')). unfold sender_prec in Hsender_prec.
												rewrite Hcomp in Hsender_prec. rewrite (nth_middle comp' nil (Event_receive proc send_event_proc send_event_num) (Event 0)) in Hsender_prec. lia.
											}
											assert (event_timestamps a p >= event_timestamps send_event_num p) as Htrans_1. {
												unfold event_timestamps.
												rewrite Hcomp. rewrite <- (preserve_ets comp' (Event_receive proc send_event_proc send_event_num) a). {
													rewrite <- (preserve_ets comp' (Event_receive proc send_event_proc send_event_num) send_event_num). {
														(* redundant === *)
														apply (IHn comp' Hcomp' a send_event_num p).
														{ lia. }
														{ lia. }
														{ lia. }
														{ rewrite (preserve_proc comp' (Event_receive proc send_event_proc send_event_num)).
															rewrite <- Hcomp. apply Ha_proc. { lia. } }
														{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec). }
														{ apply (preserve_sender_proc comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec Hsender_proc). }
														{
															unfold not. intros Hmsg_contra. unfold not in Htrans.
															assert (
																(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
															) as Hcontra. {
																exists send_event_num. split. { lia. } split. right. { 
																	apply (maintain_msg comp comp' (Event_receive proc send_event_proc send_event_num) a send_event_num).
																	{ lia. }
																	{ lia. }
																	{ apply Hcomp. }
																	{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp Hsender_prec). }
																	{ apply Hmsg_contra. }
																}
																{
																	apply (after_dp2 comp send_event_num b Hmsg_sen_b).
																}
															}
															{
																apply Htrans in Hcontra. inversion Hcontra.
															}
														}
														{
															unfold not. intros Hseq_contra. unfold not in Htrans.
															assert (
																(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
															) as Hcontra. {
																exists send_event_num. split. { lia. } split. left. { 
																	apply (maintain_seq comp comp' (Event_receive proc send_event_proc send_event_num) a send_event_num).
																	{ lia. }
																	{ lia. }
																	{ apply Hcomp. }
																	{ apply Hseq_contra. }
																}
																{
																	apply (after_dp2 comp send_event_num b Hmsg_sen_b).
																}
															}
															{
																apply Htrans in Hcontra. inversion Hcontra.
															}
														}
														{
															unfold not. intros Htrans_contra. unfold not in Htrans.
															destruct Htrans_contra as [x_contra [Hxc_bound [Haxc_base Hxc_after2]]].
															assert (after2 comp x_contra send_event_num) as Hafter2_1. {
																apply (maintain_after2 comp comp' (Event_receive proc send_event_proc send_event_num) x_contra send_event_num).
																{ lia. }
																{ lia. }
																{ apply Hcomp. }
																{ apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp). apply Hsender_prec. }
																{ apply Hxc_after2. }
															}
															assert (after2 comp send_event_num b) as Hafter2_2. {
																apply (after_dp2 comp send_event_num b Hmsg_sen_b).
															}
															assert (after2 comp x_contra b) as Hafter2. {
																apply (after_trans2 comp x_contra send_event_num b Hafter2_1 Hafter2_2). { lia. }
															}
															assert (
																(exists x : event_index, x < S (S (S n)) /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)
															) as Hcontra. {
																exists x_contra. split. { lia. } split.
																destruct Haxc_base as [Haxc_seq | Haxc_msg].
																{
																	apply (maintain_seq comp comp' (Event_receive proc send_event_proc send_event_num) a x_contra) in Haxc_seq.
																	left. apply Haxc_seq. { lia. } { lia. } { apply Hcomp. }
																}
																{
																	apply (maintain_msg comp comp' (Event_receive proc send_event_proc send_event_num) a x_contra) in Haxc_msg.
																	right. apply Haxc_msg. { lia. } { lia. } { apply Hcomp. } {
																		apply (preserve_sender_prec comp comp' (Event_receive proc send_event_proc send_event_num) Hcomp). apply Hsender_prec. (* === bring outside? === *)
																	}
																}
																apply (after_trans2 comp x_contra send_event_num b Hafter2_1 Hafter2_2). { lia. }
															}
															apply Htrans in Hcontra. inversion Hcontra.
														}
													}
													{ apply Hsen_bound. }
												}
												{ lia. }
											}

											(* ets b p = ets a' p*)
											assert (event_timestamps b p = event_timestamps send_event_num p) as Htrans_2. {
												unfold event_timestamps. rewrite Hcomp.
												rewrite (comp_step comp' (Event_receive proc send_event_proc send_event_num)). {
													unfold step. simpl. simpl_step.
													rewrite (n_value comp'). {
														rewrite Hb. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. rewrite Hmax.
														rewrite Nat.eqb_sym in Hsend_event_proc. rewrite Hsend_event_proc.
														
														(* === different from above === *)
														rewrite Hp_proc.
														specialize (Hsender_prec b). unfold sender_prec in Hsender_prec. rewrite Htl in Hsender_prec. rewrite Hb in Hsender_prec. apply Nat.eqb_eq in Hcomp'.
														apply Nat.lt_neq in Hsender_prec. apply not_eq_sym in Hsender_prec. apply Nat.eqb_neq in Hsender_prec. rewrite Hsender_prec. simpl. reflexivity.
													}
												}
											}

											rewrite Htrans_2. apply Htrans_1.

										}

									}
								}
							}
						}
						{
							unfold event_timestamps. rewrite Hcomp. rewrite <- (preserve_ets comp' tl a). {
								rewrite <- (preserve_ets comp' tl b). {
									apply (IHn comp' Hcomp' a b).
									{ lia. }
									{ lia. }
									{ lia. }
									{ rewrite (preserve_proc comp' tl).
										rewrite <- Hcomp. apply Ha_proc. { lia. } }
									{ apply (preserve_sender_prec comp comp' tl Hcomp Hsender_prec). }
									{ apply (preserve_sender_proc comp comp' tl Hcomp Hsender_prec Hsender_proc). }
									{
										unfold not. intros Hmsg_contra. unfold not in Hmsg.
										apply (maintain_msg comp comp' tl a b) in Hmsg_contra. apply Hmsg in Hmsg_contra. inversion Hmsg_contra.
										{ lia. }
										{ lia. }
										{ apply Hcomp. }
										{ apply (preserve_sender_prec comp comp' tl Hcomp Hsender_prec). }
									}
									{
										unfold not. intros Hseq_contra. unfold not in Hseq.
										apply (maintain_seq comp comp' tl a b) in Hseq_contra. apply Hseq in Hseq_contra. inversion Hseq_contra.
										{ lia. }
										{ lia. }
										{ apply Hcomp. }
									}
									{
										unfold not. intros Htrans_contra. unfold not in Htrans. rewrite Hcomp' in Htrans_contra.
										apply (maintain_trans comp comp' tl a b) in Htrans_contra. rewrite <- Hlen in Htrans_contra. apply Htrans in Htrans_contra. inversion Htrans_contra.
										{ lia. }
										{ lia. }
										{ apply Hcomp. }
										{ apply (preserve_sender_prec comp comp' tl Hcomp Hsender_prec). }
									}
								}
								{ lia. }
							}
							{ lia. }
						}
					}
				}
			}
		}
Qed.

(* do modus tollens on this *)
Lemma order3:
	forall (comp : computation) (a b : nat) (p : process),
	length comp >= 2 ->
	a < length comp ->
	b < length comp ->
	p = event_process comp a ->
	(forall (i : event_index), sender_prec comp i) ->
	(forall (i : event_index), sender_proc comp i) ->
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	event_timestamps a p < event_timestamps b p ->
	after comp a b.
Proof.
	intros comp a b p Hlen_bound Ha_bound Hb_bound Ha_proc Hsender_prec Hsender_proc event_timestamps Hets. unfold event_timestamps in Hets.
	assert (seq comp a b \/ ~(seq comp a b)) as Hseq. { apply classic. } destruct Hseq.
	- apply (after_sp comp a b H).
	- assert (msg comp a b \/ ~(msg comp a b)) as Hmsg. { apply classic. } destruct Hmsg.
		+ apply (after_dp comp a b H0).
		+ assert (
				(exists (x : event_index), x < length comp /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b) \/
				~(exists (x : event_index), x < length comp /\ (seq comp a x \/ msg comp a x) /\ after2 comp x b)) as Htrans. { apply classic. }
			destruct Htrans. {
				destruct H1 as [x [H1 [H2 H3]]]. apply (after_trans comp a x b).
				{ apply H2. }
				{ apply H3. }
				{ apply H1. }
			}
			{
				(* test a < b for trans_contra, pass trans_contra b a instead for b < a (knock out the equals case here) *)
				assert (event_timestamps a p >= event_timestamps b p) as Hcontra. {
					apply (trans_contra comp a b p Hlen_bound Ha_bound Hb_bound Ha_proc Hsender_prec Hsender_proc H0 H H1).
				}
				unfold event_timestamps in Hcontra. unfold ge in Hcontra. Search le not. apply Nat.lt_nge in Hets. apply Hets in Hcontra. inversion Hcontra.
			}
Qed.

Lemma after_has_basecase:
	forall (comp : computation) (a b : event_index),
	after2 comp a b ->
	seq comp a b \/ msg comp a b \/
	exists (x : event_index), (x < length comp) /\ (seq comp a x \/ msg comp a x) /\ (after2 comp x b).
Proof.
	intros. induction H.
	- left. apply H.
	- right. left. apply H.
	- right. right.
		destruct IHafter2_1 as [Hseq | [Hmsg | Htrans]]. {
			exists b. split.
			{ apply H1. }
			{ split. left. apply Hseq. apply H0. }
		}
		{
			exists b. split.
			{ apply H1. }
			{ split. right. apply Hmsg. apply H0. }
		}
		{
			destruct Htrans as [x Htrans]. exists x. split.
			{ destruct Htrans as [Hbound [Hbase Hind]]. apply Hbound. }
			{ destruct Htrans as [Hbound [Hbase Hind]]. split. apply Hbase.
				apply (after_trans2 comp x b c Hind H0 H1). }
		}
Qed.

Lemma after_eq:
	forall (comp : computation) (a b : event_index),
	after comp a b <-> after2 comp a b.
Proof.
	split.
	- intros. destruct H.
		+ apply (after_sp2 comp a b). apply H.
		+ apply (after_dp2 comp a b). apply H.
		+ assert (after2 comp a b). {
			destruct Htrans1.
			{ apply (after_sp2 comp a b). apply H0. }
			{ apply (after_dp2 comp a b). apply H0. }
		}
		apply (after_trans2 comp a b c H0 Htrans2). apply H.
	- intros. pose proof (after_has_basecase comp a b H). destruct H0 as [Hseq | [Hmsg | Htrans]].
		+ apply (after_sp comp a b Hseq).
		+ apply (after_dp comp a b Hmsg).
		+ destruct Htrans as [x Htrans].
			apply (after_trans comp a x b).
			{ destruct Htrans as [Hbound [Hbase Hind]]. apply Hbase. }
			{ destruct Htrans as [Hbound [Hbase Hind]]. apply Hind. }
			{ destruct Htrans as [Hbound [Hbase Hind]]. apply Hbound. }
Qed.

Theorem order : 
	forall (comp : computation) (a b : event_index) (p : process),
	length comp >= 2 -> (* can remove *)
	a < length comp ->
	b < length comp ->
	p = event_process comp a ->
	(forall (i : event_index), sender_prec comp i) -> (* bundle into 1 well-formedness guarantee *)
	(forall (i : event_index), sender_proc comp i) ->
	after2 comp a b <->
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	event_timestamps a p < event_timestamps b p.
Proof.
	split.
	- intros. apply after_eq in H5. apply (order1 comp a b p H H0 H1 H2 H3 H5).
	- intros. apply after_eq. apply (order3 comp a b p H H0 H1 H2 H3 H4 H5).
Qed.


Definition user := process.
Definition operation_index := nat. (* above needs to replace nat with comp_ind *)
Definition database_operation := event.
Definition database_computation := computation.

Definition database_state := nat. (* arbitrary *)
Definition database_states := user -> database_state.
Definition database_op_states := operation_index -> database_state.

Definition run_op_state := (operation_index * database_states * database_op_states) % type.

Definition apply_op (stop : operation_index) (acc : run_op_state) (op : database_operation) : run_op_state :=
	let op_ind := fst (fst acc) in
	let state := snd (fst acc) in
	let op_states := snd acc in
	match op with
	| Event u | Event_send u =>
		if op_ind =? stop then
		(op_ind + 1, state, op_states)
		else
		let state' := ((state u) + 1) in
		(op_ind + 1, update Nat.eqb state u state', update Nat.eqb op_states op_ind state')
	| Event_receive u s_u _ =>
		if op_ind =? stop then
		(op_ind + 1, state, op_states)
		else
		let state' := ((state u) + (state s_u) + 1) in
		(op_ind + 1, update Nat.eqb state u state', update Nat.eqb op_states op_ind state')
	end.

Definition apply_operations (comp : database_computation) (state : run_op_state) (stop : operation_index) : run_op_state :=
	fold_left (apply_op stop) comp state.

Theorem affects:
	forall (comp : database_computation) (a b : operation_index) (state : database_states),
	length comp >= 2 ->
	a < length comp ->
	b < length comp ->
	after2 comp a b <-> 
	let op_states := snd (apply_operations comp (0, state, fun _ => 0) (length comp)) in
	let op_states_rem_a := snd (apply_operations comp (0, state, fun _ => 0) a) in
	op_states b <> op_states_rem_a b.
Proof.
	Admitted. (* by definition *)

Theorem vclock_preserve:
	forall (comp : database_computation) (a b : operation_index) (p : process) (state : database_states),
	length comp >= 2 ->
	a < length comp ->
	b < length comp ->
	p = event_process comp a ->
	(forall (i : event_index), sender_prec comp i) -> (* bundle into 1 well-formedness guarantee *)
	(forall (i : event_index), sender_proc comp i) ->
	let event_timestamps : time_stamps :=
		snd (run_computation comp init_state) in
	event_timestamps a p < event_timestamps b p <->
	let op_states := snd (apply_operations comp (0, state, fun _ => 0) (length comp)) in
	let op_states_rem_a := snd (apply_operations comp (0, state, fun _ => 0) a) in
	op_states b <> op_states_rem_a b.
Proof.
	intros. split. {
		intros. apply (order comp a b p H H0 H1 H2 H3 H4) in H5.
		apply (affects comp a b state0 H H0 H1) in H5. apply H5.
	}
	{
		intros. apply (order comp a b p H H0 H1 H2 H3 H4).
		apply (affects comp a b state0 H H0 H1) in H5. apply H5.
	}
Admitted.
