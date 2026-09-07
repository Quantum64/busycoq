From BusyCoq Require Import Individual62.
From Coq Require Import String Bool List Arith Lia.
Import List ListNotations.
Open Scope nat_scope.
Set Default Goal Selector "1".

Definition tm : TM := Eval compute in
  TM_from_str "1RB0LF_1LC1LA_1LD0LC_1RE1LB_0RB1RA_---0RD"%string.

Definition machine_state := Q.
Record config := cfg {
  st : machine_state; left : list Sym; scan : Sym; right : list Sym
}.
Definition peek (xs : list Sym) := List.hd S0 xs.
Definition goL q w c := cfg q (List.tl (left c)) (peek (left c)) (w :: right c).
Definition goR q w c := cfg q (w :: left c) (peek (right c)) (List.tl (right c)).

Definition step (c : config) : option config :=
  match tm (st c, scan c) with
  | Some (w, L, q) => Some (goL q w c)
  | Some (w, R, q) => Some (goR q w c)
  | None => None
  end.

Definition blank := cfg A [] S0 [].
Fixpoint advance n c : config :=
  match n with
  | O => c
  | S n => match step c with Some d => advance n d | None => c end
  end.

Lemma advance_halted n c : step c = None -> advance n c = c.
Proof. destruct n; cbn; intro H; [reflexivity | rewrite H; reflexivity]. Qed.

Lemma advance_add n m c : advance (n+m) c = advance m (advance n c).
Proof.
  revert c; induction n as [|n IH]; intro c; cbn; [reflexivity |].
  destruct (step c) eqn:H; [apply IH | symmetry; apply advance_halted; exact H].
Qed.

Definition Progress (a b : config) : Prop :=
  exists n, 0<n /\ advance n a=b.

Lemma progress_trans a b c : Progress a b -> Progress b c -> Progress a c.
Proof.
  intros [n [Hn H1]] [m [Hm H2]].
  exists (n+m); split; [lia | rewrite advance_add,H1; exact H2].
Qed.

Lemma progress_rule n a b a' b' :
  advance n a'=b' -> 0<n -> a=a' -> b'=b -> Progress a b.
Proof. intros H Hn -> <-; exists n; auto. Qed.

Lemma progress_after n a b c : advance n a=b -> Progress b c -> Progress a c.
Proof.
  intros Hbefore [m [Hm Hafter]].
  exists (n+m); split; [lia |rewrite advance_add,Hbefore; exact Hafter].
Qed.

Definition compact_config (c : config) : cconfig :=
  (left c, right c, scan c, st c).
Definition decode (c : config) : Q * tape :=
  cconfig_to_config (compact_config c).

Lemma compact_step c :
  cconfig_step tm (compact_config c) =
  option_map compact_config (step c).
Proof.
  destruct c as [q l b r]; destruct q,b; destruct l,r; reflexivity.
Qed.

Lemma literal_step_sound c d : step c = Some d ->
  decode c -[tm]-> decode d.
Proof.
  intro H.
  pose proof (cconfig_step_spec tm (compact_config c)) as Hstep.
  rewrite compact_step,H in Hstep; exact Hstep.
Qed.

Lemma decode_blank : decode blank = c0.
Proof. reflexivity. Qed.

Lemma advance_evstep n c : decode c -[tm]->* decode (advance n c).
Proof.
  revert c; induction n as [|n IH]; intro c; cbn [advance].
  - constructor.
  - destruct (step c) as [d|] eqn:Hstep.
    + eapply evstep_step; [apply literal_step_sound; exact Hstep|apply IH].
    + constructor.
Qed.

Lemma advance_progress n c : 0<n ->
  step (advance n c) <> None ->
  decode c -[tm]->+ decode (advance n c).
Proof.
  destruct n as [|n]; [lia|].
  intros _ Hlive; cbn [advance] in *.
  destruct (step c) as [d|] eqn:Hstep.
  - eapply progress_intro; [apply literal_step_sound; exact Hstep|apply advance_evstep].
  - contradiction.
Qed.

Fixpoint copies (n : nat) (w : list Sym) : list Sym :=
  match n with O => [] | S n => w ++ copies n w end.

Lemma copies_add n m w : copies (n+m) w = copies n w ++ copies m w.
Proof. induction n; cbn; [reflexivity | rewrite IHn, app_assoc; reflexivity]. Qed.

Lemma copies_slide n w r : copies n w ++ w ++ r = w ++ copies n w ++ r.
Proof.
  induction n; cbn; [reflexivity |].
  repeat rewrite <- app_assoc; rewrite IHn; reflexivity.
Qed.

Lemma copies_succ_end n w : copies (S n) w = copies n w ++ w.
Proof.
  rewrite <- (Nat.add_1_r n), copies_add; cbn; rewrite app_nil_r; reflexivity.
Qed.

Lemma copies_rotate n u v r :
  copies n (u++v) ++ u ++ r = u ++ copies n (v++u) ++ r.
Proof.
  induction n; cbn; [reflexivity |].
  repeat rewrite <- app_assoc; rewrite IHn; reflexivity.
Qed.

Lemma copies_double n w : copies (2*n) w = copies n (w++w).
Proof.
  induction n; cbn [copies]; [reflexivity |].
  replace (2*S n) with (S (S (2*n))) by lia.
  cbn [copies]; rewrite IHn; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma copies_prefix_eq n m w a b : n=m -> a=b ->
  copies n w++a=copies m w++b.
Proof. intros -> ->; reflexivity. Qed.

Lemma copies_prefix_left n m w a b : m<=n ->
  copies (n-m) w++a=b -> copies n w++a=copies m w++b.
Proof.
  intros H Htail; replace n with (m+(n-m)) by lia.
  rewrite copies_add; repeat rewrite <- app_assoc.
  rewrite Htail; reflexivity.
Qed.

Lemma copies_prefix_right n m w a b : n<=m ->
  a=copies (m-n) w++b -> copies n w++a=copies m w++b.
Proof.
  intros H Htail; replace m with (n+(m-n)) by lia.
  rewrite copies_add; repeat rewrite <- app_assoc.
  rewrite Htail; reflexivity.
Qed.

Lemma copies_peel n w r : 0<n ->
  copies n w++r=w++copies (n-1) w++r.
Proof.
  intro H; replace n with (S (n-1)) at 1 by lia.
  cbn [copies]; rewrite <- app_assoc; reflexivity.
Qed.

Lemma d011 l r :
  advance 4 (cfg D l S0 (S1::S1::r)) =
  cfg D (S0::S1::l) S0 r.
Proof. reflexivity. Qed.

Lemma d0six l r :
  advance 12 (cfg D l S0 (S1::S1::S1::S1::S1::S1::r)) =
  cfg D (S0::S1::S0::S1::S0::S1::l) S0 r.
Proof. reflexivity. Qed.

Lemma d0four l r :
  advance 8 (cfg D l S0 (S1::S1::S1::S1::r)) =
  cfg D (S0::S1::S0::S1::l) S0 r.
Proof. reflexivity. Qed.

Lemma d000 l r :
  advance 4 (cfg D l S0 (S0::S0::r)) =
  cfg D l S1 (S1::S1::r).
Proof. reflexivity. Qed.

Lemma empty_left r :
  advance 3 (cfg D [] S1 r) = cfg D [] S0 (S1::S1::S1::r).
Proof. reflexivity. Qed.

Lemma d0101 l r :
  advance 6 (cfg D l S0 (S1::S0::S1::r)) =
  cfg D (S0::S1::l) S0 (S1::r).
Proof. reflexivity. Qed.

Lemma d001 l r :
  advance 7 (cfg D l S0 (S0::S1::r)) =
  cfg D (S0::l) S0 (S1::r).
Proof. reflexivity. Qed.

Lemma d11110 l r :
  advance 4 (cfg D (S0::S1::S0::S1::l) S1 r) =
  cfg D l S1 (S1::S0::S1::S1::r).
Proof. reflexivity. Qed.

Lemma d1gap l r :
  advance 3 (cfg D (S0::S0::S1::l) S1 r) =
  cfg D l S1 (S1::S1::S1::r).
Proof. reflexivity. Qed.

Lemma d0reverse l r :
  advance 8 (cfg D (S0::S1::l) S0 (S1::S0::S0::r)) =
  cfg D l S1 (S1::S0::S0::S0::S1::r).
Proof. reflexivity. Qed.

Lemma left_edge r :
  advance 4 (cfg D [S0;S1] S1 r) =
  cfg D [] S0 (S1::S0::S1::S1::r).
Proof. reflexivity. Qed.

Lemma alternating_left n l r :
  advance (4*n) (cfg D (copies n [S0;S1;S0;S1] ++ l) S1 r) =
  cfg D l S1 (copies n [S1;S0;S1;S1] ++ r).
Proof.
  revert r; induction n as [|n IH]; intro r; cbn [copies]; [reflexivity |].
  replace (4*S n) with (4+4*n) by lia.
  rewrite advance_add; cbn [app]; rewrite d11110, IH.
  f_equal; change (copies n [S1;S0;S1;S1] ++ [S1;S0;S1;S1] ++ r =
                  [S1;S0;S1;S1] ++ copies n [S1;S0;S1;S1] ++ r).
  apply copies_slide.
Qed.

Lemma triple_right_step l r :
  advance 10 (cfg D l S0 (S1::S1::S1::S0::S1::r)) =
  cfg D (S0::S1::S0::S1::l) S0 (S1::r).
Proof. reflexivity. Qed.

Lemma triple_right n l r :
  advance (10*n) (cfg D l S0 (copies n [S1;S1;S1;S0] ++ S1::r)) =
  cfg D (copies n [S0;S1;S0;S1] ++ l) S0 (S1::r).
Proof.
  revert l; induction n as [|n IH]; intro l; cbn [copies]; [reflexivity |].
  replace (10*S n) with (10+10*n) by lia.
  rewrite advance_add; cbn [app].
  destruct n as [|n].
  - cbn [copies app]; rewrite triple_right_step; reflexivity.
  - cbn [copies app] in *.
    rewrite triple_right_step, IH.
    f_equal.
    change ([S0;S1;S0;S1] ++
       copies n [S0;S1;S0;S1] ++ [S0;S1;S0;S1] ++ l =
       [S0;S1;S0;S1] ++ [S0;S1;S0;S1] ++
       copies n [S0;S1;S0;S1] ++ l).
    rewrite copies_slide; reflexivity.
Qed.

Definition K a b r := cfg D [] S0
  ([S1;S0] ++ copies a [S1;S1;S1;S0] ++
   [S1;S1;S1;S1;S1;S1;S0] ++
   copies b [S1;S1;S1;S0] ++ S0::r).

Lemma start_repeat n l r :
  advance 6 (cfg D l S0
    (S1::S0::copies n [S1;S1;S1;S0] ++ S1::r)) =
  cfg D (S0::S1::l) S0
    (copies n [S1;S1;S1;S0] ++ S1::r).
Proof. destruct n; cbn [copies app]; apply d0101. Qed.

Lemma alternating_left_succ n l r :
  advance (4*S n) (cfg D
    (S0::S1::S0::S1::copies n [S0;S1;S0;S1] ++ l) S1 r) =
  cfg D l S1 (copies (S n) [S1;S0;S1;S1] ++ r).
Proof. exact (alternating_left (S n) l r). Qed.

Lemma zero_repeat n l r :
  advance 7 (cfg D l S0
    (S0 :: copies n [S1;S1;S1;S0] ++ S1::r)) =
  cfg D (S0::l) S0 (copies n [S1;S1;S1;S0] ++ S1::r).
Proof. destruct n; cbn [copies app]; apply d001. Qed.

Lemma rotate_Q n r :
  copies n [S1;S0;S1;S1] ++ S1::S0::r =
  S1::S0::copies n [S1;S1;S1;S0] ++ r.
Proof. exact (copies_rotate n [S1;S0] [S1;S1] r). Qed.

Lemma rotate_head n r :
  S1::S1::copies n [S1;S0;S1;S1] ++ r =
  copies n [S1;S1;S1;S0] ++ S1::S1::r.
Proof. symmetry; exact (copies_rotate n [S1;S1] [S1;S0] r). Qed.

Lemma K_successor a b r :
  advance (14*(a+b)+48) (K a (S b) r) = K (S a) b (S0::S1::r).
Proof.
  unfold K at 1.
  rewrite copies_succ_end.
  repeat rewrite <- app_assoc.
  replace (14*(a+b)+48) with
    (6 + (10*a + (12 + (7 + (10*b + (4 + (8 +
      (4*b + (3 + (4*(S a) + 4)))))))))) by lia.
  rewrite advance_add; cbn [app]; rewrite start_repeat.
  rewrite advance_add, triple_right.
  rewrite advance_add, d0six.
  rewrite advance_add, zero_repeat.
  rewrite advance_add, triple_right.
  rewrite advance_add, d011.
  rewrite advance_add, d0reverse.
  rewrite advance_add, alternating_left.
  cbn [copies app].
  rewrite advance_add, d1gap.
  rewrite advance_add, alternating_left_succ.
  rewrite left_edge.
  unfold K; f_equal.
  rewrite rotate_Q, rotate_head; reflexivity.
Qed.

Definition J n r := cfg D [] S0
  ([S1;S1;S1;S1;S0] ++ copies n [S1;S1;S1;S0] ++
   [S1;S1;S1;S1] ++ r).

Lemma padded_word a :
  S0::S1::S0::S1::S0::S1::
    copies a [S0;S1;S0;S1] ++ [S0;S1] =
  copies (S (S a)) [S0;S1;S0;S1].
Proof.
  induction a; [reflexivity |].
  exact (f_equal (fun r : list Sym => S0::S1::S0::S1::r) IHa).
Qed.

Lemma padded_left a r :
  advance (4*(a+2)) (cfg D
    (S0::S1::S0::S1::S0::S1::
      copies a [S0;S1;S0;S1] ++ [S0;S1]) S1 r) =
  cfg D [] S1 (copies (a+2) [S1;S0;S1;S1] ++ r).
Proof.
  rewrite padded_word.
  replace (S (S a)) with (a+2) by lia.
  pose proof (alternating_left (a+2) [] r) as H.
  rewrite app_nil_r in H; exact H.
Qed.

Lemma K_terminal a r :
  advance (14*a+33) (K a 0 r) = J (S a) r.
Proof.
  unfold K.
  cbn [copies app].
  replace (14*a+33) with (6+(10*a+(12+(4+(4*(a+2)+3))))) by lia.
  rewrite advance_add, start_repeat.
  rewrite advance_add, triple_right.
  rewrite advance_add, d0six.
  rewrite advance_add, d000.
  rewrite advance_add, padded_left.
  rewrite empty_left.
  unfold J; f_equal.
  replace (a+2) with (S (S a)) by lia.
  cbn [copies app].
  rewrite rotate_head; reflexivity.
Qed.

Definition phase_clock a b := (b+1)*(14*(a+b)+34)-1.

Lemma K_phase b a r :
  advance (phase_clock a b) (K a b r) =
  J (a+b+1) (copies b [S0;S1] ++ r).
Proof.
  revert a r; induction b as [|b IH]; intros a r.
  - replace (phase_clock a 0) with (14*a+33) by (unfold phase_clock; lia).
    replace (a+0+1) with (S a) by lia.
    cbn [copies app]; apply K_terminal.
  - replace (phase_clock a (S b)) with
      (14*(a+b)+48 + phase_clock (S a) b) by (unfold phase_clock; nia).
    rewrite advance_add, K_successor, IH.
    replace (S a+b+1) with (a+S b+1) by lia.
    change (J (a+S b+1) (copies b [S0;S1] ++ [S0;S1] ++ r) =
            J (a+S b+1) ([S0;S1] ++ copies b [S0;S1] ++ r)).
    rewrite copies_slide; reflexivity.
Qed.

Definition H n r := cfg D
  (copies (S n) [S0;S1;S0;S1] ++ [S0;S0;S1;S0;S1])
  S0 r.

Lemma J_entry n r : advance (10*n+23) (J n r) = H n r.
Proof.
  unfold J.
  replace (10*n+23) with (8+(7+(10*n+8))) by lia.
  rewrite advance_add; cbn [app]; rewrite d0four.
  rewrite advance_add, zero_repeat.
  rewrite advance_add, triple_right.
  rewrite d0four; reflexivity.
Qed.

Lemma alternating_right n l r :
  advance (6*n) (cfg D l S0 (S1::copies n [S0;S1] ++ r)) =
  cfg D (copies n [S0;S1] ++ l) S0 (S1::r).
Proof.
  revert l; induction n as [|n IH]; intro l; cbn [copies app]; [reflexivity |].
  replace (6*S n) with (6+6*n) by lia.
  rewrite advance_add, d0101, IH.
  f_equal.
  change (copies n [S0;S1] ++ [S0;S1] ++ l =
    [S0;S1] ++ copies n [S0;S1] ++ l).
  apply copies_slide.
Qed.

Lemma q_right_step l r :
  advance 10 (cfg D l S0 (S1::S0::S1::S1::S1::r)) =
  cfg D (S0::S1::S0::S1::l) S0 (S1::r).
Proof. reflexivity. Qed.

Lemma q_right n l r :
  advance (10*n) (cfg D l S0
    (copies n [S1;S0;S1;S1] ++ S1::r)) =
  cfg D (copies n [S0;S1;S0;S1] ++ l) S0 (S1::r).
Proof.
  revert l; induction n as [|n IH]; intro l; cbn [copies app]; [reflexivity |].
  replace (10*S n) with (10+10*n) by lia.
  rewrite advance_add.
  destruct n as [|n].
  - cbn [copies app]; rewrite q_right_step; reflexivity.
  - cbn [copies app] in *; rewrite q_right_step, IH.
    f_equal.
    change ([S0;S1;S0;S1] ++ copies n [S0;S1;S0;S1] ++
      [S0;S1;S0;S1] ++ l =
      [S0;S1;S0;S1] ++ [S0;S1;S0;S1] ++
      copies n [S0;S1;S0;S1] ++ l).
    rewrite copies_slide; reflexivity.
Qed.

Lemma odd_turn l r :
  advance 4 (cfg D (S0::S1::S0::S0::S1::S0::S1::l) S1 r) =
  cfg D (S1::S0::S1::l) S0 (S1::S0::S1::S1::r).
Proof. reflexivity. Qed.

Lemma d1double l r :
  advance 5 (cfg D (S0::S1::S1::S0::S1::l) S1 r) =
  cfg D l S1 (S1::S0::S0::S1::S1::r).
Proof. reflexivity. Qed.

Lemma left_finish n r :
  advance (4*n+7) (cfg D
    (copies n [S0;S1;S0;S1] ++ [S0;S0;S1;S0;S1])
    S1 (S1::S0::S0::r)) = K 0 n r.
Proof.
  replace (4*n+7) with (4*n+(3+4)) by lia.
  rewrite advance_add, alternating_left.
  rewrite advance_add, d1gap, left_edge.
  unfold K; cbn [copies app]; f_equal.
  rewrite rotate_Q; reflexivity.
Qed.

Lemma q_right_succ n l r :
  advance (10*S n) (cfg D l S0
    (S1::S0::S1::S1::copies n [S1;S0;S1;S1] ++ S1::r)) =
  cfg D (copies (S n) [S0;S1;S0;S1] ++ l) S0 (S1::r).
Proof. exact (q_right (S n) l r). Qed.

Lemma p_half_slide n r :
  S0::S1::copies n [S0;S1;S0;S1] ++ r =
  copies n [S0;S1;S0;S1] ++ S0::S1::r.
Proof. symmetry; exact (copies_rotate n [S0;S1] [S0;S1] r). Qed.

Lemma double_zero_frontier r :
  advance 19 (cfg D [] S0 (S1::S1::S1::S1::S0::S0::r)) =
  cfg D [] S0 (S1::S1::S1::S1::S0::S1::S1::S1::S1::r).
Proof. reflexivity. Qed.

Inductive block := Three | Six.
Definition block_bits b := match b with
  | Three => [S1;S1;S1;S0]
  | Six => [S1;S1;S1;S1;S1;S1;S0] end.
Definition pushed_bits b := match b with
  | Three => [S0;S1;S0;S1]
  | Six => [S0;S0;S1;S0;S1;S0;S1] end.
Definition returned_bits b := match b with
  | Three => [S1;S0;S1;S1]
  | Six => [S1;S0;S1;S1;S1;S1;S1] end.
Definition right_cost b := match b with Three => 10 | Six => 19 end.
Definition left_cost b := match b with Three => 4 | Six => 7 end.

Fixpoint core_bits w := match w with
  | [] => [] | b::w => block_bits b ++ core_bits w end.
Fixpoint pushed_core w := match w with
  | [] => [] | b::w => pushed_core w ++ pushed_bits b end.
Fixpoint returned_core w := match w with
  | [] => [] | b::w => returned_bits b ++ returned_core w end.
Fixpoint right_clock w := match w with
  | [] => 0 | b::w => right_cost b + right_clock w end.
Fixpoint left_clock w := match w with
  | [] => 0 | b::w => left_cost b + left_clock w end.
Definition weight w := right_clock w + left_clock w.

Lemma core_bits_app u v : core_bits (u++v) = core_bits u ++ core_bits v.
Proof. induction u; cbn; [reflexivity | rewrite IHu, app_assoc; reflexivity]. Qed.

Lemma right_block b w l r :
  advance (right_cost b) (cfg D l S0 (core_bits (b::w) ++ S1::r)) =
  cfg D (pushed_bits b ++ l) S0 (core_bits w ++ S1::r).
Proof. destruct b; destruct w as [|b w]; [reflexivity | destruct b; reflexivity | reflexivity | destruct b; reflexivity]. Qed.

Lemma right_core w l r :
  advance (right_clock w) (cfg D l S0 (core_bits w ++ S1::r)) =
  cfg D (pushed_core w ++ l) S0 (S1::r).
Proof.
  revert l; induction w as [|b w IH]; intro l; [reflexivity |].
  cbn [right_clock]; rewrite advance_add, right_block, IH.
  cbn [pushed_core]; rewrite app_assoc; reflexivity.
Qed.

Lemma left_block b l r :
  advance (left_cost b) (cfg D (pushed_bits b ++ l) S1 r) =
  cfg D l S1 (returned_bits b ++ r).
Proof. destruct b; reflexivity. Qed.

Lemma left_core w l r :
  advance (left_clock w) (cfg D (pushed_core w ++ l) S1 r) =
  cfg D l S1 (returned_core w ++ r).
Proof.
  revert l r; induction w as [|b w IH]; intros l r; [reflexivity |].
  cbn [left_clock pushed_core].
  rewrite Nat.add_comm, advance_add, <- app_assoc, IH, left_block.
  cbn [returned_core]; rewrite app_assoc; reflexivity.
Qed.

Lemma returned_rotation w r :
  returned_core w ++ S1::S0::r = S1::S0::core_bits w ++ r.
Proof.
  induction w as [|b w IH]; [reflexivity |].
  cbn [returned_core]; rewrite <- app_assoc, IH.
  destruct b; cbn [returned_bits core_bits block_bits app]; reflexivity.
Qed.

Definition W w r := cfg D [] S0 (S1::S0::core_bits w ++ S0::r).

Lemma core_start w l r :
  advance 6 (cfg D l S0 (S1::S0::core_bits w ++ S1::r)) =
  cfg D (S0::S1::l) S0 (core_bits w ++ S1::r).
Proof. destruct w as [|b w]; [reflexivity | destruct b; reflexivity]. Qed.

Lemma W_transfer w r :
  advance (weight w+22) (W (w++[Three]) r) = W (Three::w) (S0::S1::r).
Proof.
  unfold W at 1; rewrite core_bits_app; cbn [core_bits block_bits app].
  rewrite <- app_assoc; cbn [app].
  replace (weight w+22) with (6+(right_clock w+(4+(8+(left_clock w+4))))) by
    (unfold weight; lia).
  rewrite advance_add, core_start, advance_add, right_core.
  rewrite advance_add, d011, advance_add, d0reverse.
  rewrite advance_add, left_core, left_edge.
  unfold W; cbn [core_bits block_bits app]; f_equal.
  rewrite returned_rotation; reflexivity.
Qed.

Lemma weight_app u v : weight (u++v) = weight u + weight v.
Proof.
  unfold weight; induction u as [|b u IH]; cbn; [lia |].
  destruct b; cbn in *; lia.
Qed.

Lemma weight_threes n : weight (repeat Three n) = 14*n.
Proof.
  unfold weight; induction n; cbn in *; lia.
Qed.

Lemma weight_cons_three w : weight (Three::w) = 14+weight w.
Proof. unfold weight; cbn; lia. Qed.

Lemma threes_succ_end n : repeat Three (S n) = repeat Three n ++ [Three].
Proof. induction n; cbn; [reflexivity | f_equal; exact IHn]. Qed.

Lemma W_phase n w r :
  advance (n*(weight w+14*n+8)) (W (w++repeat Three n) r) =
  W (repeat Three n++w) (copies n [S0;S1] ++ r).
Proof.
  revert w r; induction n as [|n IH]; intros w r.
  - cbn [repeat copies app]; rewrite app_nil_r; reflexivity.
  - rewrite threes_succ_end, app_assoc.
    replace (S n*(weight w+14*S n+8)) with
      (weight (w++repeat Three n)+22 + n*(weight (Three::w)+14*n+8)) by
      (rewrite weight_app, weight_threes, weight_cons_three; nia).
    rewrite advance_add, W_transfer.
    change (advance (n*(weight (Three::w)+14*n+8))
      (W ((Three::w)++repeat Three n) (S0::S1::r)) =
      W ((repeat Three n++[Three])++w)
        (copies (S n) [S0;S1] ++ r)).
    rewrite IH, <- app_assoc; cbn [app copies].
    pose proof (copies_slide n [S0;S1] r) as Hslide.
    cbn [app] in Hslide; unfold Sym in *; rewrite Hslide; reflexivity.
Qed.

Lemma returned_core_app u v :
  returned_core (u++v) = returned_core u ++ returned_core v.
Proof. induction u; cbn; [reflexivity | rewrite IHu, app_assoc; reflexivity]. Qed.

Lemma core_zero w l r :
  advance 7 (cfg D l S0 (S0::core_bits w ++ S1::r)) =
  cfg D (S0::l) S0 (core_bits w ++ S1::r).
Proof. destruct w as [|b w]; [reflexivity | destruct b; reflexivity]. Qed.

Lemma core_turn w l r :
  advance (weight w+30) (cfg D l S0
    ([S1;S1;S1;S1;S0] ++ core_bits w ++
     [S1;S1;S1;S0;S0;S0] ++ r)) =
  cfg D (S0::S1::l) S1
    (S1::S1::S1::returned_core w ++ S1::S0::S0::S0::S1::S0::r).
Proof.
  replace (weight w+30) with
    (8+(7+(right_clock w+(4+(8+(left_clock w+3)))))) by (unfold weight; lia).
  cbn [app]; rewrite advance_add, d0four, advance_add, core_zero.
  rewrite advance_add, right_core, advance_add, d011, advance_add, d0reverse.
  rewrite advance_add, left_core, d1gap; reflexivity.
Qed.

Definition mixed_word w := Three::Three::w++[Three;Three].
Definition mixed_suffix m w r := copies m [S0;S1] ++
  core_bits (mixed_word w) ++ S0::S0::r.

Lemma mixed_weight w : weight (Three::w++[Three]) = weight w+28.
Proof. rewrite weight_cons_three, weight_app; unfold weight; cbn; lia. Qed.

Lemma J_mixed_turn n m w r :
  advance (10*n+6*m+weight w+88) (J n (mixed_suffix (S m) w r)) =
  cfg D (copies (S m) [S0;S1] ++ S0::copies (S n) [S0;S1;S0;S1] ++
      [S0;S0;S1;S0;S1]) S1
    (S1::S1::S1::returned_core (Three::w++[Three]) ++
      S1::S0::S0::S0::S1::S0::r).
Proof.
  replace (10*n+6*m+weight w+88) with
    ((10*n+23)+(7+(6*m+(weight (Three::w++[Three])+30)))) by
    (rewrite mixed_weight; lia).
  rewrite advance_add, J_entry; unfold H, mixed_suffix, mixed_word.
  cbn [copies app].
  rewrite advance_add, d001, advance_add, alternating_right.
  cbn [core_bits block_bits].
  rewrite core_bits_app; cbn [core_bits block_bits app].
  pose proof (core_turn (Three::w++[Three])
    (copies m [S0;S1] ++ S0::copies (S n) [S0;S1;S0;S1] ++
      [S0;S0;S1;S0;S1]) r) as Hturn.
  cbn [core_bits block_bits copies app] in Hturn.
  rewrite core_bits_app in Hturn; cbn [core_bits block_bits app] in Hturn.
  repeat rewrite <- app_assoc in *; cbn [app] in *; exact Hturn.
Qed.

Lemma right_core_three w l r :
  advance (right_clock (Three::w)) (cfg D l S0
    (S1::S1::S1::S0::core_bits w ++ S1::r)) =
  cfg D (pushed_core (Three::w) ++ l) S0 (S1::r).
Proof. exact (right_core (Three::w) l r). Qed.

Lemma J_mixed_odd n k w r :
  advance (14*n+30*k+2*weight w+162)
    (J n (mixed_suffix (2*k+1) w r)) =
  K 0 n (copies (S k) [S1;S1;S1;S0] ++
    [S1;S1;S1;S1;S1;S1;S0] ++ core_bits (Three::w) ++
    S0::S0::S1::S0::S1::S0::r).
Proof.
  replace (2*k+1) with (S (2*k)) by lia.
  replace (14*n+30*k+2*weight w+162) with
    ((10*n+6*(2*k)+weight w+88)+(4*k+(4+(10*S k+(8+(7+
      (right_clock (Three::w)+(4+(8+(left_clock (Three::w)+
        (3+(4*S k+(5+(4*n+7)))))))))))))) by
    (unfold weight; cbn [right_clock left_clock right_cost left_cost]; lia).
  rewrite advance_add, J_mixed_turn.
  cbn [copies app]; rewrite copies_double, p_half_slide.
  rewrite advance_add, alternating_left, advance_add, odd_turn.
  rewrite advance_add, q_right_succ.
  cbn [returned_core returned_bits app].
  rewrite returned_core_app; cbn [returned_core returned_bits app].
  repeat rewrite <- app_assoc; cbn [app].
  rewrite advance_add, d0four, advance_add, d001.
  rewrite returned_rotation.
  rewrite advance_add, right_core_three, advance_add, d011, advance_add, d0reverse.
  rewrite advance_add, left_core.
  cbn [copies app]; rewrite advance_add, d1gap, p_half_slide.
  rewrite advance_add, alternating_left_succ, advance_add, d1double.
  rewrite left_finish, rotate_head.
  rewrite returned_rotation.
  reflexivity.
Qed.

Definition mixed_even_result n k w r := cfg D [] S0
  ([S1;S1;S1;S1;S0;S0] ++ copies (S n) [S1;S1;S1;S0] ++
   [S1;S1;S1;S1;S1;S1;S0] ++ copies k [S1;S1;S1;S0] ++
   [S1;S1;S1;S1;S1;S1;S0] ++ core_bits (Three::w) ++
   S0::S0::S1::S0::S1::S0::r).

Lemma J_mixed_even n k w r :
  advance (28*n+30*k+2*weight w+197)
    (J n (mixed_suffix (2*k+2) w r)) = mixed_even_result n k w r.
Proof.
  replace (2*k+2) with (S (S (2*k))) by lia.
  replace (28*n+30*k+2*weight w+197) with
    ((10*n+6*S (2*k)+weight w+88)+(4*S k+(3+(4*n+(4+(10*S n+
      (8+(7+(10*k+(12+(7+(right_clock (Three::w)+(4+(8+
        (left_clock (Three::w)+(3+(4*S k+(3+(4*S n+(5+3)))))))))))))))))))) by
    (unfold weight; cbn [right_clock left_clock right_cost left_cost]; lia).
  rewrite advance_add, J_mixed_turn.
  cbn [copies app]; rewrite copies_double.
  rewrite advance_add, alternating_left_succ, advance_add, d1gap, p_half_slide.
  rewrite advance_add, alternating_left, advance_add, odd_turn.
  rewrite advance_add, q_right_succ.
  cbn [copies returned_core returned_bits app].
  rewrite returned_core_app; cbn [returned_core returned_bits app].
  repeat rewrite <- app_assoc; cbn [app].
  rewrite advance_add, d0four, advance_add, d001, rotate_head.
  rewrite advance_add, triple_right, advance_add, d0six, advance_add, d001.
  rewrite returned_rotation.
  rewrite advance_add, right_core_three, advance_add, d011, advance_add, d0reverse.
  rewrite advance_add, left_core, advance_add, d1gap.
  rewrite advance_add, alternating_left_succ.
  cbn [copies app]; rewrite advance_add, d1gap, p_half_slide.
  rewrite advance_add, alternating_left_succ, advance_add, d1double, empty_left.
  unfold mixed_even_result; f_equal.
  rewrite rotate_head; cbn [app].
  rewrite rotate_head, returned_rotation; reflexivity.
Qed.

Definition G a r := cfg D [] S0
  ([S1;S1;S1;S1;S0] ++ copies (S a) [S1;S1;S1;S0] ++ S0::r).

Lemma G_entry a r : advance (14*a+34) (G a r) = K 0 a (S0::S1::r).
Proof.
  unfold G; rewrite copies_succ_end.
  repeat rewrite <- app_assoc; cbn [app].
  replace (14*a+34) with (8+(7+(10*a+(4+(8+(4*a+(3+4))))))) by lia.
  rewrite advance_add, d0four, advance_add, zero_repeat.
  rewrite advance_add, triple_right, advance_add, d011, advance_add, d0reverse.
  rewrite advance_add, alternating_left, advance_add, d1gap, left_edge.
  unfold K; cbn [copies app]; f_equal; rewrite rotate_Q; reflexivity.
Qed.

Lemma G_phase a r :
  advance ((a+2)*(14*a+34)-1) (G a r) =
  J (S a) (copies (S a) [S0;S1] ++ r).
Proof.
  replace ((a+2)*(14*a+34)-1) with (14*a+34+phase_clock 0 a) by
    (unfold phase_clock; nia).
  rewrite advance_add, G_entry, K_phase.
  cbn [Nat.add copies app].
  replace (0+a+1) with (S a) by lia.
  replace (a+1) with (S a) by lia.
  pose proof (copies_slide a [S0;S1] r) as Hslide.
  cbn [app] in Hslide; unfold Sym in *; rewrite Hslide; reflexivity.
Qed.

Lemma B_start w l r :
  advance 33 (cfg D l S0
    ([S1;S1;S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S0] ++
     core_bits w ++ S1::r)) =
  cfg D ([S0;S1;S0;S1;S0;S1;S0;S1;S0;S0;S1;S0;S1] ++ l)
    S0 (core_bits w ++ S1::r).
Proof. destruct w as [|b w]; [reflexivity | destruct b; reflexivity]. Qed.

Lemma B_transfer w r :
  advance (weight w+60)
    (J 0 (core_bits (Three::w++[Three]) ++ S0::S0::r)) =
  W (Six::Three::Three::w) (S0::S1::S0::r).
Proof.
  unfold J; cbn [copies core_bits block_bits app].
  rewrite core_bits_app; cbn [core_bits block_bits app].
  repeat rewrite <- app_assoc; cbn [app].
  replace (weight w+60) with (33+(right_clock w+(4+(8+(left_clock w+(8+(3+4))))))) by
    (unfold weight; lia).
  rewrite advance_add.
  pose proof (B_start w []
    (S1::S1::S0::S0::S0::r)) as Hstart.
  cbn [app] in Hstart; rewrite Hstart.
  rewrite advance_add, right_core, advance_add, d011, advance_add, d0reverse.
  rewrite advance_add, left_core.
  change (advance (8+(3+4)) (cfg D
    (copies 2 [S0;S1;S0;S1] ++ [S0;S0;S1;S0;S1]) S1
    (returned_core w ++ S1::S0::S0::S0::S1::S0::r)) =
    W (Six::Three::Three::w) (S0::S1::S0::r)).
  rewrite advance_add, (alternating_left 2), advance_add, d1gap, left_edge.
  cbn [copies app]; rewrite returned_rotation; reflexivity.
Qed.

Lemma core_bits_threes n : core_bits (repeat Three n) =
  copies n [S1;S1;S1;S0].
Proof. induction n; cbn; [reflexivity | rewrite IHn; reflexivity]. Qed.

Definition tilted w n r := cfg D
  ([S0;S1] ++ copies (n+2) [S0;S1;S0;S1] ++
   [S1;S0;S1;S0;S1] ++ pushed_core w ++ [S0;S1]) S0 r.

Lemma W_multi_six w n r :
  advance (right_clock w+24*n+73)
    (W (w++Six::repeat Three n++[Six]) r) = tilted w n r.
Proof.
  unfold W; rewrite core_bits_app; cbn [core_bits block_bits app].
  rewrite core_bits_app; cbn [core_bits block_bits app].
  rewrite core_bits_threes.
  replace (right_clock w+24*n+73) with
    (6+(right_clock w+(12+(7+(10*n+(12+(4+(4*S n+
      (4+(10*(n+2)+4)))))))))) by lia.
  repeat rewrite <- app_assoc; cbn [app].
  rewrite advance_add, core_start, advance_add, right_core.
  rewrite advance_add, d0six.
  repeat rewrite <- app_assoc; cbn [app].
  rewrite advance_add, zero_repeat, advance_add, triple_right.
  rewrite advance_add, d0six, advance_add, d000.
  rewrite p_half_slide.
  rewrite advance_add, alternating_left_succ, advance_add, odd_turn.
  replace (n+2) with (S (S n)) by lia.
  rewrite advance_add, q_right_succ, d011.
  unfold tilted; replace (n+2) with (S (S n)) by lia; reflexivity.
Qed.

Lemma right_clock_app u v : right_clock (u++v) = right_clock u+right_clock v.
Proof. induction u; cbn; [lia | rewrite IHu; lia]. Qed.

Lemma right_clock_threes n : right_clock (repeat Three n) = 10*n.
Proof. induction n; cbn in *; lia. Qed.

Lemma two_six_weight w n :
  weight (w++Six::repeat Three n++[Six]) = weight w+14*n+52.
Proof.
  rewrite weight_app.
  change (weight w+weight ([Six]++repeat Three n++[Six]) = weight w+14*n+52).
  rewrite !weight_app, weight_threes.
  assert (Hsix : weight [Six] = 26) by reflexivity.
  rewrite Hsix; lia.
Qed.

Lemma W_multi_six_phase w n b r :
  advance (b*(weight w+14*(n+b)+60)+right_clock w+10*b+24*n+73)
    (W ((w++Six::repeat Three n++[Six])++repeat Three b) r) =
  tilted (repeat Three b++w) n (copies b [S0;S1] ++ r).
Proof.
  replace (b*(weight w+14*(n+b)+60)+right_clock w+10*b+24*n+73) with
    (b*(weight (w++Six::repeat Three n++[Six])+14*b+8)+
      (right_clock (repeat Three b++w)+24*n+73)) by
    (rewrite two_six_weight, right_clock_app, right_clock_threes; nia).
  rewrite advance_add, W_phase.
  rewrite app_assoc, W_multi_six; reflexivity.
Qed.

Definition page w := [S1;S1;S1;S1;S0] ++ core_bits w ++ [S0;S0].
Definition carried w r := cfg D
  (S0::S0::S1::pushed_core w ++ [S0;S1]) S0 r.

Lemma d1_101 l r :
  advance 6 (cfg D (S1::S0::S1::l) S1 r) =
  cfg D (S0::l) S0 (S1::S1::r).
Proof. reflexivity. Qed.

Lemma core_turn_head v l r :
  advance (weight v+30) (cfg D l S0
    (S1::S1::S1::S1::S0::core_bits v ++
      S1::S1::S1::S0::S0::r)) =
  cfg D (S0::S1::l) S1
    (S1::S1::S1::returned_core v ++ S1::S0::S0::S0::S1::r).
Proof.
  replace (weight v+30) with
    (8+(7+(right_clock v+(4+(8+(left_clock v+3)))))) by (unfold weight; lia).
  rewrite advance_add, d0four, advance_add, core_zero.
  rewrite advance_add, right_core, advance_add, d011, advance_add, d0reverse.
  rewrite advance_add, left_core, d1gap; reflexivity.
Qed.

Definition core_suffix m v r := copies m [S0;S1] ++
  core_bits (Three::v++[Three]) ++ S0::r.

Lemma T_core_turn w n m v r :
  advance (6*m+weight v+37) (tilted w n (core_suffix (S m) v r)) =
  cfg D (copies (S m) [S0;S1] ++
      S0::S0::S1::copies (n+2) [S0;S1;S0;S1] ++
      [S1;S0;S1;S0;S1] ++ pushed_core w ++ [S0;S1]) S1
    (S1::S1::S1::returned_core v ++ S1::S0::S0::S0::S1::r).
Proof.
  replace (6*m+weight v+37) with (7+(6*m+(weight v+30))) by lia.
  unfold tilted, core_suffix; cbn [copies core_bits block_bits app].
  rewrite core_bits_app; cbn [core_bits block_bits app].
  repeat rewrite <- app_assoc; cbn [app].
  rewrite advance_add, d001, advance_add, alternating_right.
  apply core_turn_head.
Qed.

Lemma T_core_even w n m v r :
  advance (4*n+16*m+weight v+64)
    (tilted w n (core_suffix (2*m+2) v r)) =
  carried w (copies (n+2) [S1;S1;S1;S0] ++
    [S1;S1;S1;S1;S1;S1;S0] ++ copies m [S1;S1;S1;S0] ++
    [S1;S1;S1;S1;S1;S1;S0] ++ core_bits v ++
    S0::S0::S1::r).
Proof.
  replace (2*m+2) with (S (S (2*m))) by lia.
  replace (4*n+16*m+weight v+64) with
    ((6*S (2*m)+weight v+37)+(4*S m+(3+(4*(n+2)+6)))) by lia.
  rewrite advance_add, T_core_turn.
  cbn [copies app]; rewrite copies_double.
  rewrite advance_add, alternating_left_succ, advance_add, d1gap.
  rewrite advance_add, alternating_left, d1_101.
  unfold carried; f_equal.
  rewrite rotate_head; cbn [copies app].
  rewrite rotate_head, returned_rotation; reflexivity.
Qed.

Lemma T_core_odd_turn w n m v r :
  advance (4*n+30*m+2*weight v+113)
    (tilted w n (core_suffix (2*m+1) (v++[Three]) r)) =
  cfg D (S0::S1::pushed_core w ++ [S0;S1]) S1
    ([S1;S0;S0;S1;S1] ++ copies (S n) [S1;S0;S1;S1] ++
     [S1;S0;S0;S1;S1] ++ copies (S m) [S1;S0;S1;S1] ++
     S1::S1::S1::returned_core v ++
     S1::S0::S0::S0::S1::S0::S1::r).

Proof.
  replace (2*m+1) with (S (2*m)) by lia.
  replace (4*n+30*m+2*weight v+113) with
    ((6*(2*m)+weight (v++[Three])+37)+(4*m+(4+(10*S m+
      ((weight v+30)+(4*S m+(5+(4*S n+5)))))))) by
    (rewrite weight_app; assert (weight [Three]=14) by reflexivity; nia).
  rewrite advance_add, T_core_turn.
  cbn [copies app]; rewrite copies_double, p_half_slide.
  rewrite advance_add, alternating_left.
  replace (n+2) with (S (S n)) by lia; cbn [copies app].
  rewrite advance_add, odd_turn, advance_add, q_right_succ.
  rewrite returned_core_app; cbn [returned_core returned_bits app].
  repeat rewrite <- app_assoc; cbn [app].
  rewrite returned_rotation, advance_add, core_turn_head.
  rewrite p_half_slide, advance_add, alternating_left, advance_add, d1double.
  rewrite p_half_slide, advance_add, alternating_left_succ, d1double.
  reflexivity.
Qed.

Lemma pushed_core_app u v : pushed_core (u++v) = pushed_core v ++ pushed_core u.
Proof.
  induction u; cbn; [rewrite app_nil_r; reflexivity |].
  rewrite IHu, app_assoc; reflexivity.
Qed.

Lemma left_clock_app u v : left_clock (u++v) = left_clock u+left_clock v.
Proof. induction u; cbn; [lia | rewrite IHu; lia]. Qed.

Lemma carried_return u v r :
  advance (weight v+left_clock u+23)
    (carried (u++[Three]) (core_bits (v++[Three]) ++ S0::r)) =
  W (Three::u++Six::v) (S0::S1::r).
Proof.
  replace (weight v+left_clock u+23) with
    (right_clock v+(4+(8+(left_clock v+(3+(left_clock (u++[Three])+4)))))) by
    (rewrite left_clock_app; unfold weight; cbn [left_clock left_cost]; lia).
  unfold carried; rewrite core_bits_app; cbn [core_bits block_bits app].
  repeat rewrite <- app_assoc; cbn [app].
  rewrite advance_add, right_core, advance_add, d011, advance_add, d0reverse.
  rewrite advance_add, left_core, advance_add, d1gap.
  rewrite advance_add, left_core, left_edge.
  rewrite returned_core_app; cbn [returned_core returned_bits app].
  repeat rewrite <- app_assoc; cbn [app].
  rewrite !returned_rotation.
  unfold W; cbn [core_bits block_bits app].
  rewrite core_bits_app; cbn [core_bits block_bits app].
  repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma core_multi_six v n l r :
  advance (right_clock v+24*n+67)
    (cfg D l S0 (core_bits (v++Six::repeat Three n++[Six]) ++ S0::r)) =
  cfg D ([S0;S1] ++ copies (n+2) [S0;S1;S0;S1] ++
    [S1;S0;S1;S0;S1] ++ pushed_core v ++ l) S0 r.
Proof.
  rewrite core_bits_app; cbn [core_bits block_bits app].
  rewrite core_bits_app, core_bits_threes; cbn [core_bits block_bits app].
  replace (right_clock v+24*n+67) with
    (right_clock v+(12+(7+(10*n+(12+(4+(4*S n+(4+(10*(n+2)+4))))))))) by lia.
  repeat first [progress cbn [app] | rewrite <- app_assoc].
  rewrite advance_add, right_core, advance_add, d0six.
  repeat first [progress cbn [app] | rewrite <- app_assoc].
  rewrite advance_add, zero_repeat, advance_add, triple_right.
  rewrite advance_add, d0six, advance_add, d000, p_half_slide.
  rewrite advance_add, alternating_left_succ, advance_add, odd_turn.
  replace (n+2) with (S (S n)) by lia.
  rewrite advance_add, q_right_succ, d011; reflexivity.
Qed.

Lemma carried_six u v n r :
  advance (right_clock v+24*n+67)
    (carried (u++[Three]) (core_bits (v++Six::repeat Three n++[Six]) ++ S0::r)) =
  tilted (u++Six::v) n r.
Proof.
  unfold carried; rewrite core_multi_six.
  unfold tilted; rewrite !pushed_core_app; cbn [pushed_core pushed_bits app].
  repeat first [progress cbn [app] | rewrite <- app_assoc].
  reflexivity.
Qed.

Definition page_core n m v := repeat Three (n+2) ++ Six::repeat Three m ++ Six::v.

Lemma page_core_weight n m v : weight (page_core n m v) =
  14*n+14*m+weight v+80.
Proof.
  unfold page_core.
  change (weight (repeat Three (n+2) ++ [Six] ++ repeat Three m ++ [Six] ++ v) = 14*n+14*m+weight v+80).
  rewrite !weight_app, !weight_threes.
  assert (Hsix : weight [Six] = 26) by reflexivity; rewrite Hsix; lia.
Qed.

Lemma page_core_bits n m v : core_bits (page_core n m v) =
  copies (n+2) [S1;S1;S1;S0] ++ [S1;S1;S1;S1;S1;S1;S0] ++
  copies m [S1;S1;S1;S0] ++ [S1;S1;S1;S1;S1;S1;S0] ++ core_bits v.
Proof.
  unfold page_core; rewrite core_bits_app, core_bits_threes.
  cbn [core_bits block_bits]; rewrite core_bits_app, core_bits_threes; reflexivity.
Qed.

Lemma T_core_even_return u n m v r :
  advance (18*n+30*m+2*weight v+left_clock u+181)
    (tilted (u++[Three]) n (core_suffix (2*m+2) (v++[Three]) r)) =
  W (Three::u++Six::page_core n m v) (S0::S1::S0::S1::r).
Proof.
  replace (18*n+30*m+2*weight v+left_clock u+181) with
    ((4*n+16*m+weight (v++[Three])+64)+(weight (page_core n m v)+left_clock u+23)) by
    (rewrite weight_app, page_core_weight;
      assert (weight [Three]=14) by reflexivity; nia).
  rewrite advance_add, T_core_even.
  pose proof (carried_return u (page_core n m v) (S0::S1::r)) as Hreturn.
  rewrite core_bits_app, page_core_bits in Hreturn.
  cbn [core_bits block_bits app] in Hreturn.
  rewrite core_bits_app; cbn [core_bits block_bits app].
  repeat first [progress cbn [app] in * | rewrite <- app_assoc in *].
  exact Hreturn.
Qed.

Definition page_outer u n := Three::u++Six::repeat Three (n+2).

Lemma page_outer_weight u n : weight (page_outer u n) = weight u+14*n+68.
Proof.
  unfold page_outer.
  change (weight ([Three]++u++[Six]++repeat Three (n+2)) = weight u+14*n+68).
  rewrite !weight_app, weight_threes.
  assert (weight [Three]=14) by reflexivity; assert (weight [Six]=26) by reflexivity; lia.
Qed.

Lemma page_outer_clock u n : right_clock (page_outer u n) = right_clock u+10*n+49.
Proof.
  unfold page_outer.
  change (right_clock ([Three]++u++[Six]++repeat Three (n+2)) = right_clock u+10*n+49).
  rewrite !right_clock_app, right_clock_threes; cbn [right_clock right_cost]; lia.
Qed.

Lemma T_page_consume u n m b r :
  advance (b*(weight u+14*(n+m+b)+128)+weight u+28*n+54*m+38*b+303)
    (tilted (u++[Three]) n
      (core_suffix (2*m+2) (repeat Three b++[Three]) r)) =
  tilted (repeat Three b++page_outer u n) m
    (copies b [S0;S1] ++ S0::S1::S0::S1::r).
Proof.
  replace (b*(weight u+14*(n+m+b)+128)+weight u+28*n+54*m+38*b+303) with
    ((18*n+30*m+2*weight (repeat Three b)+left_clock u+181)+
      (b*(weight (page_outer u n)+14*(m+b)+60)+right_clock (page_outer u n)+10*b+24*m+73)) by
    (rewrite weight_threes, page_outer_weight, page_outer_clock; unfold weight; nia).
  rewrite advance_add, T_core_even_return.
  pose proof (W_multi_six_phase (page_outer u n) m b (S0::S1::S0::S1::r)) as Hphase.
  unfold page_outer, page_core in *.
  repeat first [progress cbn [app] in * | rewrite <- app_assoc in *].
  exact Hphase.
Qed.

Lemma pure_page_form p b r :
  core_suffix (S p) (repeat Three b++[Three]) r =
  copies p [S0;S1] ++ [S0;S1;S1;S1;S1;S0] ++
    copies (b+2) [S1;S1;S1;S0] ++ S0::r.
Proof.
  unfold core_suffix; rewrite (copies_succ_end p [S0;S1]).
  cbn [core_bits block_bits].
  rewrite !core_bits_app, core_bits_threes.
  rewrite (copies_add b 2 [S1;S1;S1;S0]).
  repeat first [progress cbn [core_bits block_bits copies app] | rewrite <- app_assoc].
  reflexivity.
Qed.

Lemma T_odd_page u n m b r :
  advance (b*(weight u+14*(n+m+b)+128)+weight u+28*n+54*m+38*b+303)
    (tilted (u++[Three]) n
      (copies (2*m+1) [S0;S1] ++ [S0;S1;S1;S1;S1;S0] ++
        copies (b+2) [S1;S1;S1;S0] ++ S0::r)) =
  tilted (repeat Three (S b)++u++Six::repeat Three (n+2)) m
    (copies (b+2) [S0;S1] ++ r).
Proof.
  rewrite <- pure_page_form.
  replace (S (2*m+1)) with (2*m+2) by lia.
  rewrite T_page_consume.
  unfold page_outer; rewrite threes_succ_end, (copies_add b 2 [S0;S1]).
  repeat first [progress cbn [copies app] | rewrite <- app_assoc].
  reflexivity.
Qed.

Lemma T_page_one u n m r :
  advance (14*n+40*m+151)
    (tilted (u++[Three]) n (core_suffix (2*m+2) [] r)) =
  tilted (u++Six::repeat Three (n+2)) m (S0::S1::r).
Proof.
  replace (14*n+40*m+151) with
    ((4*n+16*m+weight []+64)+(right_clock (repeat Three (n+2))+24*m+67)) by
    (rewrite right_clock_threes; assert (weight []=0) by reflexivity; lia).
  rewrite advance_add, T_core_even; cbn [core_bits].
  pose proof (carried_six u (repeat Three (n+2)) m (S0::S1::r)) as H.
  rewrite core_bits_app, core_bits_threes in H.
  cbn [core_bits block_bits] in H; rewrite core_bits_app, core_bits_threes in H.
  repeat first [progress cbn [core_bits block_bits app] in * | rewrite <- app_assoc in *].
  exact H.
Qed.

Lemma positive_page_form p c r :
  core_suffix (S p) (repeat Three c) r =
  copies p [S0;S1] ++ [S0;S1;S1;S1;S1;S0] ++
    copies (S c) [S1;S1;S1;S0] ++ S0::r.
Proof.
  unfold core_suffix; rewrite (copies_succ_end p [S0;S1]).
  cbn [core_bits block_bits]; rewrite core_bits_app, core_bits_threes.
  rewrite (copies_succ_end c [S1;S1;S1;S0]).
  repeat first [progress cbn [core_bits block_bits app] | rewrite <- app_assoc].
  reflexivity.
Qed.

Definition page_clock u n m c := (c-1)*weight u + 14*c*n+(14*c+26)*m+
  14*c*c+110*c+27.

Lemma page_clock_ge2 u n m b : page_clock u n m (b+2) =
  b*(weight u+14*(n+m+b)+128)+weight u+28*n+54*m+38*b+303.
Proof. unfold page_clock; replace (b+2-1) with (b+1) by lia; nia. Qed.

Lemma T_positive_page u n m c r : 0 < c ->
  advance (page_clock u n m c)
    (tilted (u++[Three]) n
      (copies (2*m+1) [S0;S1] ++ [S0;S1;S1;S1;S1;S0] ++
        copies c [S1;S1;S1;S0] ++ S0::r)) =
  tilted (repeat Three (c-1)++u++Six::repeat Three (n+2)) m
    (copies c [S0;S1] ++ r).
Proof.
  intro Hc; destruct c as [|c]; [lia |].
  destruct c as [|c].
  - replace (page_clock u n m 1) with (14*n+40*m+151) by
      (unfold page_clock; nia).
    rewrite <- (positive_page_form (2*m+1) 0 r).
    replace (S (2*m+1)) with (2*m+2) by lia.
    cbn [repeat Nat.sub copies app]; apply T_page_one.
  - replace (S (S c)) with (c+2) by lia.
    rewrite page_clock_ge2; replace (c+2-1) with (S c) by lia.
    apply T_odd_page.
Qed.

Definition short_frame w n m r := cfg D
  (S0::S0::S1::copies (S n) [S0;S1;S0;S1] ++
    [S1;S0;S1;S0;S1] ++ pushed_core w ++ [S0;S1]) S0
  (copies (m+2) [S1;S1;S1;S0] ++ [S1;S1;S1;S1;S0;S1] ++ r).

Lemma T_short_turn w n m r :
  advance (30*m+77) (tilted w n (core_suffix (2*m+1) [] r)) =
  short_frame w n m r.
Proof.
  replace (2*m+1) with (S (2*m)) by lia.
  replace (30*m+77) with
    ((6*(2*m)+weight []+37)+(4*m+(4+(10*S m+(8+(4+(4*(m+2)+6))))))) by
    (assert (weight []=0) by reflexivity; lia).
  rewrite advance_add, T_core_turn.
  cbn [copies app]; rewrite copies_double, p_half_slide.
  rewrite advance_add, alternating_left.
  replace (n+2) with (S (S n)) by lia; cbn [copies app].
  rewrite advance_add, odd_turn, advance_add, q_right_succ.
  cbn [returned_core app]; rewrite advance_add, d0four, advance_add, d000.
  replace (m+2) with (S (S m)) by lia.
  rewrite advance_add, alternating_left_succ, d1_101.
  unfold short_frame; replace (m+2) with (S (S m)) by lia.
  f_equal; rewrite rotate_head; reflexivity.
Qed.

Lemma pushed_threes n : pushed_core (repeat Three n) =
  copies n [S0;S1;S0;S1].
Proof.
  induction n; cbn [repeat pushed_core pushed_bits]; [reflexivity |].
  rewrite IHn, copies_succ_end; reflexivity.
Qed.

Lemma half_six w b r :
  advance (18*b+27)
    (cfg D (S0::S1::pushed_core (w++Six::repeat Three b) ++ [S0;S1])
      S1 (S1::S0::S0::S1::S1::r)) =
  cfg D (S0::S1::pushed_core w ++ [S0;S1]) S1
    ([S1;S0;S0;S1;S1] ++ copies b [S1;S0;S1;S1] ++
      S1::S0::S0::S0::S1::S1::S1::r).
Proof.
  rewrite pushed_core_app; cbn [pushed_core pushed_bits].
  rewrite pushed_threes; repeat rewrite <- app_assoc; cbn [app].
  replace (18*b+27) with (4*b+(4+(10*S b+(8+(4*b+5))))) by lia.
  rewrite p_half_slide, advance_add, alternating_left, advance_add, odd_turn.
  rewrite advance_add, q_right_succ.
  cbn [copies app]; rewrite advance_add, d0reverse.
  rewrite p_half_slide, advance_add, alternating_left, d1double; reflexivity.
Qed.

Fixpoint row a gaps := match gaps with
  | [] => repeat Three a
  | b::gaps => row a gaps ++ Six::repeat Three b end.
Fixpoint packet gaps r := match gaps with
  | [] => r
  | b::gaps => packet gaps (copies b [S1;S0;S1;S1] ++
      S1::S0::S0::S0::S1::S1::S1::r) end.
Fixpoint row_clock a gaps := match gaps with
  | [] => 4*a+7
  | b::gaps => 18*b+27+row_clock a gaps end.

Lemma half_row a gaps r :
  advance (row_clock a gaps)
    (cfg D (S0::S1::pushed_core (row a gaps) ++ [S0;S1])
      S1 (S1::S0::S0::S1::S1::r)) =
  G a (S1::S1::packet gaps r).
Proof.
  revert r; induction gaps as [|b gaps IH]; intro r.
  - cbn [row row_clock packet]; rewrite pushed_threes.
    rewrite p_half_slide.
    change (advance (4*a+7) (cfg D
      (copies a [S0;S1;S0;S1] ++ [S0;S1;S0;S1]) S1
      (S1::S0::S0::S1::S1::r)) = G a (S1::S1::r)).
    rewrite <- copies_succ_end.
    replace (4*a+7) with (4*S a+3) by lia.
    rewrite advance_add.
    pose proof (alternating_left (S a) [] (S1::S0::S0::S1::S1::r)) as Hleft.
    rewrite app_nil_r in Hleft; rewrite Hleft, empty_left.
    unfold G; cbn [copies app].
    rewrite rotate_head.
    pose proof (copies_slide a [S1;S1;S1;S0] (S0::S1::S1::r)) as Hslide.
    cbn [app] in Hslide; unfold Sym in *; rewrite Hslide; reflexivity.
  - cbn [row row_clock packet].
    rewrite advance_add, half_six.
    cbn [app]; apply IH.
Qed.

Lemma T_core_odd_row a gaps n m v r :
  advance (4*n+30*m+2*weight v+113+row_clock a gaps)
    (tilted (row a gaps) n (core_suffix (2*m+1) (v++[Three]) r)) =
  G a (S1::S1::packet gaps
    (copies (S n) [S1;S0;S1;S1] ++
     [S1;S0;S0;S1;S1] ++ copies (S m) [S1;S0;S1;S1] ++
     S1::S1::S1::returned_core v ++
     S1::S0::S0::S0::S1::S0::S1::r)).
Proof.
  rewrite advance_add, T_core_odd_turn.
  cbn [app]; apply half_row.
Qed.

Lemma q_gap n r :
  S1::S1::S1::copies (S n) [S1;S0;S1;S1] ++
    S1::S0::S0::S1::S1::r =
  [S1;S1;S1;S1;S0] ++ copies (S n) [S1;S1;S1;S0] ++
    S0::S1::S1::r.
Proof.
  cbn [copies app]; rewrite rotate_head.
  pose proof (copies_slide n [S1;S1;S1;S0] (S0::S1::S1::r)) as H.
  cbn [app] in H; unfold Sym in *; rewrite H; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma q_packet n r :
  S1::S1::S1::copies n [S1;S0;S1;S1] ++
    S1::S0::S0::S0::S1::S1::S1::r =
  page (repeat Three n) ++ S1::S1::S1::r.
Proof.
  unfold page; rewrite core_bits_threes.
  destruct n as [|n]; cbn [copies app]; [reflexivity |].
  rewrite rotate_head.
  pose proof (copies_slide n [S1;S1;S1;S0]
    (S0::S0::S1::S1::S1::r)) as H.
  cbn [app] in H; unfold Sym in *; rewrite H; repeat rewrite <- app_assoc; reflexivity.
Qed.

Fixpoint saved_pages gaps r := match gaps with
  | [] => r
  | b::gaps => saved_pages gaps (page (repeat Three b) ++ r) end.

Lemma packet_pages gaps r :
  S1::S1::S1::packet gaps r = saved_pages gaps (S1::S1::S1::r).
Proof.
  revert r; induction gaps as [|b gaps IH]; intro r; cbn [packet saved_pages];
    [reflexivity | rewrite IH, q_packet; reflexivity].
Qed.

Lemma packet_app u v r : packet (u++v) r = packet v (packet u r).
Proof. revert r; induction u; intro r; cbn; [reflexivity | rewrite IHu; reflexivity]. Qed.

Lemma packet_last gaps b r :
  S1::S1::packet (gaps++[b]) r =
  copies (S b) [S1;S1;S1;S0] ++ S0::S0::
    saved_pages gaps (S1::S1::S1::r).
Proof.
  rewrite packet_app; cbn [packet].
  rewrite rotate_head.
  pose proof (copies_slide b [S1;S1;S1;S0]
    (S0::S0::S1::S1::S1::packet gaps r)) as H.
  cbn [app] in H; unfold Sym in *; rewrite H; cbn [copies app].
  rewrite packet_pages; reflexivity.
Qed.

Definition saved_body n m v r := [S1;S1;S1;S1;S0] ++
  copies (S n) [S1;S1;S1;S0] ++ S0::
  copies (S m) [S1;S1;S1;S0] ++ [S1;S1;S1;S1;S1;S1;S0] ++
  core_bits v ++ S0::S0::S1::S0::S1::r.

Lemma saved_body_normal n m v r :
  S1::S1::S1::(copies (S n) [S1;S0;S1;S1] ++
    [S1;S0;S0;S1;S1] ++ copies (S m) [S1;S0;S1;S1] ++
    S1::S1::S1::returned_core v ++
    S1::S0::S0::S0::S1::S0::S1::r) = saved_body n m v r.
Proof.
  cbn [app]; rewrite q_gap.
  unfold saved_body; cbn [app].
  rewrite rotate_head, returned_rotation; reflexivity.
Qed.

Definition paired_frontier a b r := G a
  (copies (S b) [S1;S1;S1;S0] ++ S0::S0::r).

Lemma T_core_odd_frontier a b gaps n m v r :
  advance (4*n+30*m+2*weight v+113+row_clock a (gaps++[b]))
    (tilted (row a (gaps++[b])) n (core_suffix (2*m+1) (v++[Three]) r)) =
  paired_frontier a b (saved_pages gaps (saved_body n m v r)).
Proof.
  rewrite T_core_odd_row, packet_last, saved_body_normal; reflexivity.
Qed.

Lemma returned_threes n : returned_core (repeat Three n) =
  copies n [S1;S0;S1;S1].
Proof. induction n; cbn; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma d1_pair l r :
  advance 4 (cfg D (S0::S1::S0::S1::l) S1 r) =
  cfg D l S1 (S1::S0::S1::S1::r).
Proof. reflexivity. Qed.

Definition short_page_suffix m c r := core_suffix (2*m+1) []
  ([S0;S1;S1;S1;S1;S0] ++ copies (c+2) [S1;S1;S1;S0] ++ S0::r).

Lemma T_short_page_turn w n m c r :
  advance (4*n+58*m+28*c+293) (tilted w (S n) (short_page_suffix m c r)) =
  cfg D (S0::S1::pushed_core w ++ [S0;S1]) S1
    ([S1;S0;S0;S1;S1] ++ copies (S n) [S1;S0;S1;S1] ++
     [S1;S0;S0;S1;S1] ++ copies (S (m+2)) [S1;S0;S1;S1] ++
     S1::S1::S1::returned_core (Six::repeat Three c) ++
     S1::S0::S0::S0::S1::S0::S1::r).
Proof.
  unfold short_page_suffix.
  replace (4*n+58*m+28*c+293) with
    ((30*m+77)+(10*(m+2)+(8+(7+(6+((weight (repeat Three (S c))+30)+
      (4+(3+(4*(m+2)+(4+(10*(m+3)+((weight (Six::repeat Three c)+30)+
      (4*(m+3)+(5+(4*S n+5))))))))))))))) by
    (change (weight (Six::repeat Three c)) with (weight ([Six]++repeat Three c));
     rewrite weight_app, !weight_threes;
     assert (weight [Six]=26) by reflexivity; nia).
  rewrite advance_add, T_short_turn.
  unfold short_frame; cbn [app].
  rewrite advance_add, triple_right, advance_add, d0four, advance_add, d001.
  rewrite advance_add, d0101.
  replace (c+2) with (S c+1) by lia.
  rewrite (copies_add (S c) 1 [S1;S1;S1;S0]).
  rewrite <- core_bits_threes; cbn [copies app].
  repeat rewrite <- app_assoc; cbn [app].
  rewrite advance_add, core_turn_head.
  rewrite advance_add, d1_pair.
  rewrite advance_add, d1gap, p_half_slide.
  rewrite advance_add, alternating_left, advance_add, odd_turn.
  replace (m+3) with (S (m+2)) by lia.
  rewrite advance_add, q_right_succ.
  rewrite returned_threes; cbn [copies app].
  rewrite rotate_head.
  rewrite <- core_bits_threes.
  pose proof (core_turn_head (Six::repeat Three c)) as Hturn.
  cbn [core_bits block_bits app] in Hturn.
  rewrite advance_add, Hturn.
  rewrite p_half_slide, advance_add.
  rewrite alternating_left_succ, advance_add, d1double.
  rewrite p_half_slide, advance_add, alternating_left_succ, d1double.
  reflexivity.
Qed.

Lemma T_short_page_row a gaps n m c r :
  advance (4*n+58*m+28*c+293+row_clock a gaps)
    (tilted (row a gaps) (S n) (short_page_suffix m c r)) =
  G a (S1::S1::packet gaps
    (copies (S n) [S1;S0;S1;S1] ++
     [S1;S0;S0;S1;S1] ++ copies (S (m+2)) [S1;S0;S1;S1] ++
     S1::S1::S1::returned_core (Six::repeat Three c) ++
     S1::S0::S0::S0::S1::S0::S1::r)).
Proof.
  rewrite advance_add, T_short_page_turn; cbn [app]; apply half_row.
Qed.

Lemma T_short_page_frontier a b gaps n m c r :
  advance (4*n+58*m+28*c+293+row_clock a (gaps++[b]))
    (tilted (row a (gaps++[b])) (S n) (short_page_suffix m c r)) =
  paired_frontier a b (saved_pages gaps (saved_body n (m+2) (Six::repeat Three c) r)).
Proof.
  rewrite T_short_page_row, packet_last, saved_body_normal; reflexivity.
Qed.

Definition counter_pair a b r := cfg D [] S0
  ([S1;S1;S1;S1;S0] ++ copies a [S1;S1;S1;S0] ++
   S0::copies b [S1;S1;S1;S0] ++ S0::S0::r).

Lemma mixed_threes b : core_bits (mixed_word (repeat Three b)) =
  copies (b+4) [S1;S1;S1;S0].
Proof.
  unfold mixed_word; cbn [core_bits block_bits].
  rewrite core_bits_app, core_bits_threes.
  replace (b+4) with (2+(b+2)) by lia.
  rewrite (copies_add 2 (b+2) [S1;S1;S1;S0]).
  rewrite (copies_add b 2 [S1;S1;S1;S0]).
  cbn [copies core_bits block_bits app].
  repeat rewrite <- app_assoc; reflexivity.
Qed.

Definition bridge_core n k b := repeat Three n ++ Six::repeat Three k ++ Six::repeat Three b.

Lemma bridge_weight n k b : weight (bridge_core n k b) = 14*n+14*k+14*b+52.
Proof.
  unfold bridge_core.
  change (weight (repeat Three n++[Six]++repeat Three k++[Six]++repeat Three b) = 14*n+14*k+14*b+52).
  rewrite !weight_app, !weight_threes.
  assert (weight [Six]=26) by reflexivity; lia.
Qed.

Lemma bridge_B n k b r :
  advance (14*n+14*k+14*b+112)
    (J 0 (copies (S n) [S1;S1;S1;S0] ++
      [S1;S1;S1;S1;S1;S1;S0] ++ copies k [S1;S1;S1;S0] ++
      [S1;S1;S1;S1;S1;S1;S0] ++ copies (S b) [S1;S1;S1;S0] ++
      S0::S0::r)) =
  W (Six::repeat Three (n+2) ++ Six::repeat Three k ++ Six::repeat Three b)
    (S0::S1::S0::r).
Proof.
  pose proof (B_transfer (bridge_core n k b) r) as H.
  rewrite bridge_weight in H.
  replace (14*n+14*k+14*b+52+60) with (14*n+14*k+14*b+112) in H by lia.
  unfold bridge_core in H.
  repeat first [rewrite core_bits_app in H | rewrite core_bits_threes in H |
    progress cbn [core_bits block_bits app] in H | rewrite <- app_assoc in H].
  rewrite (copies_succ_end b [S1;S1;S1;S0]).
  replace (n+2) with (S (S n)) by lia.
  cbn [repeat copies app].
  repeat first [rewrite <- app_assoc in * | progress cbn [app] in *]; exact H.
Qed.

Lemma J_even_threes_bridge n k b r :
  advance (42*n+44*k+42*b+328)
    (J n (mixed_suffix (2*k+2) (repeat Three b) r)) =
  W (Six::repeat Three (n+2) ++ Six::repeat Three k ++ Six::repeat Three b)
    (copies 3 [S0;S1] ++ S0::r).
Proof.
  replace (42*n+44*k+42*b+328) with
    ((28*n+30*k+2*weight (repeat Three b)+197)+(19+(14*n+14*k+14*b+112))) by
    (rewrite weight_threes; nia).
  rewrite advance_add, J_mixed_even.
  unfold mixed_even_result; cbn [app].
  rewrite advance_add, double_zero_frontier.
  cbn [core_bits block_bits]; rewrite core_bits_threes.
  change (advance (14*n+14*k+14*b+112)
    (J 0 (copies (S n) [S1;S1;S1;S0] ++
      [S1;S1;S1;S1;S1;S1;S0] ++ copies k [S1;S1;S1;S0] ++
      [S1;S1;S1;S1;S1;S1;S0] ++ copies (S b) [S1;S1;S1;S0] ++
      S0::S0::S1::S0::S1::S0::r)) =
    W (Six::repeat Three (n+2) ++ Six::repeat Three k ++ Six::repeat Three b)
      (copies 3 [S0;S1] ++ S0::r)).
  rewrite bridge_B; reflexivity.
Qed.

Lemma paired_even k b r :
  advance (56*k*k+352*k+687+b*(42*k+14*b+194))
    (counter_pair (2*k+2) (b+4) r) =
  tilted (repeat Three b ++ Six::repeat Three (2*k+4)) k
    (copies (b+3) [S0;S1] ++ S0::r).
Proof.
  replace (counter_pair (2*k+2) (b+4) r) with
    (G (2*k+1) (copies (b+4) [S1;S1;S1;S0] ++ S0::S0::r)) by
    (unfold counter_pair, G; replace (S (2*k+1)) with (2*k+2) by lia; reflexivity).
  replace (56*k*k+352*k+687+b*(42*k+14*b+194)) with
    (((2*k+1+2)*(14*(2*k+1)+34)-1)+
     ((42*(2*k+2)+44*k+42*b+328)+
      (b*(weight (Six::repeat Three (2*k+4))+14*(k+b)+60)+
       right_clock (Six::repeat Three (2*k+4))+10*b+24*k+73))) by
    (change (weight (Six::repeat Three (2*k+4))) with (weight ([Six]++repeat Three (2*k+4)));
     change (right_clock (Six::repeat Three (2*k+4))) with (right_clock ([Six]++repeat Three (2*k+4)));
     rewrite weight_app, weight_threes, right_clock_app, right_clock_threes;
     assert (weight [Six]=26) by reflexivity; assert (right_clock [Six]=19) by reflexivity; nia).
  rewrite advance_add, G_phase.
  replace (S (2*k+1)) with (2*k+2) by lia.
  rewrite <- mixed_threes.
  match goal with |- advance ?clock _ = ?result =>
    change (advance clock (J (2*k+2) (mixed_suffix (2*k+2) (repeat Three b) r)) = result)
  end.
  rewrite advance_add, J_even_threes_bridge.
  replace (2*k+2+2) with (2*k+4) by lia.
  pose proof (W_multi_six_phase (Six::repeat Three (2*k+4)) k b
    (copies 3 [S0;S1] ++ S0::r)) as H.
  repeat first [rewrite <- app_assoc in H | progress cbn [app] in H].
  rewrite copies_add; repeat rewrite <- app_assoc; exact H.
Qed.

Lemma mixed_cuts p a v b r :
  mixed_suffix p (repeat Three a++v++repeat Three b) r =
  copies p [S0;S1] ++ copies (a+2) [S1;S1;S1;S0] ++
    core_bits v ++ copies (b+2) [S1;S1;S1;S0] ++ S0::S0::r.
Proof.
  unfold mixed_suffix, mixed_word.
  repeat first [rewrite core_bits_app | rewrite core_bits_threes |
    progress cbn [core_bits block_bits app] | rewrite <- app_assoc].
  rewrite (copies_add b 2 [S1;S1;S1;S0]).
  replace (a+2) with (2+a) by lia.
  cbn [copies app].
  repeat first [rewrite <- app_assoc | progress cbn [app]]; reflexivity.
Qed.

Lemma bridge_B_general n k v b r :
  advance (14*n+14*k+weight v+14*b+126)
    (J 0 (copies (S n) [S1;S1;S1;S0] ++
      [S1;S1;S1;S1;S1;S1;S0] ++ copies k [S1;S1;S1;S0] ++
      [S1;S1;S1;S1;S1;S1;S0] ++ core_bits (Three::v) ++
      copies (S b) [S1;S1;S1;S0] ++ S0::S0::r)) =
  W (Six::repeat Three (n+2) ++ Six::repeat Three k ++ Six::Three::v++repeat Three b)
    (S0::S1::S0::r).
Proof.
  pose proof (B_transfer (repeat Three n ++ Six::repeat Three k ++
    Six::Three::v++repeat Three b) r) as H.
  assert (Hweight : weight (repeat Three n ++ Six::repeat Three k ++
    Six::Three::v++repeat Three b) = 14*n+14*k+weight v+14*b+66).
  { change (weight (repeat Three n++[Six]++repeat Three k++[Six;Three]++v++repeat Three b) =
      14*n+14*k+weight v+14*b+66).
    rewrite !weight_app, !weight_threes.
    assert (weight [Six]=26) by reflexivity; assert (weight [Six;Three]=40) by reflexivity; lia. }
  rewrite Hweight in H.
  replace (14*n+14*k+weight v+14*b+66+60) with
    (14*n+14*k+weight v+14*b+126) in H by lia.
  repeat first [rewrite core_bits_app in H | rewrite core_bits_threes in H |
    progress cbn [core_bits block_bits app] in H | rewrite <- app_assoc in H].
  rewrite (copies_succ_end b [S1;S1;S1;S0]).
  replace (n+2) with (S (S n)) by lia.
  cbn [repeat copies core_bits block_bits app].
  repeat first [rewrite <- app_assoc in * | progress cbn [app] in *]; exact H.
Qed.

Lemma J_even_general_bridge n k v b r :
  advance (42*n+44*k+3*weight v+42*b+370)
    (J n (mixed_suffix (2*k+2) (v++repeat Three (S b)) r)) =
  W (Six::repeat Three (n+2) ++ Six::repeat Three k ++ Six::Three::v++repeat Three b)
    (copies 3 [S0;S1] ++ S0::r).
Proof.
  replace (42*n+44*k+3*weight v+42*b+370) with
    ((28*n+30*k+2*weight (v++repeat Three (S b))+197)+
      (19+(14*n+14*k+weight v+14*b+126))) by
    (rewrite weight_app, weight_threes; nia).
  rewrite advance_add, J_mixed_even.
  unfold mixed_even_result; cbn [app].
  rewrite advance_add, double_zero_frontier.
  cbn [core_bits block_bits]; rewrite core_bits_app, core_bits_threes.
  pose proof (bridge_B_general n k v b (S1::S0::S1::S0::r)) as H.
  cbn [core_bits block_bits app] in H.
  repeat first [rewrite <- app_assoc in * | progress cbn [app] in *]; exact H.
Qed.

Definition odd_middle h b := repeat Three h ++ Six::repeat Three (b+3).
Definition odd_bridge h := repeat Three h ++ Six::repeat Three (h+1) ++ [Six].
Definition odd_outer h := Six::repeat Three (2*h+7) ++
  Six::repeat Three (h+1) ++ Six::repeat Three (h+1).

Lemma odd_weights h b :
  weight (odd_middle h b)=14*h+14*b+68 /\
  weight (odd_bridge h)=28*h+66 /\
  weight (odd_outer h)=56*h+204 /\ right_clock (odd_outer h)=40*h+147.
Proof.
  unfold odd_middle, odd_bridge, odd_outer.
  change (weight (repeat Three h++[Six]++repeat Three (b+3))=14*h+14*b+68 /\
    weight (repeat Three h++[Six]++repeat Three (h+1)++[Six])=28*h+66 /\
    weight ([Six]++repeat Three (2*h+7)++[Six]++repeat Three (h+1)++[Six]++repeat Three (h+1))=56*h+204 /\
    right_clock ([Six]++repeat Three (2*h+7)++[Six]++repeat Three (h+1)++[Six]++repeat Three (h+1))=40*h+147).
  rewrite !weight_app, !weight_threes, !right_clock_app, !right_clock_threes.
  assert (weight [Six]=26) by reflexivity; assert (right_clock [Six]=19) by reflexivity.
  repeat split; lia.
Qed.

Lemma paired_odd h b r :
  advance (168*(h+1)*(h+1)+904*(h+1)+1723+b*(70*(h+1)+14*b+316))
    (counter_pair (2*h+3) (b+8) r) =
  tilted (repeat Three b ++ odd_outer h) (h+1)
    (copies (b+7) [S0;S1] ++ S0::r).
Proof.
  replace (counter_pair (2*h+3) (b+8) r) with
    (G (2*h+2) (copies (b+8) [S1;S1;S1;S0] ++ S0::S0::r)) by
    (unfold counter_pair, G; replace (S (2*h+2)) with (2*h+3) by lia; reflexivity).
  replace (168*(h+1)*(h+1)+904*(h+1)+1723+b*(70*(h+1)+14*b+316)) with
    (((2*h+2+2)*(14*(2*h+2)+34)-1)+
     ((14*(2*h+3)+30*(h+1)+2*weight (repeat Three (b+4))+162)+
      (phase_clock 0 (2*h+3)+
       ((14*(2*h+4)+30*(h+1)+2*weight (odd_middle h b)+162)+
        (phase_clock 0 (2*h+4)+
         ((42*(2*h+5)+44*(h+1)+3*weight (odd_bridge h)+42*b+370)+
          (b*(weight (odd_outer h)+14*(h+1+b)+60)+right_clock (odd_outer h)+10*b+24*(h+1)+73))))))) by
    (destruct (odd_weights h b) as [H1 [H2 [H3 H4]]];
     rewrite H1,H2,H3,H4,weight_threes; unfold phase_clock; nia).
  rewrite advance_add, G_phase.
  replace (S (2*h+2)) with (2*h+3) by lia.
  replace (b+8) with (b+4+4) by lia; rewrite <- mixed_threes.
  match goal with |- advance ?clock _ = ?result =>
    change (advance clock (J (2*h+3) (mixed_suffix (2*h+3) (repeat Three (b+4)) r)) = result)
  end.
  replace (2*h+3) with (2*(h+1)+1) by lia.
  rewrite advance_add, J_mixed_odd, advance_add, K_phase.
  replace (0+(2*(h+1)+1)+1) with (2*h+4) by lia.
  pose proof (mixed_cuts (2*(h+1)+1) h [Six] (b+3)
    (S1::S0::S1::S0::r)) as Hfirst.
  change (repeat Three h++[Six]++repeat Three (b+3)) with (odd_middle h b) in Hfirst.
  replace (h+2) with (S (h+1)) in Hfirst by lia.
  replace (b+3+2) with (S (b+4)) in Hfirst by lia.
  cbn [core_bits block_bits app] in *; rewrite core_bits_threes.
  cbn [copies app] in Hfirst.
  cbn [copies app].
  repeat rewrite <- app_assoc.
  unfold Sym in *; rewrite <- Hfirst.
  rewrite advance_add, J_mixed_odd, advance_add, K_phase.
  clear Hfirst.
  replace (0+(2*h+4)+1) with (2*h+5) by lia.
  pose proof (mixed_cuts (2*(h+1)+2) h
    (Six::repeat Three (h+1)++[Six]) (b+1)
    (S1::S0::S1::S0::S1::S0::S1::S0::r)) as Hsecond.
  assert (Hlist : repeat Three h ++ (Six::repeat Three (h+1)++[Six]) ++ repeat Three (b+1) =
    odd_bridge h ++ repeat Three (S b)).
  { unfold odd_bridge; replace (b+1) with (S b) by lia.
    repeat first [rewrite <- app_assoc | progress cbn [app]]; reflexivity. }
  rewrite Hlist in Hsecond.
  replace (h+2) with (S (h+1)) in Hsecond by lia.
  replace (b+1+2) with (b+3) in Hsecond by lia.
  replace (2*h+4) with (2*(h+1)+2) by lia.
  unfold odd_middle.
  repeat first [rewrite core_bits_app | rewrite core_bits_threes |
    progress cbn [core_bits block_bits app] | rewrite <- app_assoc].
  repeat first [rewrite core_bits_app in Hsecond | rewrite core_bits_threes in Hsecond |
    progress cbn [core_bits block_bits app] in Hsecond | rewrite <- app_assoc in Hsecond].
  replace (h+1) with (S h) in * by lia.
  cbn [copies app] in *.
  unfold Sym in *; rewrite <- Hsecond.
  rewrite advance_add, J_even_general_bridge.
  clear Hsecond Hlist.
  pose proof (W_multi_six_phase (odd_outer h) (S h) b
    (copies 7 [S0;S1] ++ S0::r)) as Hphase.
  rewrite (copies_add b 7 [S0;S1]).
  unfold odd_bridge, odd_outer in *.
  replace (h+1) with (S h) in * by lia.
  replace (2*h+5+2) with (2*h+7) by lia.
  repeat first [rewrite <- app_assoc in * | progress cbn [repeat copies app] in *].
  exact Hphase.
Qed.

Definition shield a b d r := counter_pair a b
  (page (repeat Three (b/2-1)) ++ page (repeat Three d) ++ r).

Definition shield28_tail :=
  [S1;S1;S1;S1;S0] ++
  copies 5 [S1;S1;S1;S0] ++
  [S0;S0] ++
  [S1;S1;S1;S1;S0] ++
  [S1;S1;S1;S0] ++
  [S0;S0] ++
  [S1;S1;S1;S1;S0] ++
  copies 2 [S1;S1;S1;S0] ++
  [S0;S0] ++
  [S1;S1;S1;S1;S0] ++
  [S1;S1;S1;S0] ++
  [S0;S0] ++
  [S1;S1;S1;S1;S0] ++
  copies 3 [S1;S1;S1;S0] ++
  [S0;S0] ++
  [S1;S1;S1;S1;S0] ++
  copies 4 [S1;S1;S1;S0] ++
  [S0] ++
  copies 2 [S1;S1;S1;S0] ++
  [S1;S1;S1;S1;S1;S1;S0] ++
  copies 2 [S1;S1;S1;S0] ++
  [S1;S1;S1;S1;S1;S1;S0] ++
  copies 5 [S1;S1;S1;S0] ++
  [S1;S1;S1;S1;S1;S1;S0] ++
  copies 2 [S1;S1;S1;S0] ++
  [S0;S0;S1;S0;S1] ++
  [S0;S1;S0;S1] ++
  [S0] ++
  copies 2 [S1;S0] ++
  [S1;S0;S0;S1;S0;S1] ++
  [].

Definition shield59_tail r :=
  [S1;S1;S1;S1;S0] ++
  copies 7 [S1;S1;S1;S0] ++
  [S0] ++
  copies 13 [S1;S1;S1;S0] ++
  [S1;S1;S1;S1;S1;S1;S0] ++
  copies 11 [S1;S1;S1;S0] ++
  [S1;S1;S1;S1;S1;S1;S0] ++
  copies 17 [S1;S1;S1;S0] ++
  [S0;S0;S1;S0;S1] ++
  [S0;S1;S0;S1] ++
  [S0] ++
  [S1;S1;S1;S1;S0] ++
  copies 23 [S1;S1;S1;S0] ++
  [S0;S0] ++
  [S1;S1;S1;S1;S0] ++
  copies 7 [S1;S1;S1;S0] ++
  [S0;S0] ++
  [S1;S1;S1;S1;S0] ++
  copies 3 [S1;S1;S1;S0] ++
  [S0] ++
  copies 9 [S1;S1;S1;S0] ++
  [S1;S1;S1;S1;S1;S1;S0] ++
  copies 6 [S1;S1;S1;S0] ++
  [S0;S0;S1;S0;S1] ++
  copies 3 [S1;S1;S1;S0] ++
  [S1;S1;S1;S1;S1;S1;S0] ++
  copies 2 [S1;S1;S1;S0] ++
  [S1;S1;S1;S1;S1;S1;S0] ++
  copies 3 [S1;S1;S1;S0] ++
  [S0;S0;S1;S0;S1] ++
  [S0;S1;S0;S1] ++
  [S0] ++
  r.

Lemma blank_to_shield64259 : advance 64259 blank =
  shield 28 10 7 shield28_tail.
Proof. vm_compute; reflexivity. Qed.

Lemma shield28_to59 r : advance 553376 (shield 28 10 7 r) =
  shield 59 70 14 (shield59_tail r).
Proof. vm_compute; reflexivity. Qed.

Definition qright x r := [S1;S1;S1;S1;S0] ++
  copies (2*x+2) [S1;S1;S1;S0] ++ S0::r.

Definition Qfront x y r := counter_pair (6*x+2) (2*y+4)
  (page (repeat Three (y+2)) ++ qright x r).

Definition qframe x z r := copies (z+2) [S1;S1;S1;S0] ++
  [S1;S1;S1;S1;S1;S1;S0] ++
  copies (2*x) [S1;S1;S1;S0] ++ [S0;S0;S1;S0;S1] ++ r.

Definition qclock x z := 504*x*x+756*x*z+448*z*z+1442*x+1498*z+1414.
Definition qleft x z := repeat Three (4*z) ++ Six::repeat Three (6*x+3).

Lemma qleft_weight x z : weight (qleft x z) = 56*z+84*x+68.
Proof.
  unfold qleft.
  change (weight (repeat Three (4*z)++[Six]++repeat Three (6*x+3))=56*z+84*x+68).
  rewrite !weight_app, !weight_threes.
  assert (weight [Six]=26) by reflexivity; lia.
Qed.

Lemma qleft_input x z :
  repeat Three (4*z) ++ Six::repeat Three (2*(3*x)+4) = qleft x z++[Three].
Proof.
  unfold qleft; replace (2*(3*x)+4) with (S (6*x+3)) by lia.
  rewrite threes_succ_end; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma qleft_output x z :
  repeat Three (2*z+2-1) ++ qleft x z ++ Six::repeat Three (3*x+2) =
  row (6*z+1) [3*x+2;6*x+3].
Proof.
  unfold qleft; cbn [row].
  replace (2*z+2-1) with (2*z+1) by lia.
  replace (6*z+1) with ((2*z+1)+4*z) by lia.
  rewrite (repeat_app Three (2*z+1) (4*z)).
  repeat first [rewrite <- app_assoc | progress cbn [app]]; reflexivity.
Qed.

Lemma qright_core m x r :
  copies (2*m) [S0;S1] ++ S0::qright x r =
  core_suffix (2*m+1) (repeat Three (2*x)++[Three]) r.
Proof.
  replace (2*m+1) with (S (2*m)) by lia.
  rewrite <- threes_succ_end, positive_page_form.
  unfold qright; replace (S (S (2*x))) with (2*x+2) by lia.
  repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma Q_push x z r :
  advance (qclock x z) (Qfront x (2*z) r) = Qfront z (3*x) (qframe x z r).
Proof.
  unfold Qfront at 1.
  replace (6*x+2) with (2*(3*x)+2) by lia.
  replace (2*(2*z)+4) with (4*z+4) by lia.
  replace (qclock x z) with
    ((56*(3*x)*(3*x)+352*(3*x)+687+4*z*(42*(3*x)+14*(4*z)+194))+
     (page_clock (qleft x z) (3*x) (2*z+1) (2*z+2)+
      (4*(2*z+1)+30*(z+1)+2*weight (repeat Three (2*x))+113+
       row_clock (6*z+1) ([3*x+2]++[6*x+3])))) by
    (unfold qclock, page_clock; rewrite qleft_weight, weight_threes;
     cbn [row_clock app]; replace (2*z+2-1) with (2*z+1) by lia; nia).
  rewrite advance_add, paired_even, qleft_input.
  replace (4*z+3) with (2*(2*z+1)+1) by lia.
  assert (Hpage : S0::page (repeat Three (2*z+2)) ++ qright x r =
    [S0;S1;S1;S1;S1;S0] ++ copies (2*z+2) [S1;S1;S1;S0] ++
      S0::S0::qright x r).
  { unfold page; rewrite core_bits_threes; repeat rewrite <- app_assoc; reflexivity. }
  rewrite Hpage, advance_add, T_positive_page by lia.
  rewrite qleft_output.
  replace (copies (2*z+2) [S0;S1]) with
    (copies (2*(z+1)) [S0;S1]) by (f_equal; lia).
  rewrite qright_core, (T_core_odd_frontier (6*z+1) (6*x+3) [3*x+2]).
  unfold paired_frontier, counter_pair, G, Qfront, qright, qframe, saved_body.
  cbn [saved_pages].
  rewrite core_bits_threes.
  replace (S (6*z+1)) with (6*z+2) by lia.
  replace (S (6*x+3)) with (2*(3*x)+4) by lia.
  replace (S (2*z+1)) with (2*z+2) by lia.
  replace (S (z+1)) with (z+2) by lia.
  repeat first [rewrite <- app_assoc | progress cbn [app]]; reflexivity.
Qed.

Inductive QRun : nat -> nat -> list Sym -> nat -> nat -> list Sym -> nat -> nat -> Prop :=
| qrun_stop x k r : QRun x (2*k+1) r x (2*k+1) r 0 0
| qrun_push x z r xf yf rf n t :
    QRun z (3*x) (qframe x z r) xf yf rf n t ->
    QRun x (2*z) r xf yf rf (S n) (qclock x z+t).

Lemma Qrun_sound x y r xf yf rf n t : QRun x y r xf yf rf n t ->
  advance t (Qfront x y r) = Qfront xf yf rf.
Proof.
  intro H; induction H; [reflexivity |].
  rewrite advance_add, Q_push; exact IHQRun.
Qed.

Lemma positive_two_power n : 0<n -> exists a u, n=2^a*(2*u+1).
Proof.
  induction n as [n IH] using lt_wf_ind; intro Hn.
  pose proof (Nat.div_mod n 2 ltac:(lia)) as Hdivide.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as Hmod.
  assert (Hcases : n mod 2=0 \/ n mod 2=1) by lia.
  destruct Hcases as [Heven|Hodd].
  - assert (Hsmall : n/2<n) by (apply Nat.div_lt; lia).
    assert (Hpositive : 0<n/2) by nia.
    destruct (IH (n/2) Hsmall Hpositive) as [a [u Hu]].
    exists (S a),u; repeat first [rewrite Nat.pow_succ_r' | rewrite Nat.pow_0_r]; nia.
  - exists 0,(n/2); repeat first [rewrite Nat.pow_succ_r' | rewrite Nat.pow_0_r]; nia.
Qed.

Lemma Qrun_power_exit budget : forall a b u v r, a+b=budget ->
  exists xf k rf n t,
    QRun (2^a*(2*u+1)) (2^b*(2*v+1)) r xf (2*k+1) rf n t /\
    n=Nat.min (2*b) (2*a+1) /\ 0<xf.
Proof.
  induction budget as [budget IH] using lt_wf_ind.
  intros a b u v r Hbudget.
  destruct b as [|b].
  - exists (2^a*(2*u+1)),v,r,0,0.
    split.
    + replace (2^0*(2*v+1)) with (2*v+1) by (repeat first [rewrite Nat.pow_succ_r' | rewrite Nat.pow_0_r]; nia); constructor.
    + split; [reflexivity |].
      assert (Hpow : 2^a<>0) by (apply Nat.pow_nonzero; lia); nia.
  - destruct (IH (b+a) ltac:(lia) b a v (3*u+1)
      (qframe (2^a*(2*u+1)) (2^b*(2*v+1)) r) eq_refl)
      as [xf [k [rf [n [t [Hrun [Hcount Hxf]]]]]]].
    replace (2^a*(2*(3*u+1)+1)) with (3*(2^a*(2*u+1))) in Hrun by nia.
    exists xf,k,rf,(S n),(qclock (2^a*(2*u+1)) (2^b*(2*v+1))+t).
    split.
    + replace (2^S b*(2*v+1)) with (2*(2^b*(2*v+1))) by (repeat first [rewrite Nat.pow_succ_r' | rewrite Nat.pow_0_r]; nia).
      constructor; exact Hrun.
    + split; [|exact Hxf].
      rewrite Hcount; destruct (le_dec a b) as [Hab|Hab].
      * rewrite (Nat.min_l (2*a) (2*b+1)) by lia.
        rewrite (Nat.min_r (2*S b) (2*a+1)) by lia; lia.
      * rewrite (Nat.min_r (2*a) (2*b+1)) by lia.
        rewrite (Nat.min_l (2*S b) (2*a+1)) by lia; lia.
Qed.

Lemma Q_positive_phase_exit x y r : 0<x -> 0<y ->
  exists xf k rf n t, QRun x y r xf (2*k+1) rf n t /\ 0<xf.
Proof.
  intros Hx Hy.
  destruct (positive_two_power x Hx) as [a [u Hxu]].
  destruct (positive_two_power y Hy) as [b [v Hyv]].
  destruct (Qrun_power_exit (a+b) a b u v r eq_refl)
    as [xf [k [rf [n [t [Hrun [Hcount Hxf]]]]]]].
  exists xf,k,rf,n,t; rewrite Hxu,Hyv; auto.
Qed.

Definition callback_middle t b := repeat Three (t+2) ++ Six::repeat Three b.
Definition callback_payload t b r :=
  core_bits (Three::callback_middle t b++[Three;Three]) ++
  [S0;S0;S1;S0;S1] ++ r.
Definition callback_outer u n t :=
  Three::u++Six::repeat Three (n+2)++Six::repeat Three (t+1).
Definition callback_next u n t b :=
  repeat Three (b+1)++u++Six::repeat Three (n+2)++Six::repeat Three t.
Definition callback_clock u n t b :=
  b*(weight u+14*n+28*t+14*b+196)+weight u+28*n+92*t+38*b+518.

Lemma callback_weights u n t b :
  weight (callback_middle t b)=14*t+14*b+54 /\
  weight (callback_outer u n t)=weight u+14*n+14*t+108 /\
  right_clock (callback_outer u n t)=right_clock u+10*n+10*t+78.
Proof.
  unfold callback_middle, callback_outer.
  change (weight (repeat Three (t+2)++[Six]++repeat Three b)=14*t+14*b+54 /\
    weight ([Three]++u++[Six]++repeat Three (n+2)++[Six]++repeat Three (t+1))=weight u+14*n+14*t+108 /\
    right_clock ([Three]++u++[Six]++repeat Three (n+2)++[Six]++repeat Three (t+1))=right_clock u+10*n+10*t+78).
  rewrite !weight_app, !weight_threes, !right_clock_app, !right_clock_threes.
  assert (weight [Six]=26) by reflexivity; assert (weight [Three]=14) by reflexivity.
  assert (right_clock [Six]=19) by reflexivity; assert (right_clock [Three]=10) by reflexivity.
  repeat split; lia.
Qed.

Lemma callback_input t b r :
  copies (2*t+4) [S0;S1] ++ callback_payload t b r =
  core_suffix (2*(t+1)+2) (callback_middle t b++[Three])
    (S0::S1::S0::S1::r).
Proof.
  unfold callback_payload, core_suffix.
  replace (2*t+4) with (2*(t+1)+2) by lia.
  repeat first [rewrite <- app_assoc | progress cbn [app]]; reflexivity.
Qed.

Lemma callback_row u n t b :
  repeat Three b++callback_outer u n t = callback_next u n t b++[Three].
Proof.
  unfold callback_outer, callback_next.
  replace (b+1) with (S b) by lia; replace (t+1) with (S t) by lia.
  rewrite !threes_succ_end.
  repeat first [rewrite <- app_assoc | progress cbn [app]]; reflexivity.
Qed.

Lemma callback_link u n t b r :
  advance (callback_clock u n t b)
    (tilted (u++[Three]) n
      (copies (2*t+4) [S0;S1] ++ callback_payload t b r)) =
  tilted (callback_next u n t b++[Three]) (t+2)
    (copies (b+4) [S0;S1] ++ r).
Proof.
  destruct (callback_weights u n t b) as [Hmiddle [Houter Hright]].
  replace (callback_clock u n t b) with
    ((18*n+30*(t+1)+2*weight (callback_middle t b)+left_clock u+181)+
     (b*(weight (callback_outer u n t)+14*(t+2+b)+60)+
      right_clock (callback_outer u n t)+10*b+24*(t+2)+73)) by
    (rewrite Hmiddle,Houter,Hright; unfold callback_clock,weight; nia).
  rewrite callback_input, advance_add, T_core_even_return.
  pose proof (W_multi_six_phase (callback_outer u n t) (t+2) b
    (copies 4 [S0;S1] ++ r)) as Hphase.
  unfold page_core, callback_middle.
  unfold callback_outer in Hphase.
  repeat first [rewrite <- app_assoc in * | progress cbn [app] in *].
  unfold callback_outer.
  cbn [copies app] in Hphase.
  unfold Sym in *; rewrite Hphase.
  fold (callback_outer u n t).
  rewrite callback_row, copies_add.
  repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma row_prepend q a gaps : repeat Three q++row a gaps = row (a+q) gaps.
Proof.
  induction gaps as [|b gaps IH]; cbn [row].
  - rewrite <- repeat_app; f_equal; lia.
  - rewrite app_assoc,IH; reflexivity.
Qed.

Lemma callback_next_row a gaps n t b :
  callback_next (row a gaps) n t b = row (a+b+1) (t::(n+2)::gaps).
Proof.
  unfold callback_next; cbn [row].
  replace (a+b+1) with (a+(b+1)) by lia.
  rewrite <- row_prepend; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma row_last_three a d gaps : row a (d::gaps)++[Three] = row a (S d::gaps).
Proof.
  cbn [row]; rewrite threes_succ_end.
  repeat rewrite <- app_assoc; reflexivity.
Qed.

Definition exit_core v r := core_bits (Three::v++[Three;Three])++S0::r.

Lemma exit_core_form p v r : copies p [S0;S1]++exit_core v r =
  core_suffix p (v++[Three]) r.
Proof.
  unfold exit_core,core_suffix.
  repeat rewrite <- app_assoc; reflexivity.
Qed.

Definition row_exit_clock a b gaps n t s v :=
  callback_clock (row a (gaps++[b])) n t (2*s+1)+
  (4*(t+2)+30*(s+2)+2*weight v+113+
   row_clock (a+2*s+2) ([t+1;n+2]++gaps++[b])).

Definition row_exit_output a b gaps n t s v r :=
  paired_frontier (a+2*s+2) b
    (saved_pages ([t+1;n+2]++gaps) (saved_body (t+2) (s+2) v r)).

Lemma callback_row_exit a b gaps n t s v r :
  advance (row_exit_clock a b gaps n t s v)
    (tilted (row a (gaps++[b])++[Three]) n
      (copies (2*t+4) [S0;S1]++callback_payload t (2*s+1) (exit_core v r))) =
  row_exit_output a b gaps n t s v r.
Proof.
  unfold row_exit_clock; rewrite advance_add, callback_link, callback_next_row.
  rewrite row_last_three.
  replace (a+(2*s+1)+1) with (a+2*s+2) by lia.
  replace (2*s+1+4) with (2*(s+2)+1) by lia.
  rewrite exit_core_form.
  replace (S t) with (t+1) by lia.
  rewrite (T_core_odd_frontier (a+2*s+2) b ([t+1;n+2]++gaps)).
  reflexivity.
Qed.

Fixpoint exit_chain t indices s v r := match indices with
  | [] => callback_payload t (2*s+1) (exit_core v r)
  | z::indices => callback_payload t (2*z) (exit_chain z indices s v r)
  end.

Fixpoint exit_chain_clock a b gaps n t indices s v := match indices with
  | [] => row_exit_clock a b gaps n t s v
  | z::indices => callback_clock (row a (gaps++[b])) n t (2*z)+
      exit_chain_clock (a+2*z+1) b (t::(n+2)::gaps) (t+2) z indices s v
  end.

Fixpoint exit_chain_output a b gaps n t indices s v r := match indices with
  | [] => row_exit_output a b gaps n t s v r
  | z::indices => exit_chain_output (a+2*z+1) b (t::(n+2)::gaps) (t+2) z indices s v r
  end.

Lemma exit_chain_run indices : forall a b gaps n t s v r,
  advance (exit_chain_clock a b gaps n t indices s v)
    (tilted (row a (gaps++[b])++[Three]) n
      (copies (2*t+4) [S0;S1]++exit_chain t indices s v r)) =
  exit_chain_output a b gaps n t indices s v r.
Proof.
  induction indices as [|z indices IH]; intros a b gaps n t s v r;
    cbn [exit_chain_clock exit_chain exit_chain_output].
  - apply callback_row_exit.
  - rewrite advance_add, callback_link, callback_next_row; apply IH.
Qed.

Lemma saved_pages_append u v r : saved_pages (u++v) r = saved_pages v (saved_pages u r).
Proof.
  revert r; induction u as [|b u IH]; intro r; cbn [saved_pages app];
    [reflexivity | apply IH].
Qed.

Lemma exit_chain_prefix indices : forall a b extras c d n t s v r,
  exists aa rr, a+2*s+3<=aa /\
    exit_chain_output a b (extras++[d;c]) n t indices s v r =
    counter_pair aa (b+1) (page (repeat Three c)++page (repeat Three d)++rr).
Proof.
  induction indices as [|z indices IH]; intros a b extras c d n t s v r.
  - exists (a+2*s+3),
      (saved_pages ([t+1;n+2]++extras) (saved_body (t+2) (s+2) v r)).
    split; [lia |].
    cbn [exit_chain_output]; unfold row_exit_output.
    rewrite app_assoc, saved_pages_append; cbn [saved_pages].
    unfold paired_frontier,counter_pair,G.
    replace (S (a+2*s+2)) with (a+2*s+3) by lia.
    replace (S b) with (b+1) by lia; reflexivity.
  - destruct (IH (a+2*z+1) b (t::(n+2)::extras) c d (t+2) z s v r)
      as [aa [rr [Hbound Houtput]]].
    exists aa,rr; split; [lia |].
    cbn [exit_chain_output]; exact Houtput.
Qed.

Definition qodd_first x b := repeat Three (4*b+2)++Six::repeat Three (6*x+3).
Definition qodd_second x b := repeat Three (6*b+4)++
  Six::repeat Three (6*x+3)++Six::repeat Three (3*x+1).
Definition qodd_left x b := row (2*x+6*b+5) [2*b+3;3*x+1;6*x+3].
Definition qodd_clock x b := 812*x*x+1008*x*b+448*b*b+2472*x+2078*b+2519.

Lemma qodd_weights x b :
  weight (qodd_first x b)=56*b+84*x+96 /\
  weight (qodd_second x b)=84*b+126*x+164.
Proof.
  unfold qodd_first,qodd_second.
  change (weight (repeat Three (4*b+2)++[Six]++repeat Three (6*x+3))=56*b+84*x+96 /\
    weight (repeat Three (6*b+4)++[Six]++repeat Three (6*x+3)++[Six]++repeat Three (3*x+1))=84*b+126*x+164).
  rewrite !weight_app, !weight_threes.
  assert (weight [Six]=26) by reflexivity; split; lia.
Qed.

Lemma qodd_pair x b :
  repeat Three (4*b+2)++Six::repeat Three (2*(3*x)+4) = qodd_first x b++[Three].
Proof.
  unfold qodd_first; replace (2*(3*x)+4) with (S (6*x+3)) by lia.
  rewrite threes_succ_end; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma qodd_first_page x b :
  repeat Three (2*b+3-1)++qodd_first x b++Six::repeat Three (3*x+2) =
  qodd_second x b++[Three].
Proof.
  unfold qodd_first,qodd_second.
  replace (2*b+3-1) with (2*b+2) by lia.
  replace (6*b+4) with ((2*b+2)+(4*b+2)) by lia.
  rewrite (repeat_app Three (2*b+2) (4*b+2)).
  replace (3*x+2) with (S (3*x+1)) by lia; rewrite threes_succ_end.
  repeat first [rewrite <- app_assoc | progress cbn [app]]; reflexivity.
Qed.

Lemma qodd_second_page x b :
  repeat Three (2*x+2-1)++qodd_second x b++Six::repeat Three (2*b+2+2) =
  qodd_left x b++[Three].
Proof.
  unfold qodd_second,qodd_left; cbn [row].
  replace (2*x+2-1) with (2*x+1) by lia.
  replace (2*x+6*b+5) with ((2*x+1)+(6*b+4)) by lia.
  rewrite (repeat_app Three (2*x+1) (6*b+4)).
  replace (2*b+2+2) with (S (2*b+3)) by lia; rewrite threes_succ_end.
  repeat first [rewrite <- app_assoc | progress cbn [app]]; reflexivity.
Qed.

Lemma Q_odd_entry x b r :
  advance (qodd_clock x b) (Qfront x (2*b+1) r) =
  tilted (qodd_left x b++[Three]) (b+1) (copies (2*x+2) [S0;S1]++r).
Proof.
  destruct (qodd_weights x b) as [Hfirst Hsecond].
  unfold Qfront; replace (6*x+2) with (2*(3*x)+2) by lia.
  replace (2*(2*b+1)+4) with ((4*b+2)+4) by lia.
  replace (qodd_clock x b) with
    ((56*(3*x)*(3*x)+352*(3*x)+687+(4*b+2)*(42*(3*x)+14*(4*b+2)+194))+
     (page_clock (qodd_first x b) (3*x) (2*b+2) (2*b+3)+
      page_clock (qodd_second x b) (2*b+2) (b+1) (2*x+2))) by
    (unfold qodd_clock,page_clock; rewrite Hfirst,Hsecond;
     replace (2*b+3-1) with (2*b+2) by lia;
     replace (2*x+2-1) with (2*x+1) by lia; nia).
  rewrite advance_add, paired_even, qodd_pair.
  replace (2*b+1+2) with (2*b+3) by lia.
  replace (4*b+2+3) with (2*(2*b+2)+1) by lia.
  assert (Hpage : S0::page (repeat Three (2*b+3))++qright x r =
    [S0;S1;S1;S1;S1;S0]++copies (2*b+3) [S1;S1;S1;S0]++S0::S0::qright x r).
  { unfold page; rewrite core_bits_threes; repeat rewrite <- app_assoc; reflexivity. }
  rewrite Hpage, advance_add, T_positive_page by lia.
  rewrite qodd_first_page.
  replace (2*b+3) with (2*(b+1)+1) by lia.
  unfold qright; cbn [app].
  etransitivity; [apply T_positive_page; lia |].
  rewrite qodd_second_page; reflexivity.
Qed.

Lemma Q_odd_chain_to_shield indices a b s v r :
  2<=b -> 24<=4*a+6*b+2*s+10 ->
  exists aa rr, 24<=aa /\ 6<=2*b+3 /\
    advance (qodd_clock (2*a+1) b+
      exit_chain_clock (4*a+6*b+7) (12*a+9) [2*b+3;6*a+4] (b+1) (2*a) indices s v)
      (Qfront (2*a+1) (2*b+1) (exit_chain (2*a) indices s v r)) =
    shield aa (12*a+10) (2*b+3) rr.
Proof.
  intros Hb Hsize; rewrite advance_add,Q_odd_entry.
  unfold qodd_left.
  replace (2*(2*a+1)+6*b+5) with (4*a+6*b+7) by lia.
  replace (3*(2*a+1)+1) with (6*a+4) by lia.
  replace (6*(2*a+1)+3) with (12*a+9) by lia.
  replace (2*(2*a+1)+2) with (2*(2*a)+4) by lia.
  rewrite (exit_chain_run indices (4*a+6*b+7) (12*a+9) [2*b+3;6*a+4]).
  destruct (exit_chain_prefix indices (4*a+6*b+7) (12*a+9) [] (6*a+4) (2*b+3)
    (b+1) (2*a) s v r) as [aa [rr [Hbound Houtput]]].
  exists aa,rr; split; [lia |]; split; [lia |].
  cbn [app] in Houtput; rewrite Houtput; unfold shield.
  replace (12*a+9+1) with (12*a+10) by lia.
  replace ((12*a+10)/2-1) with (6*a+4); [reflexivity |].
  replace (12*a+10) with ((6*a+5)*2) by lia.
  rewrite Nat.div_mul by lia; lia.
Qed.

Lemma qframe_exit_chain x z indices s v r : 0<x -> 0<z ->
  qframe x z (exit_chain (x-1) indices s v r) =
  exit_chain (z-1) ((x-1)::indices) s v r.
Proof.
  intros Hx Hz; cbn [exit_chain].
  unfold qframe,callback_payload,callback_middle.
  cbn [core_bits block_bits].
  rewrite !core_bits_app,!core_bits_threes.
  cbn [core_bits block_bits].
  rewrite core_bits_threes.
  replace (z-1+2) with (z+1) by lia.
  replace (z+2) with (S (z+1)) by lia.
  cbn [copies].
  replace (2*x) with (2*(x-1)+2) by lia.
  rewrite (copies_add (2*(x-1)) 2 [S1;S1;S1;S0]).
  repeat first [rewrite <- app_assoc | progress cbn [copies app]]; reflexivity.
Qed.

Definition pure_page c r := page (repeat Three c)++r.
Definition page_header c r := [S1;S1;S1;S1;S0]++
  copies c [S1;S1;S1;S0]++S0::r.

Lemma pure_page_header c r : pure_page c r=page_header c (S0::r).
Proof.
  unfold pure_page,page,page_header; rewrite core_bits_threes.
  repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma header_core m c r :
  copies (2*m) [S0;S1]++S0::page_header (c+2) r =
  core_suffix (2*m+1) (repeat Three c++[Three]) r.
Proof.
  replace (2*m+1) with (S (2*m)) by lia.
  rewrite <- threes_succ_end,positive_page_form.
  unfold page_header; replace (S (S c)) with (c+2) by lia.
  repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma page_row_next a b gaps n c : 0<c ->
  repeat Three (c-1)++row a (gaps++[b])++Six::repeat Three (n+2) =
  row (a+(c-1)) (((n+1)::gaps)++[b])++[Three].
Proof.
  intro Hc; cbn [row app].
  rewrite <- row_prepend.
  replace (n+2) with (S (n+1)) by lia; rewrite threes_succ_end.
  repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma positive_page_row a b gaps n m c r : 0<c ->
  advance (page_clock (row a (gaps++[b])) n m c)
    (tilted (row a (gaps++[b])++[Three]) n
      (copies (2*m+1) [S0;S1]++S0::pure_page c r)) =
  tilted (row (a+(c-1)) (((n+1)::gaps)++[b])++[Three]) m
    (copies c [S0;S1]++S0::r).
Proof.
  intro Hc; rewrite pure_page_header; unfold page_header.
  etransitivity; [apply T_positive_page; exact Hc |].
  rewrite page_row_next by exact Hc; reflexivity.
Qed.

Definition RowReturn a b gaps n m r : Prop :=
  exists clock delta tail, 0<clock /\
    advance clock (tilted (row a (gaps++[b])++[Three]) n
      (copies (2*m+1) [S0;S1]++S0::r)) =
    counter_pair (a+delta+1) (b+1) (saved_pages gaps tail).

Lemma row_return_odd_page a b gaps n m z r :
  RowReturn (a+2*z) b ((n+1)::gaps) m z r ->
  RowReturn a b gaps n m (pure_page (2*z+1) r).
Proof.
  intros [clock [delta [tail [Hclock Hreturn]]]].
  exists (page_clock (row a (gaps++[b])) n m (2*z+1)+clock),
    (2*z+delta),(page (repeat Three (n+1))++tail).
  split; [lia |].
  rewrite advance_add,positive_page_row by lia.
  replace (a+(2*z+1-1)) with (a+2*z) by lia.
  rewrite Hreturn; cbn [saved_pages]; f_equal; lia.
Qed.

Lemma row_return_even_page a b gaps n m z d r :
  RowReturn a b gaps n m (pure_page (2*z+2) (page_header (d+2) r)).
Proof.
  exists (page_clock (row a (gaps++[b])) n m (2*z+2)+
    (4*m+30*(z+1)+2*weight (repeat Three d)+113+
     row_clock (a+(2*z+1)) (((n+2)::gaps)++[b]))),
    (2*z+1),(page (repeat Three (n+2))++saved_body m (z+1) (repeat Three d) r).
  split; [lia |].
  rewrite advance_add,positive_page_row by lia.
  replace (a+(2*z+2-1)) with (a+(2*z+1)) by lia.
  replace (2*z+2) with (2*(z+1)) by lia.
  rewrite header_core.
  cbn [app]; rewrite row_last_three.
  replace (S (n+1)) with (n+2) by lia.
  rewrite (T_core_odd_frontier (a+(2*z+1)) b ((n+2)::gaps)).
  unfold paired_frontier,counter_pair,G; cbn [saved_pages].
  replace (S (a+(2*z+1))) with (a+(2*z+1)+1) by lia.
  replace (S b) with (b+1) by lia; reflexivity.
Qed.

Lemma short_pure_pages z d r :
  copies (2*z+2) [S0;S1]++S0::pure_page 1 (pure_page (d+2) r) =
  short_page_suffix (z+1) d (S0::r).
Proof.
  unfold short_page_suffix.
  replace (2*(z+1)+1) with (S (2*z+2)) by lia.
  change (@nil block) with (repeat Three 0); rewrite positive_page_form.
  unfold pure_page,page; rewrite !core_bits_threes.
  repeat first [rewrite <- app_assoc | progress cbn [copies app]]; reflexivity.
Qed.

Lemma row_return_even_page_short a b gaps n m z d r :
  RowReturn a b gaps n (S m)
    (pure_page (2*z+2) (pure_page 1 (pure_page (d+2) r))).
Proof.
  exists (page_clock (row a (gaps++[b])) n (S m) (2*z+2)+
    (4*m+58*(z+1)+28*d+293+
     row_clock (a+(2*z+1)) (((n+2)::gaps)++[b]))),
    (2*z+1),(page (repeat Three (n+2))++
      saved_body m (z+1+2) (Six::repeat Three d) (S0::r)).
  split; [lia |].
  rewrite advance_add,positive_page_row by lia.
  replace (a+(2*z+2-1)) with (a+(2*z+1)) by lia.
  rewrite short_pure_pages.
  cbn [app]; rewrite row_last_three.
  replace (S (n+1)) with (n+2) by lia.
  rewrite (T_short_page_frontier (a+(2*z+1)) b ((n+2)::gaps)).
  unfold paired_frontier,counter_pair,G; cbn [saved_pages].
  replace (S (a+(2*z+1))) with (a+(2*z+1)+1) by lia.
  replace (S b) with (b+1) by lia; reflexivity.
Qed.

Definition frame_core s v := repeat Three (s+2)++Six::v.
Definition frame_body s v r :=
  core_bits (repeat Three (s+3)++Six::v++[Three;Three])++
    [S0;S0;S1;S0;S1]++r.

Lemma frame_body_core p s v r :
  copies p [S0;S1]++frame_body s v r =
  core_suffix p (frame_core s v++[Three]) ([S0;S1;S0;S1]++r).
Proof.
  unfold frame_body,frame_core,core_suffix.
  replace (s+3) with (S (s+2)) by lia.
  cbn [repeat].
  repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma row_return_odd_mixed a b gaps n m z s v r :
  RowReturn a b gaps n m (page_header (2*z+1) (frame_body s v r)).
Proof.
  exists (page_clock (row a (gaps++[b])) n m (2*z+1)+
    (4*m+30*z+2*weight (frame_core s v)+113+
     row_clock (a+2*z) (((n+2)::gaps)++[b]))),
    (2*z),(page (repeat Three (n+2))++
      saved_body m z (frame_core s v) ([S0;S1;S0;S1]++r)).
  split; [lia |].
  rewrite advance_add; unfold page_header.
  etransitivity; [apply f_equal; apply T_positive_page; lia |].
  rewrite page_row_next by lia.
  replace (a+(2*z+1-1)) with (a+2*z) by lia.
  rewrite frame_body_core.
  cbn [app]; rewrite row_last_three.
  replace (S (n+1)) with (n+2) by lia.
  rewrite (T_core_odd_frontier (a+2*z) b ((n+2)::gaps)).
  unfold paired_frontier,counter_pair,G; cbn [saved_pages].
  replace (S (a+2*z)) with (a+2*z+1) by lia.
  replace (S b) with (b+1) by lia; reflexivity.
Qed.

Fixpoint frame_pages t indices s v r := match indices with
  | [] => pure_page (t+1) (page_header (t+3) (frame_body s v r))
  | z::indices => pure_page t (pure_page (t+4) (frame_pages z indices s v r))
  end.

Lemma frame_pages_return indices : Forall (fun z => 1<=z) indices ->
  forall t a b gaps n m s v r, 1<=t ->
    RowReturn a b gaps n m (frame_pages t indices s v r).
Proof.
  intro Hindices; induction Hindices as [|z indices Hz Hindices IH];
    intros t a b gaps n m s v r Ht; cbn [frame_pages].
  - pose proof (Nat.div_mod t 2 ltac:(lia)) as Hdivide.
    pose proof (Nat.mod_upper_bound t 2 ltac:(lia)) as Hmod.
    destruct (Nat.eq_dec (t mod 2) 0) as [Heven|Hodd].
    + replace (t+1) with (2*(t/2)+1) by lia.
      apply row_return_odd_page.
      replace (t+3) with (2*(t/2+1)+1) by lia.
      apply row_return_odd_mixed.
    + replace (t+1) with (2*(t/2)+2) by lia.
      replace (t+3) with ((2*(t/2)+2)+2) by lia.
      apply row_return_even_page.
  - pose proof (Nat.div_mod t 2 ltac:(lia)) as Hdivide.
    pose proof (Nat.mod_upper_bound t 2 ltac:(lia)) as Hmod.
    destruct (Nat.eq_dec (t mod 2) 0) as [Heven|Hodd].
    + rewrite (pure_page_header (t+4) (frame_pages z indices s v r)).
      replace t with (2*(t/2-1)+2) at 1 by lia.
      replace (t+4) with ((t+2)+2) by lia.
      apply row_return_even_page.
    + replace t with (2*(t/2)+1) at 1 by lia.
      apply row_return_odd_page.
      replace (t+4) with (2*(t/2+2)+1) by lia.
      apply row_return_odd_page; apply IH; exact Hz.
Qed.

Lemma leading_page_frames_return indices : Forall (fun z => 1<=z) indices ->
  forall t a b gaps n k s v r, 1<=t ->
    RowReturn a b gaps n (k+1) (pure_page (k+3) (frame_pages t indices s v r)).
Proof.
  intro Hindices; intros t a b gaps n k s v r Ht.
  pose proof (Nat.div_mod k 2 ltac:(lia)) as Hdivide.
  pose proof (Nat.mod_upper_bound k 2 ltac:(lia)) as Hmod.
  destruct (Nat.eq_dec (k mod 2) 0) as [Heven|Hodd].
  - replace (k+3) with (2*(k/2+1)+1) by lia.
    apply row_return_odd_page; apply frame_pages_return; assumption.
  - replace (k+3) with (2*(k/2+1)+2) by lia.
    destruct indices as [|z indices].
    + cbn [frame_pages].
      rewrite (pure_page_header (t+1) (page_header (t+3) (frame_body s v r))).
      replace (t+1) with ((t-1)+2) by lia.
      apply row_return_even_page.
    + cbn [frame_pages].
      destruct t as [|[|t]]; [lia | |].
      * replace (k+1) with (S k) by lia.
        change (1+4) with (3+2); apply row_return_even_page_short.
      * rewrite (pure_page_header (S (S t)) (pure_page (S (S t)+4) (frame_pages z indices s v r))).
        replace (S (S t)) with (t+2) by lia.
        apply row_return_even_page.
Qed.

Fixpoint chain_growth indices := match indices with
  | [] => 0
  | z::indices => 2*z+1+chain_growth indices
  end.

Lemma saved_frame_body t s v r :
  saved_body (t+2) (s+2) (v++[Three;Three]) r =
  page_header (t+3) (frame_body s v r).
Proof.
  unfold saved_body,page_header,frame_body.
  repeat first [rewrite core_bits_app | rewrite core_bits_threes |
    progress cbn [core_bits block_bits app] | rewrite <- app_assoc].
  replace (S (t+2)) with (t+3) by lia.
  replace (S (s+2)) with (s+3) by lia.
  repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma exit_chain_page_form indices : forall a b gaps n t s v r,
  exit_chain_output a b gaps n t indices s (v++[Three;Three]) r =
  counter_pair (a+chain_growth indices+2*s+3) (b+1)
    (saved_pages gaps (pure_page (n+2) (frame_pages t indices s v r))).
Proof.
  induction indices as [|z indices IH]; intros a b gaps n t s v r.
  - cbn [exit_chain_output chain_growth frame_pages].
    unfold row_exit_output; rewrite saved_pages_append; cbn [saved_pages].
    rewrite saved_frame_body.
    unfold paired_frontier,counter_pair,G,pure_page.
    replace (S (a+2*s+2)) with (a+0+2*s+3) by lia.
    replace (S b) with (b+1) by lia; reflexivity.
  - cbn [exit_chain_output chain_growth]; rewrite IH.
    cbn [saved_pages frame_pages].
    replace (t+2+2) with (t+4) by lia.
    replace (a+2*z+1+chain_growth indices+2*s+3) with
      (a+(2*z+1+chain_growth indices)+2*s+3) by lia.
    unfold pure_page; reflexivity.
Qed.

Definition q_page_a x b indices s := 2*x+6*b+chain_growth indices+2*s+8.
Definition q_page_clock x b indices s v := qodd_clock x b+
  exit_chain_clock (2*x+6*b+5) (6*x+3) [2*b+3;3*x+1]
    (b+1) (x-1) indices s (v++[Three;Three]).
Definition q_page_output x b indices s v r :=
  counter_pair (q_page_a x b indices s) (6*x+4)
    (pure_page (3*x+1) (pure_page (2*b+3) (pure_page (b+3)
      (frame_pages (x-1) indices s v r)))).

Lemma Q_page_return x b indices s v r : 1<=x ->
  advance (q_page_clock x b indices s v)
    (Qfront x (2*b+1) (exit_chain (x-1) indices s (v++[Three;Three]) r)) =
  q_page_output x b indices s v r.
Proof.
  intro Hx; unfold q_page_clock; rewrite advance_add,Q_odd_entry.
  unfold qodd_left.
  replace (2*x+2) with (2*(x-1)+4) by lia.
  rewrite (exit_chain_run indices (2*x+6*b+5) (6*x+3) [2*b+3;3*x+1]).
  rewrite exit_chain_page_form; cbn [saved_pages].
  unfold q_page_output,q_page_a,pure_page.
  replace (2*x+6*b+5+chain_growth indices+2*s+3) with
    (2*x+6*b+chain_growth indices+2*s+8) by lia.
  replace (6*x+3+1) with (6*x+4) by lia.
  replace (b+1+2) with (b+3) by lia; reflexivity.
Qed.

Definition even_prefix_clock a x b :=
  (56*(2*a+1)*(2*a+1)+352*(2*a+1)+687+12*x*(42*(2*a+1)+14*(12*x)+194))+
  (page_clock (row (12*x) [4*a+5]) (2*a+1) (6*x+1) (6*x+1)+
   page_clock (row (18*x) [2*a+2;4*a+5]) (6*x+1) (3*x) (2*b+3)).

Lemma even_prefix_pair a x :
  repeat Three (12*x)++Six::repeat Three (2*(2*a+1)+4) =
  row (12*x) [4*a+5]++[Three].
Proof.
  cbn [row]; replace (2*(2*a+1)+4) with (S (4*a+5)) by lia.
  rewrite threes_succ_end; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma even_page_prefix a x b r :
  advance (even_prefix_clock a x b)
    (counter_pair (4*a+4) (12*x+4) (pure_page (6*x+1) (pure_page (2*b+3) r))) =
  tilted (row (18*x+2*b+2) [6*x+2;2*a+2;4*a+5]++[Three]) (3*x)
    (copies (2*(b+1)+1) [S0;S1]++S0::r).
Proof.
  unfold even_prefix_clock.
  replace (4*a+4) with (2*(2*a+1)+2) by lia.
  rewrite advance_add,paired_even,even_prefix_pair.
  replace (12*x+3) with (2*(6*x+1)+1) by lia.
  rewrite advance_add,(positive_page_row (12*x) (4*a+5) []) by lia.
  replace (12*x+(6*x+1-1)) with (18*x) by lia.
  replace (2*a+1+1) with (2*a+2) by lia.
  replace (6*x+1) with (2*(3*x)+1) at 3 by lia.
  rewrite (positive_page_row (18*x) (4*a+5) [2*a+2]) by lia.
  replace (18*x+(2*b+3-1)) with (18*x+2*b+2) by lia.
  replace (6*x+1+1) with (6*x+2) by lia.
  replace (2*b+3) with (2*(b+1)+1) by lia; reflexivity.
Qed.

Lemma even_frontier_frame_shield a x b indices s v r :
  5<=a -> 1<=x -> 2<=b -> Forall (fun z => 1<=z) indices ->
  exists clock aa rr, 0<clock /\ 24<=aa /\
    advance clock (counter_pair (4*a+4) (12*x+4)
      (pure_page (6*x+1) (pure_page (2*b+3) (pure_page (b+3)
        (frame_pages (2*x-1) indices s v r))))) =
    shield aa (4*a+6) (6*x+2) rr.
Proof.
  intros Ha Hx Hb Hindices.
  destruct (leading_page_frames_return indices Hindices (2*x-1) (18*x+2*b+2)
    (4*a+5) [6*x+2;2*a+2] (3*x) b s v r ltac:(lia))
    as [clock [delta [rr [Hclock Hreturn]]]].
  exists (even_prefix_clock a x b+clock),(18*x+2*b+2+delta+1),rr.
  split; [lia |]; split; [lia |].
  cbn [app] in Hreturn.
  rewrite advance_add,even_page_prefix,Hreturn.
  unfold shield; cbn [saved_pages].
  replace (4*a+5+1) with (4*a+6) by lia.
  replace ((4*a+6)/2-1) with (2*a+2); [reflexivity |].
  replace (4*a+6) with ((2*a+3)*2) by lia.
  rewrite Nat.div_mul by lia; lia.
Qed.

Ltac literal_nat n := lazymatch n with
  | O => idtac | S ?m => literal_nat m end.

Ltac expand_constant_copies :=
  match goal with |- context[copies ?n ?w] =>
    let k := eval cbv [Nat.add Nat.mul Nat.sub] in n in
    literal_nat k; change (copies n w) with (copies k w);
    cbn [copies app]
  end.

Ltac prefix_word_eq :=
  first [reflexivity |
    progress cbn [app]; prefix_word_eq |
    progress (repeat rewrite <- app_assoc); prefix_word_eq |
    match goal with |- context[copies ?n ?w] =>
      let H := fresh in assert (H : n=0) by lia;
      rewrite H; clear H; cbn [copies app]; prefix_word_eq end |
    expand_constant_copies; prefix_word_eq |
    lazymatch goal with
    | |- ?a::?xs = ?a::?ys => f_equal; prefix_word_eq
    | |- copies ?n ?w++?a = copies ?m ?w++?b =>
      first [apply copies_prefix_eq; [lia | prefix_word_eq] |
        apply copies_prefix_left; [lia | prefix_word_eq] |
        apply copies_prefix_right; [lia | prefix_word_eq]]
    | |- copies ?n ?w++?a = _ =>
      rewrite (copies_peel n w a) by lia; prefix_word_eq
    | |- _ = copies ?n ?w++?a =>
      rewrite (copies_peel n w a) by lia; prefix_word_eq
    end].

Ltac prefix_config_eq :=
  unfold counter_pair, paired_frontier, G, tilted, carried, W, core_suffix,
    saved_body, odd_outer, row, saved_pages, page, pure_page, page_header;
  repeat first [rewrite core_bits_app | rewrite core_bits_threes |
    rewrite pushed_core_app | rewrite pushed_threes |
    progress cbn [core_bits block_bits pushed_core pushed_bits app] |
    rewrite <- app_assoc];
  f_equal; prefix_word_eq.

Ltac one_constant_power :=
  match goal with |- context[copies ?n ?w] =>
    let k := eval cbv [Nat.add Nat.mul Nat.sub] in n in
    literal_nat k;
    let rhs := eval cbv [copies app] in (copies k w) in
    change (copies n w) with rhs; cbn [app]
  end.

Ltac prefix_word_eq_fast :=
  first [reflexivity |
    progress cbn [app]; prefix_word_eq_fast |
    progress (repeat rewrite <- app_assoc); prefix_word_eq_fast |
    lazymatch goal with
    | |- ?a::?xs = ?a::?ys => f_equal; prefix_word_eq_fast
    | |- copies ?n ?w++?a = copies ?m ?w++?b =>
      first [apply copies_prefix_eq; [lia | prefix_word_eq_fast] |
        apply copies_prefix_left; [lia | prefix_word_eq_fast] |
        apply copies_prefix_right; [lia | prefix_word_eq_fast]]
    end |
    match goal with |- context[copies ?n ?w] =>
      let H := fresh in assert (H : n=0) by lia;
      rewrite H; clear H; change (copies 0 w) with (@nil Sym);
      cbn [app]; prefix_word_eq_fast end |
    one_constant_power; prefix_word_eq_fast |
    match goal with |- context[copies ?n ?w++?tail] =>
      progress (rewrite (copies_slide n w)); prefix_word_eq_fast end |
    lazymatch goal with
    | |- copies ?n ?w++?a = _ =>
      rewrite (copies_peel n w a) by lia; prefix_word_eq_fast
    | |- _ = copies ?n ?w++?a =>
      rewrite (copies_peel n w a) by lia; prefix_word_eq_fast
    end].

Ltac prefix_config_eq_fast :=
  unfold pure_page, counter_pair, paired_frontier, G, tilted, carried, W,
    core_suffix, saved_body, odd_outer, row, saved_pages, page, page_header;
  repeat first [rewrite core_bits_app | rewrite core_bits_threes |
    rewrite pushed_core_app | rewrite pushed_threes |
    progress cbn [core_bits block_bits pushed_core pushed_bits app] |
    rewrite <- app_assoc];
  f_equal; prefix_word_eq_fast.

Lemma Qrun_strong_bounds x y r xf yf rf n t :
  QRun x y r xf yf rf n t -> 6<=x -> 13<=y -> 6<=xf /\ 13<=yf.
Proof.
  intro Hrun; induction Hrun; intros Hx Hy; [lia |apply IHHrun; lia].
Qed.

Lemma Qrun_strong_chain x y r xf yf rf n t :
  QRun x y r xf yf rf n t -> 6<=x -> 13<=y ->
  forall indices s v tail, r=exit_chain (x-1) indices s v tail ->
    Forall (fun z => 5<=z) indices ->
  exists output_indices,
    Forall (fun z => 5<=z) output_indices /\
    length output_indices=length indices+n /\
    rf=exit_chain (xf-1) output_indices s v tail.
Proof.
  intro Hrun; induction Hrun; intros Hx Hy indices s v tail Htail Hindices.
  - exists indices; split; [exact Hindices |]; split; [lia |exact Htail].
  - destruct (IHHrun ltac:(lia) ltac:(lia) ((x-1)::indices) s v tail)
      as [output_indices [Hpositive [Hlength Houtput]]].
    + rewrite Htail; apply qframe_exit_chain; lia.
    + constructor; [lia |exact Hindices].
    + exists output_indices; split; [exact Hpositive |].
      split; [cbn [length] in Hlength; lia |exact Houtput].
Qed.

Lemma Q_strong_chain_exit x y indices s v r :
  6<=x -> 13<=y -> Forall (fun z => 5<=z) indices ->
  exists xf b output_indices n t,
    6<=xf /\ 6<=b /\ Forall (fun z => 5<=z) output_indices /\
    length output_indices=length indices+n /\
    QRun x y (exit_chain (x-1) indices s v r)
      xf (2*b+1) (exit_chain (xf-1) output_indices s v r) n t /\
    advance t (Qfront x y (exit_chain (x-1) indices s v r)) =
      Qfront xf (2*b+1) (exit_chain (xf-1) output_indices s v r).
Proof.
  intros Hx Hy Hindices.
  destruct (Q_positive_phase_exit x y (exit_chain (x-1) indices s v r) ltac:(lia) ltac:(lia))
    as [xf [b [rf [n [t [Hrun Hxf]]]]]].
  destruct (Qrun_strong_chain _ _ _ _ _ _ _ _ Hrun Hx Hy indices s v r eq_refl Hindices)
    as [output_indices [Hpositive [Hlength Htail]]].
  destruct (Qrun_strong_bounds _ _ _ _ _ _ _ _ Hrun Hx Hy) as [Hxf2 Hyf].
  exists xf,b,output_indices,n,t; rewrite <- Htail.
  repeat split; try assumption; try lia.
  apply Qrun_sound with (n:=n); exact Hrun.
Qed.

Definition even_stage k x b r :=
  tilted (row (18*x+2*b+2) [6*x+2;k+1;2*k+3]++[Three]) (3*x)
    (copies (2*(b+1)+1) [S0;S1]++S0::r).
Definition even_stage_clock k x b :=
  (56*k*k+352*k+687+12*x*(42*k+14*(12*x)+194))+
  (page_clock (row (12*x) [2*k+3]) k (6*x+1) (6*x+1)+
   page_clock (row (18*x) [k+1;2*k+3]) (6*x+1) (3*x) (2*b+3)).

Lemma even_stage_pair k x :
  repeat Three (12*x)++Six::repeat Three (2*k+4) =
  row (12*x) [2*k+3]++[Three].
Proof.
  cbn [row]; replace (2*k+4) with (S (2*k+3)) by lia.
  rewrite threes_succ_end; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma even_stage_return k x b r :
  advance (even_stage_clock k x b)
    (counter_pair (2*k+2) (12*x+4) (pure_page (6*x+1) (pure_page (2*b+3) r))) =
  even_stage k x b r.
Proof.
  unfold even_stage_clock,even_stage.
  rewrite advance_add,paired_even,even_stage_pair.
  replace (12*x+3) with (2*(6*x+1)+1) by lia.
  rewrite advance_add,(positive_page_row (12*x) (2*k+3) []) by lia.
  replace (12*x+(6*x+1-1)) with (18*x) by lia.
  replace (6*x+1) with (2*(3*x)+1) at 3 by lia.
  rewrite (positive_page_row (18*x) (2*k+3) [k+1]) by lia.
  replace (18*x+(2*b+3-1)) with (18*x+2*b+2) by lia.
  replace (6*x+1+1) with (6*x+2) by lia.
  replace (2*b+3) with (2*(b+1)+1) by lia; reflexivity.
Qed.

Definition odd_stage h x b r :=
  tilted (row (18*x+2*b-2) [6*x+2;h+2;h;h+1;2*h+7]++[Three]) (3*x)
    (copies (2*(b+1)+1) [S0;S1]++S0::r).
Definition odd_stage_clock h x b :=
  (168*(h+1)*(h+1)+904*(h+1)+1723+(12*x-4)*(70*(h+1)+14*(12*x-4)+316))+
  (page_clock (row (12*x-4) [h;h+1;2*h+7]) (h+1) (6*x+1) (6*x+1)+
   page_clock (row (18*x-4) [h+2;h;h+1;2*h+7]) (6*x+1) (3*x) (2*b+3)).

Lemma odd_stage_pair h x :
  repeat Three (12*x-4)++odd_outer h =
  row (12*x-4) [h;h+1;2*h+7]++[Three].
Proof.
  unfold odd_outer; cbn [row].
  assert (Hlast : repeat Three (h+1)=repeat Three h++[Three]) by
    (replace (h+1) with (S h) by lia; apply threes_succ_end).
  rewrite Hlast at 2; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma odd_stage_return h x b r : 1<=x ->
  advance (odd_stage_clock h x b)
    (counter_pair (2*h+3) (12*x+4) (pure_page (6*x+1) (pure_page (2*b+3) r))) =
  odd_stage h x b r.
Proof.
  intro Hx; unfold odd_stage_clock,odd_stage.
  replace (12*x+4) with ((12*x-4)+8) by lia.
  rewrite advance_add,paired_odd,odd_stage_pair.
  replace (12*x-4+7) with (2*(6*x+1)+1) by lia.
  rewrite advance_add,(positive_page_row (12*x-4) (2*h+7) [h;h+1]) by lia.
  replace (12*x-4+(6*x+1-1)) with (18*x-4) by lia.
  replace (h+1+1) with (h+2) by lia.
  replace (6*x+1) with (2*(3*x)+1) at 3 by lia.
  rewrite (positive_page_row (18*x-4) (2*h+7) [h+2;h;h+1]) by lia.
  replace (18*x-4+(2*b+3-1)) with (18*x+2*b-2) by lia.
  replace (6*x+1+1) with (6*x+2) by lia.
  replace (2*b+3) with (2*(b+1)+1) by lia; reflexivity.
Qed.

Lemma frame_pages_header t indices s v r : 2<=t ->
  exists d tail, frame_pages t indices s v r=page_header (d+2) tail.
Proof.
  intro Ht; destruct indices as [|z indices]; cbn [frame_pages];
    rewrite pure_page_header.
  - exists (t-1),(S0::page_header (t+3) (frame_body s v r)).
    replace (t-1+2) with (t+1) by lia; reflexivity.
  - exists (t-2),(S0::pure_page (t+4) (frame_pages z indices s v r)).
    replace (t-2+2) with t by lia; reflexivity.
Qed.

Lemma odd_page_frames_prefix indices t a b gaps n m h s v r :
  1<=t -> Forall (fun z => 1<=z) indices ->
  exists clock aa tail, 0<clock /\ a+2*h+3<=aa /\
    advance clock (tilted (row a (gaps++[b])++[Three]) n
      (copies (2*m+1) [S0;S1]++S0::
        pure_page (2*h+3) (frame_pages t indices s v r))) =
    counter_pair aa (b+1) (saved_pages gaps (pure_page (n+1) tail)).
Proof.
  intros Ht Hindices.
  destruct (frame_pages_return indices Hindices t (a+2*h+2) b ((n+1)::gaps)
    m (h+1) s v r Ht) as [clock [delta [tail [Hclock Hreturn]]]].
  exists (page_clock (row a (gaps++[b])) n m (2*h+3)+clock),
    (a+2*h+2+delta+1),tail.
  split; [lia |]; split; [lia |].
  rewrite advance_add,positive_page_row by lia.
  replace (a+(2*h+3-1)) with (a+2*h+2) by lia.
  replace (2*h+3) with (2*(h+1)+1) by lia.
  rewrite Hreturn; cbn [saved_pages]; reflexivity.
Qed.

Lemma even_page_header_return a b gaps n m z d r :
  Progress (tilted (row a (gaps++[b])++[Three]) n
    (copies (2*m+1) [S0;S1]++S0::pure_page (2*z+2) (page_header (d+2) r)))
    (counter_pair (a+2*z+2) (b+1)
      (saved_pages gaps (pure_page (n+2) (saved_body m (z+1) (repeat Three d) r)))).
Proof.
  exists (page_clock (row a (gaps++[b])) n m (2*z+2)+
    (4*m+30*(z+1)+2*weight (repeat Three d)+113+
     row_clock (a+(2*z+1)) (((n+2)::gaps)++[b]))).
  split; [lia |].
  rewrite advance_add,positive_page_row by lia.
  replace (a+(2*z+2-1)) with (a+(2*z+1)) by lia.
  replace (2*z+2) with (2*(z+1)) by lia.
  rewrite header_core.
  cbn [app]; rewrite row_last_three.
  replace (S (n+1)) with (n+2) by lia.
  rewrite (T_core_odd_frontier (a+(2*z+1)) b ((n+2)::gaps)).
  unfold paired_frontier,counter_pair,G; cbn [saved_pages].
  replace (S (a+(2*z+1))) with (a+2*z+2) by lia.
  replace (S b) with (b+1) by lia; reflexivity.
Qed.

Lemma even_page_frames_prefix indices t a b gaps n m h s v r :
  2<=t -> exists tail,
  Progress (tilted (row a (gaps++[b])++[Three]) n
    (copies (2*m+1) [S0;S1]++S0::
      pure_page (2*h+4) (frame_pages t indices s v r)))
    (counter_pair (a+2*h+4) (b+1) (saved_pages gaps (pure_page (n+2) tail))).
Proof.
  intro Ht; destruct (frame_pages_header t indices s v r Ht) as [d [tail Hform]].
  exists (saved_body m (h+2) (repeat Three d) tail).
  rewrite Hform.
  replace (2*h+4) with (2*(h+1)+2) by lia.
  replace (a+2*h+4) with (a+2*(h+1)+2) by lia.
  replace (h+2) with (h+1+1) by lia.
  apply even_page_header_return.
Qed.

Lemma odd_even_header_return a b gaps n m h z d r :
  Progress (tilted (row a (gaps++[b])++[Three]) n
    (copies (2*m+1) [S0;S1]++S0::
      pure_page (2*h+3) (pure_page (2*z+2) (page_header (d+2) r))))
    (counter_pair (a+2*h+2*z+4) (b+1)
      (saved_pages gaps (pure_page (n+1) (pure_page (m+2)
        (saved_body (h+1) (z+1) (repeat Three d) r))))).
Proof.
  destruct (even_page_header_return (a+2*h+2) b ((n+1)::gaps) m (h+1) z d r)
    as [clock [Hclock Hreturn]].
  exists (page_clock (row a (gaps++[b])) n m (2*h+3)+clock).
  split; [lia |].
  rewrite advance_add,positive_page_row by lia.
  replace (a+(2*h+3-1)) with (a+2*h+2) by lia.
  replace (2*h+3) with (2*(h+1)+1) by lia.
  rewrite Hreturn; cbn [saved_pages].
  replace (a+2*h+2+2*z+2) with (a+2*h+2*z+4) by lia; reflexivity.
Qed.

Lemma odd_triple_frames_prefix indices t a b gaps h x s v r :
  1<=x -> 1<=t -> Forall (fun z => 1<=z) indices ->
  exists clock aa tail, 0<clock /\ a+2*h+4*x+3<=aa /\
    advance clock (tilted (row a (gaps++[b])++[Three]) (3*x)
      (copies (2*(2*h+1)+1) [S0;S1]++S0::
        pure_page (2*h+3) (pure_page (2*x-1) (pure_page (2*x+3)
          (frame_pages t indices s v r))))) =
    counter_pair aa (b+1) (saved_pages gaps
      (pure_page (3*x+1) (pure_page (2*h+2) (pure_page (h+2) tail)))).
Proof.
  intros Hx Ht Hindices.
  destruct (frame_pages_return indices Hindices t (a+2*h+4*x+2) b
    ((h+2)::(2*h+2)::(3*x+1)::gaps) (x-1) (x+1) s v r Ht)
    as [clock [delta [tail [Hclock Hreturn]]]].
  exists (page_clock (row a (gaps++[b])) (3*x) (2*h+1) (2*h+3)+
    (page_clock (row (a+2*h+2) (((3*x+1)::gaps)++[b])) (2*h+1) (h+1) (2*x-1)+
     (page_clock (row (a+2*h+2*x) (((2*h+2)::(3*x+1)::gaps)++[b])) (h+1) (x-1) (2*x+3)+clock))),
    (a+2*h+4*x+2+delta+1),tail.
  split; [lia |]; split; [lia |].
  rewrite advance_add,positive_page_row by lia.
  replace (a+(2*h+3-1)) with (a+2*h+2) by lia.
  replace (2*h+3) with (2*(h+1)+1) by lia.
  rewrite advance_add,positive_page_row by lia.
  replace (a+2*h+2+(2*x-1-1)) with (a+2*h+2*x) by lia.
  replace (2*h+1+1) with (2*h+2) by lia.
  replace (2*x-1) with (2*(x-1)+1) by lia.
  rewrite advance_add,positive_page_row by lia.
  replace (a+2*h+2*x+(2*x+3-1)) with (a+2*h+4*x+2) by lia.
  replace (h+1+1) with (h+2) by lia.
  replace (2*x+3) with (2*(x+1)+1) by lia.
  rewrite Hreturn; cbn [saved_pages]; reflexivity.
Qed.

Definition q_pages_front a x b indices s v r :=
  counter_pair a (12*x+4) (pure_page (6*x+1) (pure_page (2*b+3)
    (pure_page (b+3) (frame_pages (2*x-1) indices s v r)))).

Definition K5front a c x h r := counter_pair a (2*c+2)
  (pure_page c (pure_page (6*x+2) (pure_page (3*x+1)
    (pure_page (2*h+2) (pure_page (h+2) r))))).
Definition O5front a k x offset r := counter_pair a (2*k+6)
  (pure_page k (pure_page (k-1) (pure_page (k+1)
    (pure_page (6*x+2) (pure_page (3*x+offset) r))))).
Definition KEmptyFront c x h r := counter_pair (20*x+6*h+4) (2*c+2)
  (pure_page c (pure_page (6*x+2) (pure_page (3*x+1)
    (pure_page (2*h+3) (saved_body (h+1) x (repeat Three (2*x)) r))))).
Definition BOddNonemptyFront c x h r := counter_pair (18*x+6*h+8) (2*c+2)
  (pure_page c (pure_page (6*x+2) (pure_page (3*x+2)
    (saved_body (2*h+2) (h+2) (repeat Three (2*x-3))
      (S0::pure_page (2*x+3) r))))).
Definition BOddEmptyFront c x h r := counter_pair (18*x+6*h+8) (2*c+2)
  (pure_page c (pure_page (6*x+2) (pure_page (3*x+2)
    (saved_body (2*h+2) (h+2) (repeat Three (2*x-2))
      (S0::page_header (2*x+2) r))))).

Lemma even_stage_progress k x b r :
  Progress (counter_pair (2*k+2) (12*x+4)
    (pure_page (6*x+1) (pure_page (2*b+3) r))) (even_stage k x b r).
Proof.
  exists (even_stage_clock k x b); split;
    [unfold even_stage_clock; lia |apply even_stage_return].
Qed.

Lemma q_pages_even_nonempty k x h z indices s v r :
  3<=x -> 3<=h -> 1<=z -> Forall (fun n => 1<=n) indices ->
  exists aa tail, 24<=aa /\
    Progress (q_pages_front (2*k+2) x (2*h) (z::indices) s v r)
      (K5front aa (k+1) x h tail).
Proof.
  intros Hx Hh Hz Hindices.
  destruct (odd_triple_frames_prefix indices z (18*x+2*(2*h)+2) (2*k+3)
    [6*x+2;k+1] h x s v r ltac:(lia) Hz Hindices)
    as [clock [aa [tail [Hclock [Haa Hreturn]]]]].
  exists aa,tail; split; [lia |].
  unfold q_pages_front; eapply progress_trans; [apply even_stage_progress |].
  eapply progress_rule.
  - exact Hreturn.
  - exact Hclock.
  - unfold even_stage; cbn [frame_pages]; prefix_config_eq_fast.
  - unfold K5front; prefix_config_eq_fast.
Qed.

Lemma q_pages_bodd_nonempty k x h z indices s v r : 2<=x ->
  Progress (q_pages_front (2*k+2) x (2*h+1) (z::indices) s v r)
    (BOddNonemptyFront (k+1) x h (frame_pages z indices s v r)).
Proof.
  intro Hx.
  destruct (even_page_header_return (18*x+2*(2*h+1)+2) (2*k+3) [6*x+2;k+1]
    (3*x) (2*h+2) (h+1) (2*x-3)
    (S0::pure_page (2*x+3) (frame_pages z indices s v r)))
    as [clock [Hclock Hreturn]].
  unfold q_pages_front; eapply progress_trans; [apply even_stage_progress |].
  eapply progress_rule.
  - exact Hreturn.
  - exact Hclock.
  - unfold even_stage; cbn [frame_pages]; prefix_config_eq_fast.
  - unfold BOddNonemptyFront; prefix_config_eq_fast.
Qed.

Lemma q_pages_bodd_empty k x h s v r : 2<=x ->
  Progress (q_pages_front (2*k+2) x (2*h+1) [] s v r)
    (BOddEmptyFront (k+1) x h (frame_body s v r)).
Proof.
  intro Hx.
  destruct (even_page_header_return (18*x+2*(2*h+1)+2) (2*k+3) [6*x+2;k+1]
    (3*x) (2*h+2) (h+1) (2*x-2)
    (S0::page_header (2*x+2) (frame_body s v r)))
    as [clock [Hclock Hreturn]].
  unfold q_pages_front; eapply progress_trans; [apply even_stage_progress |].
  eapply progress_rule.
  - exact Hreturn.
  - exact Hclock.
  - unfold even_stage; cbn [frame_pages]; prefix_config_eq_fast.
  - unfold BOddEmptyFront; prefix_config_eq_fast.
Qed.

Lemma odd_stage_progress h x b r : 1<=x ->
  Progress (counter_pair (2*h+3) (12*x+4)
    (pure_page (6*x+1) (pure_page (2*b+3) r))) (odd_stage h x b r).
Proof.
  intro Hx; exists (odd_stage_clock h x b); split;
    [unfold odd_stage_clock; lia |apply odd_stage_return; exact Hx].
Qed.

Lemma q_pages_even_empty k x h s v r : 2<=x ->
  Progress (q_pages_front (2*k+2) x (2*h) [] s v r)
    (KEmptyFront (k+1) x h (frame_body s v r)).
Proof.
  intro Hx; unfold q_pages_front.
  eapply progress_trans; [apply even_stage_progress |].
  unfold even_stage; cbn [frame_pages].
  replace (2*x-1+1) with (2*(x-1)+2) by lia.
  replace (2*x-1+3) with (2*x+2) by lia.
  pose proof (odd_even_header_return (18*x+2*(2*h)+2) (2*k+3) [6*x+2;k+1]
    (3*x) (2*h+1) h (x-1) (2*x) (frame_body s v r)) as Hreturn.
  destruct Hreturn as [clock [Hclock Hreturn]].
  eapply progress_rule.
  - exact Hreturn.
  - exact Hclock.
  - prefix_config_eq.
  - unfold KEmptyFront,pure_page; prefix_config_eq.
Qed.

Lemma q_pages_odd k x b indices s v r :
  11<=k -> 3<=x -> 6<=b -> Forall (fun n => 1<=n) indices ->
  exists aa offset tail, 24<=aa /\ (offset=1 \/ offset=2) /\
    Progress (q_pages_front (2*k+3) x b indices s v r)
      (O5front aa (k+1) x offset tail).
Proof.
  intros Hk Hx Hb Hindices.
  pose proof (Nat.div_mod b 2 ltac:(lia)) as Hdivide.
  pose proof (Nat.mod_upper_bound b 2 ltac:(lia)) as Hmod.
  remember (b/2) as h.
  assert (Hcases : b=2*h \/ b=2*h+1) by lia.
  destruct Hcases as [Hform|Hform]; subst b.
  - destruct (odd_page_frames_prefix indices (2*x-1) (18*x+2*(2*h)-2)
      (2*k+7) [6*x+2;k+2;k;k+1] (3*x) (2*h+1) h s v r ltac:(lia) Hindices)
      as [clock [aa [tail [Hclock [Haa Hreturn]]]]].
    exists aa,1,tail; split; [lia |]; split; [left; reflexivity |].
    unfold q_pages_front; eapply progress_trans; [apply odd_stage_progress; lia |].
    eapply progress_rule.
    + exact Hreturn.
    + exact Hclock.
    + unfold odd_stage; prefix_config_eq_fast.
    + unfold O5front; prefix_config_eq_fast.
  - destruct (even_page_frames_prefix indices (2*x-1) (18*x+2*(2*h+1)-2)
      (2*k+7) [6*x+2;k+2;k;k+1] (3*x) (2*h+2) h s v r ltac:(lia))
      as [tail [clock [Hclock Hreturn]]].
    exists (18*x+2*(2*h+1)-2+2*h+4),2,tail.
    split; [lia |]; split; [right; reflexivity |].
    unfold q_pages_front; eapply progress_trans; [apply odd_stage_progress; lia |].
    eapply progress_rule.
    + exact Hreturn.
    + exact Hclock.
    + unfold odd_stage; prefix_config_eq_fast.
    + unfold O5front; prefix_config_eq_fast.
Qed.

Record aff := Aff { a0:nat; a1:nat; a2:nat; a3:nat; a4:nat }.
Definition val a (v:list nat) :=
  a0 a+a1 a*nth 0 v 0+a2 a*nth 1 v 0+a3 a*nth 2 v 0+a4 a*nth 3 v 0.
Definition cn n := Aff n 0 0 0 0.
Definition plus a b := Aff (a0 a+a0 b) (a1 a+a1 b) (a2 a+a2 b)
  (a3 a+a3 b) (a4 a+a4 b).
Definition scale k a := Aff (k*a0 a) (k*a1 a) (k*a2 a) (k*a3 a) (k*a4 a).
Definition minus a b := Aff (a0 a-a0 b) (a1 a-a1 b) (a2 a-a2 b)
  (a3 a-a3 b) (a4 a-a4 b).
Definition below a b := (a0 a<=?a0 b)&&(a1 a<=?a1 b)&&(a2 a<=?a2 b)&&
  (a3 a<=?a3 b)&&(a4 a<=?a4 b).
Definition zero a := below a (cn 0).
Definition constant a := match a1 a,a2 a,a3 a,a4 a with
  | 0,0,0,0 => Some (a0 a) | _,_,_,_ => None end.

Lemma val_cn n v : val (cn n) v=n.
Proof. unfold val,cn; cbn; lia. Qed.
Lemma val_plus a b v : val (plus a b) v=val a v+val b v.
Proof. destruct a,b; unfold val,plus; cbn; nia. Qed.
Lemma val_scale k a v : val (scale k a) v=k*val a v.
Proof. destruct a; unfold val,scale; cbn; nia. Qed.
Lemma plus_minus a b : below b a=true -> plus (minus a b) b=a.
Proof.
  destruct a,b; unfold below,plus,minus; cbn.
  repeat rewrite andb_true_iff; repeat rewrite Nat.leb_le.
  intros [[[[H0 H1] H2] H3] H4]; f_equal; lia.
Qed.
Lemma val_minus a b v : below b a=true -> val (minus a b) v=val a v-val b v.
Proof.
  intro H; pose proof (f_equal (fun x=>val x v) (plus_minus a b H)) as E.
  change (val (plus (minus a b) b) v=val a v) in E.
  rewrite val_plus in E; lia.
Qed.
Lemma val_zero a v : zero a=true -> val a v=0.
Proof.
  intro H; pose proof (plus_minus (cn 0) a H) as E.
  apply (f_equal (fun x=>val x v)) in E.
  change (val (plus (minus (cn 0) a) a) v=val (cn 0) v) in E.
  rewrite val_plus,val_cn in E; lia.
Qed.
Lemma val_constant a n v : constant a=Some n -> val a v=n.
Proof.
  destruct a as [c d e f g]; unfold constant; cbn.
  destruct d,e,f,g; try discriminate; intro H; inversion H; apply val_cn.
Qed.

Inductive ne := C (n:nat) | X (i:nat) | Add (a b:ne) | Mul (a b:ne) | Sub (a b:ne).
Fixpoint nv e v := match e with
  | C n=>n | X i=>nth i v 0 | Add a b=>nv a v+nv b v
  | Mul a b=>nv a v*nv b v | Sub a b=>nv a v-nv b v end.
Fixpoint norm e : option aff := match e with
  | C n=>Some(cn n)
  | X 0=>Some(Aff 0 1 0 0 0) | X 1=>Some(Aff 0 0 1 0 0)
  | X 2=>Some(Aff 0 0 0 1 0) | X 3=>Some(Aff 0 0 0 0 1) | X _=>None
  | Add x y => match norm x,norm y with
    | Some a,Some b=>Some(plus a b) | _,_=>None end
  | Mul x y => match norm x,norm y with
    | Some a,Some b=>match constant a with
      | Some k=>Some(scale k b)
      | None=>match constant b with Some k=>Some(scale k a) | None=>None end end
    | _,_=>None end
  | Sub x y=>match norm x,norm y with
    | Some a,Some b=>if below b a then Some(minus a b) else None
    | _,_=>None end end.

Lemma norm_sound e a : norm e=Some a -> forall v, nv e v=val a v.
Proof.
  revert a; induction e; intros a H v; cbn in H.
  - inversion H; subst; cbn [nv]; symmetry; apply val_cn.
  - destruct i as [|[|[|[|i]]]]; try discriminate; inversion H; subst;
      unfold val; cbn [nv a0 a1 a2 a3 a4]; lia.
  - destruct (norm e1) as [p|] eqn:Hp; try discriminate.
    destruct (norm e2) as [q|] eqn:Hq; try discriminate.
    inversion H; cbn [nv]; rewrite (IHe1 p eq_refl v),(IHe2 q eq_refl v),val_plus; reflexivity.
  - destruct (norm e1) as [p|] eqn:Hp; try discriminate.
    destruct (norm e2) as [q|] eqn:Hq; try discriminate.
    cbn [nv]; rewrite (IHe1 p eq_refl v),(IHe2 q eq_refl v).
    destruct (constant p) as [k|] eqn:Hk.
    + inversion H; rewrite val_scale,(val_constant p k v Hk); reflexivity.
    + destruct (constant q) as [k|] eqn:Hqk; try discriminate.
      inversion H; rewrite val_scale,(val_constant q k v Hqk); nia.
  - destruct (norm e1) as [p|] eqn:Hp; try discriminate.
    destruct (norm e2) as [q|] eqn:Hq; try discriminate.
    destruct (below q p) eqn:Hle; try discriminate.
    inversion H; cbn [nv]; rewrite (IHe1 p eq_refl v),(IHe2 q eq_refl v).
    symmetry; apply val_minus; exact Hle.
Qed.

Fixpoint bits_eq x y := match x,y with
  | [],[]=>true | a::x,b::y=>sym_eqb a b&&bits_eq x y | _,_=>false end.
Lemma bits_eq_sound x y : bits_eq x y=true -> x=y.
Proof.
  revert y; induction x; destruct y; cbn; try discriminate; auto.
  rewrite andb_true_iff; intros [H T]; apply (proj2 (Bool.reflect_iff _ _ (sym_eqb_spec _ _))) in H; subst.
  f_equal; apply IHx; exact T.
Qed.

Inductive atom := Rep (a:aff) (w:list Sym) | Tail.
Definition av t v r := match t with Rep a w=>copies (val a v) w | Tail=>r end.
Fixpoint run xs v r := match xs with []=>[] | x::xs=>av x v r++run xs v r end.
Lemma run_app xs ys v r : run (xs++ys) v r=run xs v r++run ys v r.
Proof. induction xs; cbn; [reflexivity|rewrite IHxs,app_assoc; reflexivity]. Qed.
Lemma copies_nil n : copies n (@nil Sym)=[].
Proof. induction n; cbn; auto. Qed.
Lemma copies_twice n w : copies n (w++w)=copies (2*n) w.
Proof.
  induction n; [reflexivity|].
  replace (2*S n) with (S(S(2*n))) by lia.
  cbn [copies]; rewrite IHn; repeat rewrite app_assoc; reflexivity.
Qed.
Definition power a w :=
  if bits_eq w [S0;S1;S0;S1] then [Rep (scale 2 a) [S0;S1]] else
  if bits_eq w [S1;S0;S1;S0] then [Rep (scale 2 a) [S1;S0]] else [Rep a w].
Lemma power_sound a w v r : run (power a w) v r=copies (val a v) w.
Proof.
  unfold power; destruct (bits_eq w [S0;S1;S0;S1]) eqn:H.
  - apply bits_eq_sound in H; subst; cbn [run av]; rewrite app_nil_r,val_scale.
    symmetry; apply (copies_twice (val a v) [S0;S1]).
  - destruct (bits_eq w [S1;S0;S1;S0]) eqn:H2.
    + apply bits_eq_sound in H2; subst; cbn [run av]; rewrite app_nil_r,val_scale.
      symmetry; apply (copies_twice (val a v) [S1;S0]).
    + cbn [run av]; apply app_nil_r.
Qed.

Inductive ce := CNil | CCat (a b:ce) | CBlock (b:block) | CRepeat (n:ne).
Fixpoint cv c v := match c with
  | CNil=>[] | CCat a b=>cv a v++cv b v | CBlock b=>[b]
  | CRepeat n=>repeat Three (nv n v) end.
Definition view (rev:bool) c := if rev then pushed_core c else core_bits c.
Definition bitview (rev:bool) b := if rev then pushed_bits b else block_bits b.
Lemma view_app rev a b : view rev (a++b)=
  if rev then view rev b++view rev a else view rev a++view rev b.
Proof. destruct rev; unfold view; [apply pushed_core_app|apply core_bits_app]. Qed.
Lemma view_repeat rev n : view rev (repeat Three n)=copies n (bitview rev Three).
Proof. destruct rev; unfold view,bitview; [apply pushed_threes|apply core_bits_threes]. Qed.
Lemma view_block rev b : view rev [b]=bitview rev b.
Proof. destruct rev,b; reflexivity. Qed.
Fixpoint compile_core (rev:bool) c : option (list atom) := match c with
  | CNil=>Some [] | CBlock b=>Some(power (cn 1) (bitview rev b))
  | CRepeat n=>match norm n with Some a=>Some(power a (bitview rev Three)) | None=>None end
  | CCat a b=>match compile_core rev a,compile_core rev b with
    | Some x,Some y=>Some(if rev then y++x else x++y) | _,_=>None end end.
Lemma compile_core_sound c rev xs : compile_core rev c=Some xs ->
  forall v r, view rev (cv c v)=run xs v r.
Proof.
  revert xs; induction c; intros xs H v r; cbn [compile_core] in H.
  - inversion H; subst; destruct rev; reflexivity.
  - destruct (compile_core rev c1) as [p|] eqn:Hp; try discriminate.
    destruct (compile_core rev c2) as [q|] eqn:Hq; try discriminate.
    inversion H; subst; cbn [cv]; rewrite view_app.
    rewrite (IHc1 p eq_refl v r),(IHc2 q eq_refl v r).
    destruct rev; apply eq_sym; apply run_app.
  - inversion H; subst; cbn [cv]; rewrite power_sound,val_cn,view_block.
    cbn [copies]; symmetry; apply app_nil_r.
  - destruct (norm n) as [a|] eqn:Ha; try discriminate.
    inversion H; subst; cbn [cv]; rewrite power_sound,view_repeat,(norm_sound n a Ha v); reflexivity.
Qed.

Inductive we := Empty | Cat (a b:we) | Pow (n:ne) (w:list Sym) | Rest
  | Core (rev:bool) (c:ce).
Fixpoint wv e v r := match e with
  | Empty=>[] | Cat a b=>wv a v r++wv b v r | Pow n w=>copies (nv n v) w | Rest=>r
  | Core rev c=>view rev (cv c v) end.
Fixpoint compile e : option (list atom) := match e with
  | Empty=>Some [] | Rest=>Some [Tail]
  | Core rev c=>compile_core rev c
  | Pow n w=>match norm n with Some a=>Some(power a w) | None=>None end
  | Cat a b=>match compile a,compile b with Some x,Some y=>Some(x++y) | _,_=>None end end.
Lemma compile_sound e xs : compile e=Some xs -> forall v r, wv e v r=run xs v r.
Proof.
  revert xs; induction e; intros xs H v r; cbn in H.
  - inversion H; reflexivity.
  - destruct (compile e1) as [p|] eqn:Hp; try discriminate.
    destruct (compile e2) as [q|] eqn:Hq; try discriminate.
    inversion H; cbn [wv]; rewrite (IHe1 p eq_refl v r),(IHe2 q eq_refl v r),run_app; reflexivity.
  - destruct (norm n) as [a|] eqn:Ha; try discriminate.
    inversion H; cbn [wv]; rewrite (norm_sound n a Ha v),power_sound; reflexivity.
  - inversion H; cbn [wv run av]; symmetry; apply app_nil_r.
  - cbn [wv]; apply compile_core_sound; exact H.
Qed.

Definition empty_atom x := match x with Rep a w=>zero a||match w with []=>true | _=>false end | Tail=>false end.
Lemma empty_atom_sound x : empty_atom x=true -> forall v r, av x v r=[].
Proof.
  destruct x as [a w|]; cbn; try discriminate; rewrite orb_true_iff; intros [H|H] v r.
  - rewrite (val_zero a v H); reflexivity.
  - destruct w; try discriminate; apply copies_nil.
Qed.
Fixpoint trim xs := match xs with
  | []=>[] | x::ys=>if empty_atom x then trim ys else xs end.
Lemma trim_sound xs v r : run (trim xs) v r=run xs v r.
Proof.
  induction xs as [|x xs IH]; [reflexivity|]; cbn [trim].
  destruct (empty_atom x) eqn:H; [|reflexivity].
  cbn [run]; rewrite (empty_atom_sound x H v r); cbn; exact IH.
Qed.

Definition cancel xs ys : option (list atom*list atom) := match xs,ys with
  | Tail::xs,Tail::ys=>Some(xs,ys)
  | Rep a w::xs,Rep b z::ys=>if bits_eq w z then
      if below a b then Some(xs,Rep (minus b a) z::ys) else
      if below b a then Some(Rep (minus a b) w::xs,ys) else None
    else None
  | _,_=>None end.
Lemma count_split a b w v : below a b=true ->
  copies (val b v) w=copies (val a v) w++copies (val (minus b a) v) w.
Proof.
  intro H; pose proof (plus_minus b a H) as E.
  apply (f_equal (fun x=>val x v)) in E.
  change (val (plus (minus b a) a) v=val b v) in E.
  rewrite val_plus in E.
  replace (val b v) with (val a v+val (minus b a) v) by lia; apply copies_add.
Qed.
Lemma cancel_sound xs ys p q : cancel xs ys=Some(p,q) ->
  forall v r, run p v r=run q v r -> run xs v r=run ys v r.
Proof.
  destruct xs as [|x xs]; [destruct ys as [|[b z|] ys]; discriminate|].
  destruct ys as [|y ys]; [destruct x; discriminate|].
  destruct x as [a w|],y as [b z|]; cbn [cancel]; try discriminate.
  - destruct (bits_eq w z) eqn:Hw; try discriminate.
    apply bits_eq_sound in Hw; subst z.
    destruct (below a b) eqn:Hab.
    + intro H; inversion H; subst; intros v r E; cbn [run av] in *.
      rewrite (count_split a b w v Hab),<-app_assoc,E; reflexivity.
    + destruct (below b a) eqn:Hba; try discriminate.
      intro H; inversion H; subst; intros v r E; cbn [run av] in *.
      rewrite (count_split b a w v Hba),<-app_assoc,E; reflexivity.
  - intro H; inversion H; subst; intros v r E; cbn [run av]; rewrite E; reflexivity.
Qed.

Lemma rotate_copies n b w r :
  copies n (b::w)++b::r=b::(copies n (w++[b])++r).
Proof.
  induction n; [reflexivity|]; cbn [copies].
  cbn [app]; repeat rewrite <-app_assoc.
  rewrite IHn; cbn [app]; repeat rewrite <-app_assoc; reflexivity.
Qed.
Definition dec a := Aff (a0 a-1) (a1 a) (a2 a) (a3 a) (a4 a).
Lemma val_dec a v : 0<a0 a -> val a v=S(val (dec a) v).
Proof. destruct a; unfold val,dec; cbn; lia. Qed.

Fixpoint expose xs : option (Sym*list atom) := match xs with
  | []=>None | Tail::_=>None
  | Rep a []::ys=>expose ys
  | Rep a (b::w)::ys=>if zero a then expose ys else
    match a0 a with
    | S _=>Some(b,Rep (cn 1) w::Rep (dec a) (b::w)::ys)
    | 0=>match expose ys with
      | Some(c,zs)=>if sym_eqb b c then Some(b,Rep a (w++[b])::zs) else None
      | None=>None end end end.
Lemma expose_sound xs b ys : expose xs=Some(b,ys) ->
  forall v r, run xs v r=b::run ys v r.
Proof.
  revert b ys; induction xs as [|x xs IH]; intros b ys H v r; try discriminate.
  destruct x as [a w|]; try discriminate; destruct w as [|c w].
  - cbn [expose] in H; cbn [run av]; rewrite copies_nil; cbn; apply IH; exact H.
  - cbn [expose] in H; destruct (zero a) eqn:Hz.
    + cbn [run av]; rewrite (val_zero a v Hz); cbn [copies app]; apply IH; exact H.
    + destruct (a0 a) eqn:Hn.
      * destruct (expose xs) as [[d zs]|] eqn:He; try discriminate.
        destruct (sym_eqb c d) eqn:Hcd; try discriminate.
        apply (proj2 (Bool.reflect_iff _ _ (sym_eqb_spec _ _))) in Hcd; subst d; inversion H; subst.
        cbn [run av]; rewrite (IH b zs eq_refl v r); apply rotate_copies.
      * inversion H; subst; cbn [run av]; rewrite (val_dec a v ltac:(lia)),val_cn.
        cbn [copies]; repeat rewrite <-app_assoc; reflexivity.
Qed.

Definition both_empty (xs ys:list atom) := match xs,ys with [],[]=>true | _,_=>false end.
Fixpoint word_check fuel xs ys := match fuel with
  | 0=>false
  | S fuel=>let x:=trim xs in let y:=trim ys in
    if both_empty x y then true else
    match cancel x y with
    | Some(p,q)=>word_check fuel p q
    | None=>match expose x,expose y with
      | Some(b,p),Some(c,q)=>sym_eqb b c&&word_check fuel p q
      | _,_=>false end end end.
Lemma word_check_sound fuel xs ys : word_check fuel xs ys=true ->
  forall v r, run xs v r=run ys v r.
Proof.
  revert xs ys; induction fuel as [|fuel IH]; intros xs ys H v r; try discriminate.
  cbn [word_check] in H.
  rewrite <-(trim_sound xs v r),<-(trim_sound ys v r).
  remember (trim xs) as x in *; remember (trim ys) as y in *.
  destruct (both_empty x y) eqn:He.
  - destruct x,y; try discriminate; reflexivity.
  - destruct (cancel x y) as [[p q]|] eqn:Hc.
    + eapply cancel_sound; [exact Hc|]; apply IH; exact H.
    + destruct (expose x) as [[b p]|] eqn:Hx; try discriminate.
      destruct (expose y) as [[c q]|] eqn:Hy; try discriminate.
      apply andb_true_iff in H; destruct H as [Hbc Hrest].
      apply (proj2 (Bool.reflect_iff _ _ (sym_eqb_spec _ _))) in Hbc; subst c.
      rewrite (expose_sound x b p Hx v r),(expose_sound y b q Hy v r).
      f_equal; apply IH; exact Hrest.
Qed.

Definition word_equal fuel a b := match compile a,compile b with
  | Some x,Some y=>word_check fuel x y | _,_=>false end.
Definition fuel := 10000.
Lemma word_equal_sound fuel a b : word_equal fuel a b=true ->
  forall v r, wv a v r=wv b v r.
Proof.
  unfold word_equal; destruct (compile a) as [x|] eqn:Hx; try discriminate.
  destruct (compile b) as [y|] eqn:Hy; try discriminate.
  intros H v r; rewrite (compile_sound a x Hx v r),(compile_sound b y Hy v r).
  apply (word_check_sound fuel x y H v r).
Qed.
Definition lit bits := Pow (C 1) bits.
Definition addn x n := Add x (C n).
Definition succ x := Add (C 1) x.
Definition twice x n := Add (Mul (C 2) x) (C n).
Definition conscore b c := CCat (CBlock b) c.
Definition cs := (we*we)%type.
Definition denote (s:cs) v r := cfg D (wv (fst s) v r) S0 (wv (snd s) v r).
Definition pair a b r : cs := (Empty,
  Cat (lit [S1;S1;S1;S1;S0])
    (Cat (Pow a [S1;S1;S1;S0])
      (Cat (lit [S0]) (Cat (Pow b [S1;S1;S1;S0]) (Cat (lit [S0;S0]) r))))).
Definition tilt w n r : cs :=
  (Cat (lit [S0;S1]) (Cat (Pow (addn n 2) [S0;S1;S0;S1])
    (Cat (lit [S1;S0;S1;S0;S1]) (Cat (Core true w) (lit [S0;S1])))),r).
Definition carry w r : cs :=
  (Cat (lit [S0;S0;S1]) (Cat (Core true w) (lit [S0;S1])),r).
Definition wfront w r : cs :=
  (Empty,Cat (lit [S1;S0]) (Cat (Core false w) (Cat (lit [S0]) r))).
Definition suffix m v r := Cat (Pow m [S0;S1])
  (Cat (Core false (conscore Three (CCat v (CBlock Three)))) (Cat (lit [S0]) r)).
Definition body n m v r := Cat (lit [S1;S1;S1;S1;S0])
  (Cat (Pow (succ n) [S1;S1;S1;S0]) (Cat (lit [S0])
    (Cat (Pow (succ m) [S1;S1;S1;S0]) (Cat (lit [S1;S1;S1;S1;S1;S1;S0])
      (Cat (Core false v) (Cat (lit [S0;S0;S1;S0;S1]) r)))))).
Definition pg b r := Cat (lit [S1;S1;S1;S1;S0])
  (Cat (Core false (CRepeat b)) (Cat (lit [S0;S0]) r)).
Fixpoint pages gaps r := match gaps with []=>r | b::bs=>pages bs (pg b r) end.
Fixpoint crow a gaps := match gaps with
  | []=>CRepeat a | b::bs=>CCat (crow a bs) (conscore Six (CRepeat b)) end.
Definition outer h := conscore Six (CCat (CRepeat (twice h 7))
  (conscore Six (CCat (CRepeat (addn h 1)) (conscore Six (CRepeat (addn h 1)))))).

Lemma denote_pair a b t v r : denote (pair a b t) v r=counter_pair (nv a v) (nv b v) (wv t v r).
Proof. reflexivity. Qed.
Lemma denote_tilt w n t v r : denote (tilt w n t) v r=tilted (cv w v) (nv n v) (wv t v r).
Proof. reflexivity. Qed.
Lemma denote_carry w t v r : denote (carry w t) v r=carried (cv w v) (wv t v r).
Proof. reflexivity. Qed.
Lemma denote_wfront w t v r : denote (wfront w t) v r=W (cv w v) (wv t v r).
Proof. reflexivity. Qed.
Lemma value_suffix m c t v r : wv (suffix m c t) v r=core_suffix (nv m v) (cv c v) (wv t v r).
Proof. reflexivity. Qed.
Lemma value_body n m c t v r : wv (body n m c t) v r=saved_body (nv n v) (nv m v) (cv c v) (wv t v r).
Proof. reflexivity. Qed.
Lemma value_crow a gaps v : cv (crow a gaps) v=row (nv a v) (map (fun e=>nv e v) gaps).
Proof. induction gaps; cbn [crow cv row map conscore]; [reflexivity|rewrite IHgaps; reflexivity]. Qed.
Lemma value_outer h v : cv (outer h) v=odd_outer (nv h v).
Proof. reflexivity. Qed.
Lemma value_pages gaps t v r : wv (pages gaps t) v r=saved_pages (map (fun e=>nv e v) gaps) (wv t v r).
Proof.
  revert t; induction gaps; intro t; [reflexivity|].
  cbn [pages map saved_pages]; rewrite IHgaps; unfold pg,page; cbn [wv lit nv cv view];
    repeat rewrite <-app_assoc; reflexivity.
Qed.
Lemma pair_front a b t v r : denote (pair (succ a) (succ b) t) v r=
  paired_frontier (nv a v) (nv b v) (wv t v r).
Proof. reflexivity. Qed.

Inductive instruction :=
| PE (k b:ne) (t:we)
| PO (h b:ne) (t:we)
| TE (w:ce) (n m:ne) (v:ce) (t:we)
| CR (u v:ce) (t:we)
| WM (w:ce) (n b:ne) (t:we)
| TO (a b:ne) (gaps:list ne) (n m:ne) (v:ce) (t:we)
| PP (u:ce) (n m c:ne) (t:we).

Definition instruction_source i : cs := match i with
| PE k b t=>pair (twice k 2) (addn b 4) t
| PO h b t=>pair (twice h 3) (addn b 8) t
| TE w n m v t=>tilt w n (suffix (twice m 2) v t)
| CR u v t=>carry (CCat u (CBlock Three))
    (Cat (Core false (CCat v (CBlock Three))) (Cat (lit [S0]) t))
| WM w n b t=>wfront (CCat (CCat w (conscore Six (CCat (CRepeat n) (CBlock Six)))) (CRepeat b)) t
| TO a b gaps n m v t=>tilt (crow a (gaps++[b])) n (suffix (twice m 1) (CCat v (CBlock Three)) t)
| PP u n m c t=>tilt (CCat u (CBlock Three)) n
    (Cat (Pow (twice m 1) [S0;S1]) (Cat (lit [S0;S1;S1;S1;S1;S0])
      (Cat (Pow c [S1;S1;S1;S0]) (Cat (lit [S0]) t)))) end.

Definition instruction_target i : cs := match i with
| PE k b t=>tilt (CCat (CRepeat b) (conscore Six (CRepeat (twice k 4)))) k
    (Cat (Pow (addn b 3) [S0;S1]) (Cat (lit [S0]) t))
| PO h b t=>tilt (CCat (CRepeat b) (outer h)) (addn h 1)
    (Cat (Pow (addn b 7) [S0;S1]) (Cat (lit [S0]) t))
| TE w n m v t=>carry w (Cat (Pow (addn n 2) [S1;S1;S1;S0])
    (Cat (lit [S1;S1;S1;S1;S1;S1;S0]) (Cat (Pow m [S1;S1;S1;S0])
      (Cat (lit [S1;S1;S1;S1;S1;S1;S0]) (Cat (Core false v) (Cat (lit [S0;S0;S1]) t))))))
| CR u v t=>wfront (conscore Three (CCat u (conscore Six v))) (Cat (lit [S0;S1]) t)
| WM w n b t=>tilt (CCat (CRepeat b) w) n (Cat (Pow b [S0;S1]) t)
| TO a b gaps n m v t=>pair (succ a) (succ b) (pages gaps (body n m v t))
| PP u n m c t=>tilt (CCat (CRepeat (Sub c (C 1))) (CCat u (conscore Six (CRepeat (addn n 2))))) m
    (Cat (Pow c [S0;S1]) t) end.

Definition instruction_valid i := match i with
  | PP _ _ _ c _=>match norm c with Some a=>0<?a0 a | None=>false end
  | _=>true end.
Lemma valid_positive c : (match norm c with Some a=>0<?a0 a | None=>false end)=true ->
  forall v, 0<nv c v.
Proof.
  destruct (norm c) as [a|] eqn:H; try discriminate.
  intros Hpos v; apply Nat.ltb_lt in Hpos; rewrite (norm_sound c a H v).
  unfold val; lia.
Qed.

Lemma instruction_sound i : instruction_valid i=true -> forall v r,
  Progress (denote (instruction_source i) v r) (denote (instruction_target i) v r).
Proof.
  destruct i; intros Hvalid env r; cbn [instruction_source instruction_target].
  - rewrite !denote_pair,!denote_tilt; cbn [cv conscore nv twice addn wv lit].
    eexists; split; [|apply paired_even]; lia.
  - rewrite !denote_pair,!denote_tilt; cbn [cv]; rewrite value_outer; cbn [nv twice addn wv lit].
    eexists; split; [|apply paired_odd]; lia.
  - rewrite denote_tilt,denote_carry,value_suffix; cbn [nv twice wv addn lit view].
    eexists; split; [|apply T_core_even]; lia.
  - rewrite denote_carry,denote_wfront; cbn [cv conscore wv lit view].
    eexists; split; [|apply carried_return]; lia.
  - rewrite denote_wfront,denote_tilt; cbn [cv conscore wv].
    eexists; split; [|apply W_multi_six_phase]; lia.
  - rewrite denote_tilt,pair_front,value_crow,value_suffix,value_pages,value_body,map_app.
    cbn [map cv nv twice]; eexists; split; [|apply T_core_odd_frontier]; lia.
  - pose proof (valid_positive c Hvalid env) as Hc.
    rewrite !denote_tilt; cbn [cv conscore nv addn twice wv lit].
    eexists; split; [|apply T_positive_page; exact Hc]; unfold page_clock; nia.
Qed.

Definition config_equal a b := word_equal fuel (fst a) (fst b)&&word_equal fuel (snd a) (snd b).
Lemma config_equal_sound a b : config_equal a b=true -> forall v r, denote a v r=denote b v r.
Proof.
  unfold config_equal; rewrite andb_true_iff; intros [Hl Hr] v r; unfold denote.
  rewrite (word_equal_sound fuel _ _ Hl v r),(word_equal_sound fuel _ _ Hr v r); reflexivity.
Qed.
Fixpoint path_check current instructions final := match instructions with
  | []=>false
  | i::rest=>instruction_valid i&&config_equal current (instruction_source i)&&
      match rest with []=>config_equal (instruction_target i) final | _=>path_check (instruction_target i) rest final end end.
Lemma path_check_sound current instructions final : path_check current instructions final=true ->
  forall v r, Progress (denote current v r) (denote final v r).
Proof.
  revert current; induction instructions as [|i rest IH]; intros current H v r; try discriminate.
  cbn [path_check] in H; apply andb_true_iff in H; destruct H as [Hhead Hrest].
  apply andb_true_iff in Hhead; destruct Hhead as [Hvalid Hsame].
  rewrite (config_equal_sound current (instruction_source i) Hsame v r).
  destruct rest as [|j rest].
  - rewrite <-(config_equal_sound (instruction_target i) final Hrest v r); apply instruction_sound; exact Hvalid.
  - eapply progress_trans; [apply instruction_sound; exact Hvalid|].
    apply IH; exact Hrest.
Qed.
Definition aplus n a := plus (cn n) a.
Definition asub a n := minus a (cn n).
Definition adiv a n := Aff (a0 a/n) (a1 a/n) (a2 a/n) (a3 a/n) (a4 a/n).
Definition anorm e := match norm e with Some a=>a | None=>cn 0 end.
Definition term k i := match k with 0=>[] | 1=>[X i] | _=>[Mul (C k) (X i)] end.
Definition quote a :=
  let xs := (if a0 a =? 0 then [] else [C (a0 a)]) ++
    term (a1 a) 0 ++ term (a2 a) 1 ++ term (a3 a) 2 ++ term (a4 a) 3 in
  match xs with []=>C 0 | x::xs=>fold_left Add xs x end.
Fixpoint word xs := match xs with
  | []=>Empty | [Tail]=>Rest | Tail::xs=>Cat Rest (word xs)
  | Rep a w::xs=>Cat (Pow (quote a) w) (word xs) end.
Definition atoms w := match compile w with Some xs=>xs | None=>[] end.
Definition u := [S1;S1;S1;S0].
Definition six := [S1;S1;S1;S1;S1;S1;S0].
Definition alt := [S0;S1].
Fixpoint join xs ys := match xs,ys with
  | [],_=>ys | _,[]=>xs | [x],y::ys=>plus x y::ys
  | x::xs,_=>x::join xs ys end.
Fixpoint counts c := match c with
  | CNil=>[cn 0] | CBlock Three=>[cn 1] | CBlock Six=>[cn 0;cn 0]
  | CRepeat n=>[anorm n] | CCat x y=>join (counts x) (counts y) end.
Fixpoint core xs := match xs with
  | []=>CNil | [a]=>CRepeat (quote a)
  | a::xs=>CCat (CRepeat (quote a)) (CCat (CBlock Six) (core xs)) end.
Definition reduce_ends xs a b := match xs with
  | []=>[] | x::xs=>let ys:=rev (asub x a::xs) in
      match ys with []=>[] | y::ys=>rev (asub y b::ys) end end.

Fixpoint drop (n:aff) xs :=
  if zero n then xs else match xs with
  | Rep a w::xs=>
      if zero a then drop n xs else
      let width:=List.length w in
      if below (scale width a) n then drop (minus n (scale width a)) xs else
      let q:=adiv n width in
      let rem:=a0 n mod width in
      if rem =? 0 then Rep (minus a q) w::xs else
      Rep (cn 1) (skipn rem w)::Rep (minus a (aplus 1 q)) w::xs
  | _=>xs end.
Fixpoint mismatch fuel j offset w p := match fuel with
  | 0=>None
  | S fuel=>if sym_eqb (nth (j mod List.length w) w S0)
      (nth ((offset+j) mod List.length p) p S0)
    then mismatch fuel (S j) offset w p else Some j end.
Fixpoint matching p xs matched := match xs with
  | Rep a w::xs=>
      if zero a then matching p xs matched else
      let width:=List.length w in
      match mismatch (width*List.length p) 0 (a0 matched mod List.length p) w p with
      | None=>matching p xs (plus matched (scale width a))
      | Some j=>if below (scale width a) (cn j)
          then matching p xs (plus matched (scale width a))
          else plus matched (cn j) end
  | _=>matched end.
Definition prefix p xs :=
  let n:=adiv (matching p xs (cn 0)) (List.length p) in
  (n,drop (scale (List.length p) n) xs).
Definition starts p xs := 0 <? a0 (fst (prefix p xs)).
Fixpoint parse_more fuel xs := match fuel with
  | 0=>([],xs)
  | S fuel=>if starts six xs then
      let '(a,ys):=prefix u (drop (cn 7) xs) in
      let '(cs,zs):=parse_more fuel ys in (a::cs,zs)
    else ([],xs) end.
Definition parse_core xs :=
  let '(a,ys):=prefix u xs in
  let '(cs,zs):=parse_more 64 ys in (a::cs,zs).

Inductive macro_mode := Pair | Tilt | Carried | WFront.
Record macro_state := State { mode_of:macro_mode; core_of:list aff; counter:aff; right_of:list atom }.
Definition reconstruction_start (s:cs) := State Pair [cn 0] (cn 0) (atoms (snd s)).
Definition infer_instruction s :=
  let w:=core_of s in let n:=quote (counter s) in let r:=right_of s in
  match mode_of s with
  | Pair=>
      let '(a,r):=prefix u (drop (cn 5) r) in
      let '(b,r):=prefix u (drop (cn 1) r) in
      let tail:=word (drop (cn 2) r) in
      if Nat.even (a0 a)
      then PE (quote (adiv (asub a 2) 2)) (quote (asub b 4)) tail
      else PO (quote (adiv (asub a 3) 2)) (quote (asub b 8)) tail
  | Tilt=>
      let '(p,r):=prefix alt r in
      let '(c,r):=parse_core r in
      let tail:=word (drop (cn 1) r) in
      if Nat.even (a0 p) then
        let m:=quote (asub (adiv p 2) 1) in
        match c with
        | [a]=>PP (core (reduce_ends w 0 1)) n m (quote (asub a 1)) tail
        | _=>TE (core w) n m (core (reduce_ends c 1 1)) tail end
      else TO (quote (nth 0 w (cn 0))) (quote (nth 1 w (cn 0)))
        (map quote (rev (skipn 2 w))) n (quote (adiv p 2))
        (core (reduce_ends c 1 2)) tail
  | Carried=>let '(c,r):=parse_core r in
      CR (core (reduce_ends w 0 1)) (core (reduce_ends c 0 1)) (word (drop (cn 1) r))
  | WFront=>
      let rw:=rev w in
      let b:=nth 0 rw (cn 0) in let k:=nth 1 rw (cn 0) in
      let v:=rev (skipn 2 rw) in
      let width:=aplus (7*(List.length w-1)) (scale 4 (fold_left plus w (cn 0))) in
      WM (core v) (quote k) (quote b) (word (drop (aplus 3 width) r)) end.
Definition reconstruction_next i :=
  let r:=atoms (snd (instruction_target i)) in
  match i with
  | PE k b _=>State Tilt (counts (CCat (CRepeat b) (conscore Six (CRepeat (twice k 4))))) (anorm k) r
  | PO h b _=>State Tilt (counts (CCat (CRepeat b) (outer h))) (anorm (addn h 1)) r
  | TE w _ _ _ _=>State Carried (counts w) (cn 0) r
  | CR u v _=>State WFront (counts (conscore Three (CCat u (conscore Six v)))) (cn 0) r
  | WM w n b _=>State Tilt (counts (CCat (CRepeat b) w)) (anorm n) r
  | TO _ _ _ _ _ _ _=>State Pair [cn 0] (cn 0) r
  | PP u n m c _=>State Tilt
      (counts (CCat (CRepeat (Sub c (C 1))) (CCat u (conscore Six (CRepeat (addn n 2))))))
      (anorm m) r end.
Fixpoint reconstruct_instructions n s := match n with
  | 0=>[] | S n=>let i:=infer_instruction s in i::reconstruct_instructions n (reconstruction_next i) end.
Definition macro_program n s := reconstruct_instructions n (reconstruction_start s).

Fixpoint subst_n args e := match e with
  | C n=>C n | X i=>nth i args (C 0)
  | Add a b=>Add (subst_n args a) (subst_n args b)
  | Mul a b=>Mul (subst_n args a) (subst_n args b)
  | Sub a b=>Sub (subst_n args a) (subst_n args b) end.
Fixpoint subst_c args c := match c with
  | CNil=>CNil | CBlock b=>CBlock b | CRepeat n=>CRepeat (subst_n args n)
  | CCat a b=>CCat (subst_c args a) (subst_c args b) end.
Fixpoint subst_w args tail w := match w with
  | Empty=>Empty | Rest=>tail
  | Cat a b=>Cat (subst_w args tail a) (subst_w args tail b)
  | Pow n w=>Pow (subst_n args n) w | Core b c=>Core b (subst_c args c) end.
Definition substitute args tail (s:cs) := (subst_w args tail (fst s),subst_w args tail (snd s)).
Definition values args env := map (fun e=>nv e env) args.
Lemma nth_values args i env : nv (nth i args (C 0)) env=nth i (values args env) 0.
Proof. revert i; induction args; intros [|i]; cbn [values map nth nv]; auto. Qed.
Lemma subst_n_sound args e env : nv (subst_n args e) env=nv e (values args env).
Proof. induction e; cbn [subst_n nv]; try congruence; apply nth_values. Qed.
Lemma subst_c_sound args c env : cv (subst_c args c) env=cv c (values args env).
Proof. induction c; cbn [subst_c cv]; try congruence; rewrite subst_n_sound; reflexivity. Qed.
Lemma subst_w_sound args tail w env r :
  wv (subst_w args tail w) env r=wv w (values args env) (wv tail env r).
Proof.
  induction w; cbn [subst_w wv]; try congruence.
  - rewrite subst_n_sound; reflexivity.
  - rewrite subst_c_sound; reflexivity.
Qed.
Lemma substitute_sound args tail s env r :
  denote (substitute args tail s) env r=denote s (values args env) (wv tail env r).
Proof. unfold substitute,denote; cbn [fst snd]; rewrite !subst_w_sound; reflexivity. Qed.

Definition target_family shapes c := exists s, In s shapes /\ exists env r, c=denote s env r.
Definition returns shapes c := exists d, Progress c d /\ target_family shapes d.
Fixpoint width xs := match xs with
  | []=>cn 0 | Tail::xs=>width xs
  | Rep a w::xs=>plus (scale (List.length w) a) (width xs) end.
Definition fallback : instruction := PE (C 0) (C 0) Rest.
Definition reconstructed_endpoint shapes steps which args (s:cs) :=
  let template:=nth which shapes (Empty,Empty) in
  let output:=instruction_target (last steps fallback) in
  let cut:=width (atoms (snd (substitute args Empty template))) in
  let tail:=word (drop cut (atoms (snd output))) in
  substitute args tail template.
Definition leaf_check shapes n which args s :=
  let steps:=macro_program n s in
  (which <? List.length shapes) && path_check s steps (reconstructed_endpoint shapes steps which args s).
Lemma leaf_sound shapes n which args s : leaf_check shapes n which args s=true ->
  forall env r, returns shapes (denote s env r).
Proof.
  unfold leaf_check; rewrite andb_true_iff; intros [Hwhich Hpath] env r.
  exists (denote (reconstructed_endpoint shapes (macro_program n s) which args s) env r); split.
  - exact (path_check_sound s (macro_program n s) _ Hpath env r).
  - unfold reconstructed_endpoint; rewrite substitute_sound.
    exists (nth which shapes (Empty,Empty)); split.
    + apply nth_In; apply Nat.ltb_lt; exact Hwhich.
    + eexists; eexists; reflexivity.
Qed.

Definition shift factor offset e :=
  let x:=match factor with 0=>C 0 | 1=>e | _=>Mul (C factor) e end in
  match offset with 0=>x | _=>Add x (C offset) end.
Definition variables i factor offset :=
  map (fun j=>if i =? j then shift factor offset (X j) else X j) [0;1;2;3].
Definition branch i factor offset s := substitute (variables i factor offset) Rest s.
Lemma parity (P:nat->Prop) :
  (forall n, P (2*n)) -> (forall n, P (2*n+1)) -> forall n,P n.
Proof.
  intros He Ho n.
  pose proof (Nat.div_mod n 2 ltac:(lia)) as Hd.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as Hm.
  destruct (Nat.eq_dec (n mod 2) 0).
  - replace n with (2*(n/2)) by lia; apply He.
  - replace n with (2*(n/2)+1) by lia; apply Ho.
Qed.
Lemma zero_positive (P:nat->Prop) : P 0 -> (forall n,P (n+1)) -> forall n,P n.
Proof. intros Hz Hs [|n]; [exact Hz|replace (S n) with (n+1) by lia; apply Hs]. Qed.
Definition holds (P:config->Prop) s := forall a b c d r,P (denote s [a;b;c;d] r).

Lemma parity_cover P s i : i<4 -> holds P (branch i 2 0 s) ->
  holds P (branch i 2 1 s) -> holds P s.
Proof.
  intros Hi He Ho; unfold holds in *; unfold branch in He,Ho.
  setoid_rewrite substitute_sound in He; setoid_rewrite substitute_sound in Ho.
  destruct i as [|[|[|[|i]]]]; try lia; intros a b c d r.
  - apply (parity (fun a=>P (denote s [a;b;c;d] r))); intro n;
      [exact (He n b c d r)|exact (Ho n b c d r)].
  - apply (parity (fun b=>P (denote s [a;b;c;d] r))); intro n;
      [exact (He a n c d r)|exact (Ho a n c d r)].
  - apply (parity (fun c=>P (denote s [a;b;c;d] r))); intro n;
      [exact (He a b n d r)|exact (Ho a b n d r)].
  - apply (parity (fun d=>P (denote s [a;b;c;d] r))); intro n;
      [exact (He a b c n r)|exact (Ho a b c n r)].
Qed.
Lemma zero_cover P s i : i<4 -> holds P (branch i 0 0 s) ->
  holds P (branch i 1 1 s) -> holds P s.
Proof.
  intros Hi Hz Hs; unfold holds in *; unfold branch in Hz,Hs.
  setoid_rewrite substitute_sound in Hz; setoid_rewrite substitute_sound in Hs.
  destruct i as [|[|[|[|i]]]]; try lia; intros a b c d r.
  - apply (zero_positive (fun a=>P (denote s [a;b;c;d] r)));
      [exact (Hz 0 b c d r)|intro n; exact (Hs n b c d r)].
  - apply (zero_positive (fun b=>P (denote s [a;b;c;d] r)));
      [exact (Hz a 0 c d r)|intro n; exact (Hs a n c d r)].
  - apply (zero_positive (fun c=>P (denote s [a;b;c;d] r)));
      [exact (Hz a b 0 d r)|intro n; exact (Hs a b n d r)].
  - apply (zero_positive (fun d=>P (denote s [a;b;c;d] r)));
      [exact (Hz a b c 0 r)|intro n; exact (Hs a b c n r)].
Qed.

Inductive tree :=
| Leaf (steps which:nat) (args:list ne)
| Parity (variable:nat) (even odd:tree)
| Zero (variable:nat) (zero positive:tree).
Fixpoint tree_check shapes t s := match t with
  | Leaf n which args=>leaf_check shapes n which args s
  | Parity i a b=>(i<?4)&&tree_check shapes a (branch i 2 0 s)&&tree_check shapes b (branch i 2 1 s)
  | Zero i a b=>(i<?4)&&tree_check shapes a (branch i 0 0 s)&&tree_check shapes b (branch i 1 1 s) end.
Lemma tree_check_sound shapes t s : tree_check shapes t s=true -> holds (returns shapes) s.
Proof.
  revert s; induction t; intros s H.
  - intros a b c d r; apply leaf_sound with (n:=steps) (which:=which) (args:=args); exact H.
  - cbn [tree_check] in H; repeat rewrite andb_true_iff in H.
    destruct H as [[Hi Ha] Hb]; apply Nat.ltb_lt in Hi.
    apply parity_cover with (i:=variable); [exact Hi|apply IHt1; exact Ha|apply IHt2; exact Hb].
  - cbn [tree_check] in H; repeat rewrite andb_true_iff in H.
    destruct H as [[Hi Ha] Hb]; apply Nat.ltb_lt in Hi.
    apply zero_cover with (i:=variable); [exact Hi|apply IHt1; exact Ha|apply IHt2; exact Hb].
Qed.
Definition affine_expr a b c d e := quote (Aff a b c d e).
Definition shape_S22 : cs := (Empty,word [
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 24 1 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 22 0 4 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 10 0 2 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 6 0 0 1 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Tail]).

Definition shape_H1 : cs := (Empty,word [
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 38 6 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 26 0 2 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 13 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 15 2 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 7 1 0 0 0) u;
    Rep (Aff 1 0 0 0 0) six;
    Rep (Aff 9 2 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 2 0 0 0 0) [S1;S0];
    Tail]).

Definition prefix_S22 (x0 x1 x2:nat) (r:list Sym) :=
  (cfg D ([]) S0 ([S1;S1;S1;S1;S0]++copies (24+x0) [S1;S1;S1;S0]++[S0]++copies (22+4*x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (10+2*x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (6+x2) [S1;S1;S1;S0]++[S0;S0]++r)).

Definition prefix_H1 (x0 x1:nat) (r:list Sym) :=
  (cfg D ([]) S0 ([S1;S1;S1;S1;S0]++copies (38+6*x0) [S1;S1;S1;S0]++[S0]++copies (26+2*x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (13+x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (15+2*x0) [S1;S1;S1;S0]++[S0]++copies (7+x0) [S1;S1;S1;S0]++[S1;S1;S1;S1;S1;S1;S0]++copies (9+2*x0) [S1;S1;S1;S0]++[S0;S0]++copies (2) [S1;S0]++r)).

Definition shape_H0 : cs := (Empty,word [
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 28 6 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 26 0 0 2 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 13 0 0 1 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 11 2 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 6 1 0 0 0) u;
    Rep (Aff 1 0 0 0 0) six;
    Rep (Aff 4 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0;S1;S0;S1;S0];
    Tail]).
Definition shape_QShield : cs := (Empty,word [
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 38 6 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 30 0 6 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 15 0 3 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 14 2 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 8 1 0 0 0) u;
    Rep (Aff 1 0 0 0 0) six;
    Rep (Aff 9 0 2 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0;S1;S0;S1];
    Rep (Aff 6 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) six;
    Rep (Aff 4 0 0 1 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0;S1;S0;S1;S0];
    Tail]).
Definition shape_QH1 : cs := (Empty,word [
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 38 6 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 40 0 6 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 20 0 3 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 14 2 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 8 1 0 0 0) u;
    Rep (Aff 1 0 0 0 0) six;
    Rep (Aff 13 0 2 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0;S1;S0;S1];
    Rep (Aff 7 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) six;
    Rep (Aff 9 0 2 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0;S1;S0;S1;S0];
    Tail]).
Definition mixed_target_shapes := [shape_S22;shape_H1;shape_H0;shape_QShield;shape_QH1].
Definition tree_S22 : tree :=
  (Parity 0
  (Leaf 3 2 [affine_expr 0 0 1 0 0; affine_expr 0 0 0 1 0; affine_expr 0 1 0 0 0])
  (Parity 0
    (Leaf 6 1 [affine_expr 0 1 0 0 0; affine_expr 0 0 3 0 0])
    (Parity 1
      (Leaf 7 0 [affine_expr 28 8 0 0 0; affine_expr 1 0 3 0 0; affine_expr 11 2 0 0 0])
      (Parity 0
        (Leaf 12 0 [affine_expr 41 6 18 0 0; affine_expr 8 4 0 0 0; affine_expr 10 0 6 0 0])
        (Leaf 16 0 [affine_expr 70 10 22 0 0; affine_expr 10 4 0 0 0; affine_expr 10 0 6 0 0]))))).
Lemma checked_S22 : tree_check mixed_target_shapes tree_S22 shape_S22=true.
Proof. vm_compute; reflexivity. Qed.
Definition tree_H1 : tree :=
  (Parity 1
  (Parity 0
    (Parity 1
      (Leaf 11 1 [affine_expr 6 1 3 0 0; affine_expr 20 9 2 0 0])
      (Parity 0
        (Parity 1
          (Leaf 20 0 [affine_expr 141 64 42 0 0; affine_expr 22 4 12 0 0; affine_expr 28 18 4 0 0])
          (Leaf 17 0 [affine_expr 131 60 30 0 0; affine_expr 28 4 12 0 0; affine_expr 30 18 4 0 0]))
        (Leaf 12 0 [affine_expr 92 16 24 0 0; affine_expr 16 9 1 0 0; affine_expr 27 4 6 0 0])))
    (Leaf 4 0 [affine_expr 27 4 6 0 0; affine_expr 6 3 0 0 0; affine_expr 8 0 2 0 0]))
  (Leaf 3 4 [affine_expr 0 0 1 0 0; affine_expr 0 1 0 0 0])).
Lemma checked_H1 : tree_check mixed_target_shapes tree_H1 shape_H1=true.
Proof. vm_compute; reflexivity. Qed.
Definition tree_H0 : tree :=
  (Parity 2
  (Parity 0
    (Leaf 4 0 [affine_expr 21 4 0 6 0; affine_expr 2 3 0 0 0; affine_expr 8 0 0 2 0])
    (Parity 2
      (Parity 0
        (Parity 2
          (Leaf 20 0 [affine_expr 119 64 0 42 0; affine_expr 18 4 0 12 0; affine_expr 24 18 0 4 0])
          (Leaf 17 0 [affine_expr 113 60 0 30 0; affine_expr 24 4 0 12 0; affine_expr 26 18 0 4 0]))
        (Leaf 12 0 [affine_expr 76 16 0 24 0; affine_expr 14 9 0 1 0; affine_expr 23 4 0 6 0]))
      (Leaf 11 1 [affine_expr 7 1 0 3 0; affine_expr 18 9 0 2 0])))
  (Leaf 3 3 [affine_expr 0 0 0 1 0; affine_expr 0 1 0 0 0; affine_expr 0 0 1 0 0])).
Lemma checked_H0 : tree_check mixed_target_shapes tree_H0 shape_H0=true.
Proof. vm_compute; reflexivity. Qed.
Definition prefix_H0 (x0 x1 x2:nat) (r:list Sym) :=
  (cfg D ([]) S0 ([S1;S1;S1;S1;S0]++copies (28+6*x0) [S1;S1;S1;S0]++[S0]++copies (26+2*x2) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (13+x2) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (11+2*x0) [S1;S1;S1;S0]++[S0]++copies (6+x0) [S1;S1;S1;S0]++[S1;S1;S1;S1;S1;S1;S0]++copies (4+x1) [S1;S1;S1;S0]++[S0;S0;S1;S0;S1;S0]++r)).
Definition prefix_QShield (x0 x1 x2:nat) (r:list Sym) :=
  (cfg D ([]) S0 ([S1;S1;S1;S1;S0]++copies (38+6*x0) [S1;S1;S1;S0]++[S0]++copies (30+6*x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (15+3*x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (14+2*x0) [S1;S1;S1;S0]++[S0]++copies (8+x0) [S1;S1;S1;S0]++[S1;S1;S1;S1;S1;S1;S0]++copies (9+2*x1) [S1;S1;S1;S0]++[S0;S0;S1;S0;S1]++copies (6+x1) [S1;S1;S1;S0]++[S1;S1;S1;S1;S1;S1;S0]++copies (4+x2) [S1;S1;S1;S0]++[S0;S0;S1;S0;S1;S0]++r)).
Definition prefix_QH1 (x0 x1:nat) (r:list Sym) :=
  (cfg D ([]) S0 ([S1;S1;S1;S1;S0]++copies (38+6*x0) [S1;S1;S1;S0]++[S0]++copies (40+6*x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (20+3*x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (14+2*x0) [S1;S1;S1;S0]++[S0]++copies (8+x0) [S1;S1;S1;S0]++[S1;S1;S1;S1;S1;S1;S0]++copies (13+2*x1) [S1;S1;S1;S0]++[S0;S0;S1;S0;S1]++copies (7+x1) [S1;S1;S1;S0]++[S1;S1;S1;S1;S1;S1;S0]++copies (9+2*x1) [S1;S1;S1;S0]++[S0;S0;S1;S0;S1;S0]++r)).
Definition mixed_prefix_target c :=
  (exists a0 a1 a2 r, c=prefix_S22 a0 a1 a2 r) \/
  (exists a0 a1 r, c=prefix_H1 a0 a1 r) \/
  (exists a0 a1 a2 r, c=prefix_H0 a0 a1 a2 r) \/
  (exists a0 a1 a2 r, c=prefix_QShield a0 a1 a2 r) \/
  (exists a0 a1 r, c=prefix_QH1 a0 a1 r).
Definition mixed_return c := exists d, Progress c d /\ mixed_prefix_target d.
Lemma mixed_shapes_sound c : target_family mixed_target_shapes c -> mixed_prefix_target c.
Proof.
  intros [s [Hin [env [r ->]]]].
  cbn [mixed_target_shapes In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - unfold mixed_prefix_target; left.
    exists (nth 0 env 0),(nth 1 env 0),(nth 2 env 0),r; reflexivity.
  - unfold mixed_prefix_target; right; left.
    exists (nth 0 env 0),(nth 1 env 0),r; reflexivity.
  - unfold mixed_prefix_target; right; right; left.
    exists (nth 0 env 0),(nth 1 env 0),(nth 2 env 0),r; reflexivity.
  - unfold mixed_prefix_target; right; right; right; left.
    exists (nth 0 env 0),(nth 1 env 0),(nth 2 env 0),r; reflexivity.
  - unfold mixed_prefix_target; right; right; right; right; idtac.
    exists (nth 0 env 0),(nth 1 env 0),r; reflexivity.
Qed.
Lemma S22_returns (x0 x1 x2:nat) (r:list Sym) :
  mixed_return (prefix_S22 x0 x1 x2 r).
Proof.
  destruct (tree_check_sound mixed_target_shapes tree_S22 shape_S22 checked_S22
    x0 x1 x2 0 r) as [d [Hrun Htarget]].
  exists d; split; [exact Hrun|apply mixed_shapes_sound; exact Htarget].
Qed.
Lemma H1_returns (x0 x1:nat) (r:list Sym) :
  mixed_return (prefix_H1 x0 x1 r).
Proof.
  destruct (tree_check_sound mixed_target_shapes tree_H1 shape_H1 checked_H1
    x0 x1 0 0 r) as [d [Hrun Htarget]].
  exists d; split; [exact Hrun|apply mixed_shapes_sound; exact Htarget].
Qed.
Lemma H0_returns (x0 x1 x2:nat) (r:list Sym) :
  mixed_return (prefix_H0 x0 x1 x2 r).
Proof.
  destruct (tree_check_sound mixed_target_shapes tree_H0 shape_H0 checked_H0
    x0 x1 x2 0 r) as [d [Hrun Htarget]].
  exists d; split; [exact Hrun|apply mixed_shapes_sound; exact Htarget].
Qed.
Definition shape_K5 : cs := (Empty,word [
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 24 1 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 28 0 4 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 13 0 2 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 20 0 0 6 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 10 0 0 3 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 8 0 0 0 2) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 5 0 0 0 1) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Tail]).
Definition shape_O5_1 : cs := (Empty,word [
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 24 1 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 30 0 2 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 12 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 11 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 13 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 20 0 0 6 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 10 0 0 3 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Tail]).
Definition shape_O5_2 : cs := (Empty,word [
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 24 1 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 30 0 2 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 12 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 11 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 13 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 20 0 0 6 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 11 0 0 3 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Tail]).
Definition five_target_shapes := [shape_S22;shape_H1].
Definition tree_K5 : tree :=
  (Parity 0
  (Parity 0
    (Leaf 4 0 [affine_expr 32 0 6 6 0; affine_expr 1 1 0 0 0; affine_expr 9 0 2 0 0])
    (Parity 1
      (Parity 2
        (Leaf 9 0 [affine_expr 33 6 6 0 0; affine_expr 9 0 3 3 0; affine_expr 8 2 0 0 0])
        (Parity 0
          (Parity 1
            (Leaf 16 1 [affine_expr 8 3 3 0 0; affine_expr 38 2 18 9 0])
            (Parity 2
              (Parity 0
                (Parity 1
                  (Leaf 25 0 [affine_expr 229 42 138 54 0; affine_expr 26 12 12 0 0; affine_expr 54 4 36 18 0])
                  (Leaf 22 0 [affine_expr 263 30 126 54 0; affine_expr 32 12 12 0 0; affine_expr 72 4 36 18 0]))
                (Parity 1
                  (Leaf 22 0 [affine_expr 215 30 126 54 0; affine_expr 32 12 12 0 0; affine_expr 56 4 36 18 0])
                  (Leaf 25 0 [affine_expr 319 42 138 54 0; affine_expr 38 12 12 0 0; affine_expr 74 4 36 18 0])))
              (Leaf 17 0 [affine_expr 100 24 24 0 0; affine_expr 29 1 9 9 0; affine_expr 29 6 6 0 0])))
          (Parity 1
            (Parity 2
              (Parity 0
                (Parity 1
                  (Leaf 25 0 [affine_expr 205 42 138 54 0; affine_expr 26 12 12 0 0; affine_expr 46 4 36 18 0])
                  (Leaf 22 0 [affine_expr 239 30 126 54 0; affine_expr 32 12 12 0 0; affine_expr 64 4 36 18 0]))
                (Parity 1
                  (Leaf 22 0 [affine_expr 191 30 126 54 0; affine_expr 32 12 12 0 0; affine_expr 48 4 36 18 0])
                  (Leaf 25 0 [affine_expr 295 42 138 54 0; affine_expr 38 12 12 0 0; affine_expr 66 4 36 18 0])))
              (Leaf 17 0 [affine_expr 100 24 24 0 0; affine_expr 25 1 9 9 0; affine_expr 29 6 6 0 0]))
            (Leaf 16 1 [affine_expr 11 3 3 0 0; affine_expr 48 2 18 9 0]))))
      (Parity 2
        (Parity 0
          (Parity 1
            (Parity 2
              (Leaf 20 0 [affine_expr 108 24 24 24 0; affine_expr 20 1 9 9 0; affine_expr 31 6 6 6 0])
              (Leaf 19 1 [affine_expr 12 3 3 3 0; affine_expr 47 2 18 18 0]))
            (Parity 2
              (Leaf 19 1 [affine_expr 12 3 3 3 0; affine_expr 47 2 18 18 0])
              (Leaf 20 0 [affine_expr 132 24 24 24 0; affine_expr 29 1 9 9 0; affine_expr 37 6 6 6 0])))
          (Parity 1
            (Parity 2
              (Leaf 19 1 [affine_expr 12 3 3 3 0; affine_expr 39 2 18 18 0])
              (Leaf 20 0 [affine_expr 132 24 24 24 0; affine_expr 25 1 9 9 0; affine_expr 37 6 6 6 0]))
            (Parity 2
              (Leaf 20 0 [affine_expr 132 24 24 24 0; affine_expr 25 1 9 9 0; affine_expr 37 6 6 6 0])
              (Leaf 19 1 [affine_expr 15 3 3 3 0; affine_expr 57 2 18 18 0]))))
        (Leaf 13 0 [affine_expr 53 6 6 6 2; affine_expr 12 0 3 3 0; affine_expr 8 2 0 0 0]))))
  (Parity 0
    (Leaf 7 1 [affine_expr 0 1 0 0 0; affine_expr 14 0 3 3 0])
    (Parity 1
      (Parity 2
        (Leaf 8 0 [affine_expr 28 8 0 0 0; affine_expr 8 0 3 3 0; affine_expr 11 2 0 0 0])
        (Parity 0
          (Leaf 13 0 [affine_expr 83 6 18 18 0; affine_expr 8 4 0 0 0; affine_expr 24 0 6 6 0])
          (Leaf 16 0 [affine_expr 99 10 18 18 0; affine_expr 10 4 0 0 0; affine_expr 24 0 6 6 0])))
      (Parity 2
        (Parity 0
          (Leaf 13 0 [affine_expr 83 6 18 18 0; affine_expr 8 4 0 0 0; affine_expr 24 0 6 6 0])
          (Leaf 16 0 [affine_expr 99 10 18 18 0; affine_expr 10 4 0 0 0; affine_expr 24 0 6 6 0]))
        (Leaf 8 0 [affine_expr 28 8 0 0 0; affine_expr 11 0 3 3 0; affine_expr 11 2 0 0 0]))))).
Lemma checked_K5 : tree_check five_target_shapes tree_K5 shape_K5=true.
Proof. vm_compute; reflexivity. Qed.
Definition tree_O5_1 : tree :=
  (Parity 0
  (Parity 1
    (Leaf 3 1 [affine_expr 0 0 1 0 0; affine_expr 0 1 0 0 0])
    (Parity 0
      (Leaf 4 0 [affine_expr 28 0 8 0 0; affine_expr 1 1 0 0 0; affine_expr 11 0 2 0 0])
      (Parity 1
        (Leaf 9 0 [affine_expr 35 6 6 0 0; affine_expr 8 0 4 0 0; affine_expr 8 2 0 0 0])
        (Leaf 12 0 [affine_expr 51 6 10 0 0; affine_expr 10 0 4 0 0; affine_expr 8 2 0 0 0]))))
  (Parity 1
    (Parity 0
      (Leaf 6 1 [affine_expr 0 1 0 0 0; affine_expr 5 0 3 0 0])
      (Parity 1
        (Parity 0
          (Leaf 12 0 [affine_expr 47 6 18 0 0; affine_expr 8 4 0 0 0; affine_expr 12 0 6 0 0])
          (Leaf 16 0 [affine_expr 78 10 22 0 0; affine_expr 10 4 0 0 0; affine_expr 12 0 6 0 0]))
        (Leaf 7 0 [affine_expr 28 8 0 0 0; affine_expr 5 0 3 0 0; affine_expr 11 2 0 0 0])))
    (Parity 0
      (Leaf 7 1 [affine_expr 0 1 0 0 0; affine_expr 12 0 4 0 0])
      (Leaf 8 0 [affine_expr 28 8 0 0 0; affine_expr 7 0 2 0 0; affine_expr 11 2 0 0 0])))).
Lemma checked_O5_1 : tree_check five_target_shapes tree_O5_1 shape_O5_1=true.
Proof. vm_compute; reflexivity. Qed.
Definition tree_O5_2 : tree :=
  (Parity 0
  (Parity 1
    (Leaf 3 1 [affine_expr 0 0 1 0 0; affine_expr 0 1 0 0 0])
    (Parity 0
      (Leaf 4 0 [affine_expr 28 0 8 0 0; affine_expr 1 1 0 0 0; affine_expr 11 0 2 0 0])
      (Parity 1
        (Leaf 9 0 [affine_expr 35 6 6 0 0; affine_expr 8 0 4 0 0; affine_expr 8 2 0 0 0])
        (Leaf 12 0 [affine_expr 51 6 10 0 0; affine_expr 10 0 4 0 0; affine_expr 8 2 0 0 0]))))
  (Parity 1
    (Parity 0
      (Leaf 6 1 [affine_expr 0 1 0 0 0; affine_expr 5 0 3 0 0])
      (Parity 1
        (Parity 0
          (Leaf 12 0 [affine_expr 47 6 18 0 0; affine_expr 8 4 0 0 0; affine_expr 12 0 6 0 0])
          (Leaf 16 0 [affine_expr 78 10 22 0 0; affine_expr 10 4 0 0 0; affine_expr 12 0 6 0 0]))
        (Leaf 7 0 [affine_expr 28 8 0 0 0; affine_expr 5 0 3 0 0; affine_expr 11 2 0 0 0])))
    (Parity 0
      (Leaf 7 1 [affine_expr 0 1 0 0 0; affine_expr 12 0 4 0 0])
      (Leaf 8 0 [affine_expr 28 8 0 0 0; affine_expr 7 0 2 0 0; affine_expr 11 2 0 0 0])))).
Lemma checked_O5_2 : tree_check five_target_shapes tree_O5_2 shape_O5_2=true.
Proof. vm_compute; reflexivity. Qed.

Definition prefix_K5 (x0 x1 x2 x3:nat) (r:list Sym) :=
  (cfg D ([]) S0 ([S1;S1;S1;S1;S0]++copies (24+x0) [S1;S1;S1;S0]++[S0]++copies (28+4*x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (13+2*x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (20+6*x2) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (10+3*x2) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (8+2*x3) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (5+x3) [S1;S1;S1;S0]++[S0;S0]++r)).
Definition prefix_O5_1 (x0 x1 x2:nat) (r:list Sym) :=
  (cfg D ([]) S0 ([S1;S1;S1;S1;S0]++copies (24+x0) [S1;S1;S1;S0]++[S0]++copies (30+2*x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (12+x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (11+x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (13+x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (20+6*x2) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (10+3*x2) [S1;S1;S1;S0]++[S0;S0]++r)).
Definition prefix_O5_2 (x0 x1 x2:nat) (r:list Sym) :=
  (cfg D ([]) S0 ([S1;S1;S1;S1;S0]++copies (24+x0) [S1;S1;S1;S0]++[S0]++copies (30+2*x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (12+x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (11+x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (13+x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (20+6*x2) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (11+3*x2) [S1;S1;S1;S0]++[S0;S0]++r)).
Definition five_prefix_target c :=
  (exists a0 a1 a2 r, c=prefix_S22 a0 a1 a2 r) \/
  (exists a0 a1 r, c=prefix_H1 a0 a1 r).
Definition five_return c := exists d, Progress c d /\ five_prefix_target d.
Lemma five_prefix_return_change a b : a=b -> five_return b -> five_return a.
Proof. intros -> H; exact H. Qed.
Lemma five_shapes_sound c : target_family five_target_shapes c -> five_prefix_target c.
Proof.
  intros [s [Hin [env [r ->]]]].
  cbn [five_target_shapes In] in Hin.
  destruct Hin as [<-|[<-|[]]].
  - unfold five_prefix_target; left.
    exists (nth 0 env 0),(nth 1 env 0),(nth 2 env 0),r; reflexivity.
  - unfold five_prefix_target; right; idtac.
    exists (nth 0 env 0),(nth 1 env 0),r; reflexivity.
Qed.
Lemma K5_returns (x0 x1 x2 x3:nat) (r:list Sym) :
  five_return (prefix_K5 x0 x1 x2 x3 r).
Proof.
  destruct (tree_check_sound five_target_shapes tree_K5 shape_K5 checked_K5
    x0 x1 x2 x3 r) as [d [Hrun Htarget]].
  exists d; split; [exact Hrun|apply five_shapes_sound; exact Htarget].
Qed.
Lemma O5_1_returns (x0 x1 x2:nat) (r:list Sym) :
  five_return (prefix_O5_1 x0 x1 x2 r).
Proof.
  destruct (tree_check_sound five_target_shapes tree_O5_1 shape_O5_1 checked_O5_1
    x0 x1 x2 0 r) as [d [Hrun Htarget]].
  exists d; split; [exact Hrun|apply five_shapes_sound; exact Htarget].
Qed.
Lemma O5_2_returns (x0 x1 x2:nat) (r:list Sym) :
  five_return (prefix_O5_2 x0 x1 x2 r).
Proof.
  destruct (tree_check_sound five_target_shapes tree_O5_2 shape_O5_2 checked_O5_2
    x0 x1 x2 0 r) as [d [Hrun Htarget]].
  exists d; split; [exact Hrun|apply five_shapes_sound; exact Htarget].
Qed.
Definition shape_KEmpty : cs := (Empty,word [
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 82 20 6 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 64 4 12 4 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 31 2 6 2 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 20 6 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 10 3 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 9 0 2 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 5 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 4 1 0 0 0) u;
    Rep (Aff 1 0 0 0 0) six;
    Rep (Aff 6 2 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0;S1;S0;S1];
    Tail]).
Definition shape_BOddNonempty : cs := (Empty,word [
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 80 18 6 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 28 0 0 4 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 13 0 0 2 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 20 6 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 11 3 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 9 0 2 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 6 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) six;
    Rep (Aff 3 2 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0;S1;S0;S1;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 9 2 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Tail]).
Definition shape_BOddEmpty : cs := (Empty,word [
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 80 18 6 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 72 4 12 4 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 35 2 6 2 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 20 6 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 11 3 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 9 0 2 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Rep (Aff 6 0 1 0 0) u;
    Rep (Aff 1 0 0 0 0) six;
    Rep (Aff 4 2 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0;S0;S1;S0;S1;S0];
    Rep (Aff 1 0 0 0 0) [S1;S1;S1;S1;S0];
    Rep (Aff 8 2 0 0 0) u;
    Rep (Aff 1 0 0 0 0) [S0];
    Tail]).
Definition short_target_shapes := [shape_S22;shape_H1].
Definition tree_KEmpty : tree :=
  (Parity 1
  (Parity 0
    (Parity 2
      (Parity 2
        (Leaf 20 0 [affine_expr 324 144 72 24 0; affine_expr 45 14 15 9 0; affine_expr 85 36 18 6 0])
        (Leaf 19 1 [affine_expr 39 18 9 3 0; affine_expr 97 28 30 18 0]))
      (Leaf 9 0 [affine_expr 147 66 36 6 0; affine_expr 24 6 9 3 0; affine_expr 36 20 6 0 0]))
    (Parity 2
      (Parity 0
        (Parity 2
          (Leaf 16 1 [affine_expr 44 33 9 3 0; affine_expr 102 56 30 18 0])
          (Parity 0
            (Parity 1
              (Parity 2
                (Leaf 25 0 [affine_expr 601 666 270 138 0; affine_expr 98 132 36 12 0; affine_expr 118 112 60 36 0])
                (Leaf 22 0 [affine_expr 563 534 234 126 0; affine_expr 104 132 36 12 0; affine_expr 136 112 60 36 0]))
              (Parity 2
                (Leaf 22 0 [affine_expr 617 534 234 126 0; affine_expr 116 132 36 12 0; affine_expr 148 112 60 36 0])
                (Leaf 25 0 [affine_expr 805 666 270 138 0; affine_expr 122 132 36 12 0; affine_expr 166 112 60 36 0])))
            (Parity 1
              (Parity 2
                (Leaf 22 0 [affine_expr 767 534 234 126 0; affine_expr 164 132 36 12 0; affine_expr 174 112 60 36 0])
                (Leaf 25 0 [affine_expr 1003 666 270 138 0; affine_expr 170 132 36 12 0; affine_expr 192 112 60 36 0]))
              (Parity 2
                (Leaf 25 0 [affine_expr 1069 666 270 138 0; affine_expr 182 132 36 12 0; affine_expr 204 112 60 36 0])
                (Leaf 22 0 [affine_expr 947 534 234 126 0; affine_expr 188 132 36 12 0; affine_expr 222 112 60 36 0])))))
        (Parity 2
          (Leaf 17 0 [affine_expr 508 264 72 24 0; affine_expr 66 28 15 9 0; affine_expr 131 66 18 6 0])
          (Leaf 16 1 [affine_expr 62 33 9 3 0; affine_expr 139 56 30 18 0])))
      (Leaf 14 0 [affine_expr 202 72 42 6 0; affine_expr 27 6 9 3 0; affine_expr 46 20 6 0 0])))
  (Leaf 4 0 [affine_expr 104 12 36 6 0; affine_expr 17 5 3 0 0; affine_expr 33 2 12 2 0])).
Lemma checked_KEmpty : tree_check short_target_shapes tree_KEmpty shape_KEmpty=true.
Proof. vm_compute; reflexivity. Qed.
Definition tree_BOddNonempty : tree :=
  (Parity 0
  (Parity 1
    (Leaf 4 0 [affine_expr 32 12 0 6 0; affine_expr 15 9 3 0 0; affine_expr 9 0 0 2 0])
    (Parity 2
      (Leaf 9 0 [affine_expr 123 54 18 6 0; affine_expr 9 3 0 3 0; affine_expr 38 18 6 0 0])
      (Parity 1
        (Parity 2
          (Leaf 17 0 [affine_expr 110 36 12 36 0; affine_expr 37 15 11 3 0; affine_expr 27 6 0 12 0])
          (Parity 0
            (Leaf 22 0 [affine_expr 291 198 66 36 0; affine_expr 33 18 3 9 0; affine_expr 82 60 22 6 0])
            (Leaf 26 0 [affine_expr 429 216 72 40 0; affine_expr 42 18 3 9 0; affine_expr 112 60 22 6 0])))
        (Parity 2
          (Parity 0
            (Zero 2
              (Leaf 26 0 [affine_expr 337 216 72 0 0; affine_expr 30 18 3 0 0; affine_expr 90 60 22 0 0])
              (Leaf 26 0 [affine_expr 377 216 72 40 0; affine_expr 39 18 3 9 0; affine_expr 96 60 22 6 0]))
            (Leaf 22 0 [affine_expr 405 198 66 36 0; affine_expr 39 18 3 9 0; affine_expr 120 60 22 6 0]))
          (Leaf 17 0 [affine_expr 134 36 12 36 0; affine_expr 44 15 11 3 0; affine_expr 33 6 0 12 0])))))
  (Parity 1
    (Parity 2
      (Parity 0
        (Parity 1
          (Parity 2
            (Leaf 16 1 [affine_expr 35 27 9 3 0; affine_expr 56 36 6 18 0])
            (Parity 0
              (Parity 1
                (Parity 2
                  (Leaf 22 0 [affine_expr 335 378 90 126 0; affine_expr 80 108 36 12 0; affine_expr 72 72 12 36 0])
                  (Leaf 25 0 [affine_expr 487 486 126 138 0; affine_expr 86 108 36 12 0; affine_expr 90 72 12 36 0]))
                (Parity 2
                  (Leaf 25 0 [affine_expr 481 486 126 138 0; affine_expr 98 108 36 12 0; affine_expr 78 72 12 36 0])
                  (Leaf 22 0 [affine_expr 443 378 90 126 0; affine_expr 104 108 36 12 0; affine_expr 96 72 12 36 0])))
              (Parity 1
                (Parity 2
                  (Leaf 25 0 [affine_expr 661 486 126 138 0; affine_expr 134 108 36 12 0; affine_expr 108 72 12 36 0])
                  (Leaf 22 0 [affine_expr 587 378 90 126 0; affine_expr 140 108 36 12 0; affine_expr 126 72 12 36 0]))
                (Parity 2
                  (Leaf 22 0 [affine_expr 569 378 90 126 0; affine_expr 152 108 36 12 0; affine_expr 114 72 12 36 0])
                  (Leaf 25 0 [affine_expr 793 486 126 138 0; affine_expr 158 108 36 12 0; affine_expr 132 72 12 36 0])))))
          (Parity 2
            (Parity 0
              (Parity 1
                (Parity 2
                  (Leaf 25 0 [affine_expr 415 486 126 138 0; affine_expr 86 108 36 12 0; affine_expr 66 72 12 36 0])
                  (Leaf 22 0 [affine_expr 389 378 90 126 0; affine_expr 92 108 36 12 0; affine_expr 84 72 12 36 0]))
                (Parity 2
                  (Leaf 22 0 [affine_expr 371 378 90 126 0; affine_expr 104 108 36 12 0; affine_expr 72 72 12 36 0])
                  (Leaf 25 0 [affine_expr 547 486 126 138 0; affine_expr 110 108 36 12 0; affine_expr 90 72 12 36 0])))
              (Parity 1
                (Parity 2
                  (Leaf 22 0 [affine_expr 515 378 90 126 0; affine_expr 140 108 36 12 0; affine_expr 102 72 12 36 0])
                  (Leaf 25 0 [affine_expr 727 486 126 138 0; affine_expr 146 108 36 12 0; affine_expr 120 72 12 36 0]))
                (Parity 2
                  (Leaf 25 0 [affine_expr 721 486 126 138 0; affine_expr 158 108 36 12 0; affine_expr 108 72 12 36 0])
                  (Leaf 22 0 [affine_expr 623 378 90 126 0; affine_expr 164 108 36 12 0; affine_expr 126 72 12 36 0]))))
            (Leaf 16 1 [affine_expr 41 27 9 3 0; affine_expr 68 36 6 18 0])))
        (Parity 1
          (Parity 2
            (Leaf 17 0 [affine_expr 412 216 72 24 0; affine_expr 38 18 3 9 0; affine_expr 107 54 18 6 0])
            (Leaf 16 1 [affine_expr 50 27 9 3 0; affine_expr 83 36 6 18 0]))
          (Parity 2
            (Leaf 16 1 [affine_expr 53 27 9 3 0; affine_expr 77 36 6 18 0])
            (Leaf 17 0 [affine_expr 460 216 72 24 0; affine_expr 44 18 3 9 0; affine_expr 119 54 18 6 0]))))
      (Leaf 12 0 [affine_expr 155 60 18 6 0; affine_expr 12 3 0 3 0; affine_expr 44 18 6 0 0]))
    (Leaf 4 0 [affine_expr 38 12 0 6 0; affine_expr 21 9 3 0 0; affine_expr 9 0 0 2 0]))).
Lemma checked_BOddNonempty : tree_check short_target_shapes tree_BOddNonempty shape_BOddNonempty=true.
Proof. vm_compute; reflexivity. Qed.
Definition tree_BOddEmpty : tree :=
  (Parity 0
  (Parity 1
    (Leaf 4 0 [affine_expr 98 24 36 6 0; affine_expr 15 9 3 0 0; affine_expr 31 4 12 2 0])
    (Parity 2
      (Leaf 9 0 [affine_expr 165 60 36 6 0; affine_expr 30 6 9 3 0; affine_expr 38 18 6 0 0])
      (Parity 0
        (Parity 2
          (Parity 1
            (Leaf 22 0 [affine_expr 399 234 174 36 0; affine_expr 60 27 30 9 0; affine_expr 100 66 40 6 0])
            (Leaf 26 0 [affine_expr 537 256 192 40 0; affine_expr 75 27 30 9 0; affine_expr 120 66 40 6 0]))
          (Leaf 17 0 [affine_expr 254 108 60 36 0; affine_expr 49 33 10 3 0; affine_expr 75 24 18 12 0]))
        (Parity 2
          (Leaf 17 0 [affine_expr 290 108 60 36 0; affine_expr 64 33 10 3 0; affine_expr 81 24 18 12 0])
          (Parity 1
            (Leaf 26 0 [affine_expr 589 256 192 40 0; affine_expr 78 27 30 9 0; affine_expr 136 66 40 6 0])
            (Leaf 22 0 [affine_expr 621 234 174 36 0; affine_expr 93 27 30 9 0; affine_expr 156 66 40 6 0]))))))
  (Parity 1
    (Parity 2
      (Parity 2
        (Leaf 16 1 [affine_expr 44 15 9 3 0; affine_expr 110 27 30 18 0])
        (Parity 0
          (Parity 1
            (Parity 2
              (Leaf 25 0 [affine_expr 625 312 270 138 0; affine_expr 98 60 36 12 0; affine_expr 126 54 60 36 0])
              (Leaf 22 0 [affine_expr 587 252 234 126 0; affine_expr 104 60 36 12 0; affine_expr 144 54 60 36 0]))
            (Parity 2
              (Leaf 22 0 [affine_expr 641 252 234 126 0; affine_expr 116 60 36 12 0; affine_expr 156 54 60 36 0])
              (Leaf 25 0 [affine_expr 829 312 270 138 0; affine_expr 122 60 36 12 0; affine_expr 174 54 60 36 0])))
          (Leaf 17 0 [affine_expr 508 240 72 24 0; affine_expr 74 27 15 9 0; affine_expr 131 60 18 6 0])))
      (Leaf 12 0 [affine_expr 191 66 36 6 0; affine_expr 30 6 9 3 0; affine_expr 44 18 6 0 0]))
    (Leaf 4 0 [affine_expr 128 24 36 6 0; affine_expr 21 9 3 0 0; affine_expr 39 4 12 2 0]))).
Lemma checked_BOddEmpty : tree_check short_target_shapes tree_BOddEmpty shape_BOddEmpty=true.
Proof. vm_compute; reflexivity. Qed.
Definition prefix_KEmpty (x0 x1 x2:nat) (r:list Sym) :=
  (cfg D ([]) S0 ([S1;S1;S1;S1;S0]++copies (82+20*x0+6*x1) [S1;S1;S1;S0]++[S0]++copies (64+4*x0+12*x1+4*x2) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (31+2*x0+6*x1+2*x2) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (20+6*x0) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (10+3*x0) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (9+2*x1) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (5+x1) [S1;S1;S1;S0]++[S0]++copies (4+x0) [S1;S1;S1;S0]++[S1;S1;S1;S1;S1;S1;S0]++copies (6+2*x0) [S1;S1;S1;S0]++[S0;S0;S1;S0;S1]++r)).
Definition prefix_BOddNonempty (x0 x1 x2:nat) (r:list Sym) :=
  (cfg D ([]) S0 ([S1;S1;S1;S1;S0]++copies (80+18*x0+6*x1) [S1;S1;S1;S0]++[S0]++copies (28+4*x2) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (13+2*x2) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (20+6*x0) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (11+3*x0) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (9+2*x1) [S1;S1;S1;S0]++[S0]++copies (6+x1) [S1;S1;S1;S0]++[S1;S1;S1;S1;S1;S1;S0]++copies (3+2*x0) [S1;S1;S1;S0]++[S0;S0;S1;S0;S1;S0]++[S1;S1;S1;S1;S0]++copies (9+2*x0) [S1;S1;S1;S0]++[S0;S0]++r)).
Definition prefix_BOddEmpty (x0 x1 x2:nat) (r:list Sym) :=
  (cfg D ([]) S0 ([S1;S1;S1;S1;S0]++copies (80+18*x0+6*x1) [S1;S1;S1;S0]++[S0]++copies (72+4*x0+12*x1+4*x2) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (35+2*x0+6*x1+2*x2) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (20+6*x0) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (11+3*x0) [S1;S1;S1;S0]++[S0;S0]++[S1;S1;S1;S1;S0]++copies (9+2*x1) [S1;S1;S1;S0]++[S0]++copies (6+x1) [S1;S1;S1;S0]++[S1;S1;S1;S1;S1;S1;S0]++copies (4+2*x0) [S1;S1;S1;S0]++[S0;S0;S1;S0;S1;S0]++[S1;S1;S1;S1;S0]++copies (8+2*x0) [S1;S1;S1;S0]++[S0]++r)).
Definition short_prefix_target c :=
  (exists a0 a1 a2 r, c=prefix_S22 a0 a1 a2 r) \/
  (exists a0 a1 r, c=prefix_H1 a0 a1 r).
Definition short_return c := exists d, Progress c d /\ short_prefix_target d.
Lemma short_prefix_return_change a b : a=b -> short_return b -> short_return a.
Proof. intros -> H; exact H. Qed.
Lemma short_shapes_sound c : target_family short_target_shapes c -> short_prefix_target c.
Proof.
  intros [s [Hin [env [r ->]]]].
  cbn [short_target_shapes In] in Hin.
  destruct Hin as [<-|[<-|[]]].
  - unfold short_prefix_target; left.
    exists (nth 0 env 0),(nth 1 env 0),(nth 2 env 0),r; reflexivity.
  - unfold short_prefix_target; right; idtac.
    exists (nth 0 env 0),(nth 1 env 0),r; reflexivity.
Qed.
Lemma KEmpty_returns (x0 x1 x2:nat) (r:list Sym) :
  short_return (prefix_KEmpty x0 x1 x2 r).
Proof.
  destruct (tree_check_sound short_target_shapes tree_KEmpty shape_KEmpty checked_KEmpty
    x0 x1 x2 0 r) as [d [Hrun Htarget]].
  exists d; split; [exact Hrun|apply short_shapes_sound; exact Htarget].
Qed.
Lemma BOddNonempty_returns (x0 x1 x2:nat) (r:list Sym) :
  short_return (prefix_BOddNonempty x0 x1 x2 r).
Proof.
  destruct (tree_check_sound short_target_shapes tree_BOddNonempty shape_BOddNonempty checked_BOddNonempty
    x0 x1 x2 0 r) as [d [Hrun Htarget]].
  exists d; split; [exact Hrun|apply short_shapes_sound; exact Htarget].
Qed.
Lemma BOddEmpty_returns (x0 x1 x2:nat) (r:list Sym) :
  short_return (prefix_BOddEmpty x0 x1 x2 r).
Proof.
  destruct (tree_check_sound short_target_shapes tree_BOddEmpty shape_BOddEmpty checked_BOddEmpty
    x0 x1 x2 0 r) as [d [Hrun Htarget]].
  exists d; split; [exact Hrun|apply short_shapes_sound; exact Htarget].
Qed.
Inductive ReturnFamily : config -> Prop :=
| family_S a b d r : ReturnFamily (prefix_S22 a b d r)
| family_H0 d e f r : ReturnFamily (prefix_H0 d e f r)
| family_H1 d f r : ReturnFamily (prefix_H1 d f r)
| family_Q x y indices s v r :
    6<=x -> 13<=y -> 3<=s -> Forall (fun z => 5<=z) indices ->
    ReturnFamily (Qfront x y (exit_chain (x-1) indices s (v++[Three;Three]) r)).

Lemma strong_shield_form a b d r :
  prefix_S22 a b d r=shield (24+a) (22+4*b) (6+d) r.
Proof.
  unfold shield.
  assert (Hhalf : (22+4*b)/2-1=10+2*b).
  { replace (22+4*b) with ((11+2*b)*2) by lia.
    rewrite Nat.div_mul by lia; lia. }
  rewrite Hhalf; unfold prefix_S22; prefix_config_eq.
Qed.

Lemma strong_shield_family a b d r :
  24<=a -> 22<=b -> b mod 4=2 -> 6<=d -> ReturnFamily (shield a b d r).
Proof.
  intros Ha Hb Hmod Hd.
  pose proof (Nat.div_mod b 4 ltac:(lia)) as Hdivide.
  replace (shield a b d r) with
    (prefix_S22 (a-24) (b/4-5) (d-6) r).
  - constructor.
  - rewrite strong_shield_form; f_equal; lia.
Qed.

Lemma protected_chain_empty t s p q r :
  exit_chain t [] s ((repeat Three p++Six::repeat Three q)++[Three;Three]) r =
  copies (t+3) [S1;S1;S1;S0]++[S1;S1;S1;S1;S1;S1;S0]++
  copies (2*s+3) [S1;S1;S1;S0]++[S0;S0;S1;S0;S1]++
  copies (p+1) [S1;S1;S1;S0]++[S1;S1;S1;S1;S1;S1;S0]++
  copies (q+4) [S1;S1;S1;S0]++S0::r.
Proof.
  cbn [exit_chain]; unfold callback_payload,callback_middle,exit_core.
  repeat first [rewrite core_bits_app | rewrite core_bits_threes |
    progress cbn [core_bits block_bits app] | rewrite <- app_assoc].
  replace (t+3) with (S (t+2)) by lia.
  replace (p+1) with (S p) by lia.
  replace (2*s+3) with ((2*s+1)+2) by lia.
  rewrite (copies_add (2*s+1) 2 [S1;S1;S1;S0]).
  rewrite (copies_add q 4 [S1;S1;S1;S0]).
  cbn [copies app]; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma QShield_typed a b e r :
  prefix_QShield a b e r =
  Qfront (6+a) (13+3*b)
    (exit_chain (6+a-1) [] (3+b)
      ((repeat Three (5+b)++Six::repeat Three e)++[Three;Three])
      ([S0;S1;S0;S1;S0]++r)).
Proof.
  rewrite protected_chain_empty.
  unfold prefix_QShield,Qfront,qright.
  prefix_config_eq.
Qed.

Lemma QH1_typed a d r :
  prefix_QH1 a d r =
  Qfront (6+a) (18+3*d)
    (exit_chain (6+a-1) [] (5+d)
      ((repeat Three (6+d)++Six::repeat Three (5+2*d))++[Three;Three])
      ([S0;S1;S0;S1;S0]++r)).
Proof.
  rewrite protected_chain_empty.
  unfold prefix_QH1,Qfront,qright.
  replace (6*(6+a)+2) with (38+6*a) by lia.
  replace (2*(18+3*d)+4) with (40+6*d) by lia.
  replace (18+3*d+2) with (20+3*d) by lia.
  replace (2*(6+a)+2) with (14+2*a) by lia.
  replace (6+a-1+3) with (8+a) by lia.
  replace (2*(5+d)+3) with (13+2*d) by lia.
  replace (6+d+1) with (7+d) by lia.
  replace (5+2*d+4) with (9+2*d) by lia.
  prefix_config_eq.
Qed.

Lemma mixed_target_family c : mixed_prefix_target c -> ReturnFamily c.
Proof.
  intros [[a [b [d [r ->]]]] | [[d [f [r ->]]] |
    [[d [e [f [r ->]]]] | [[a [s [e [r ->]]]] | [a [d [r ->]]]]]]].
  - apply family_S.
  - apply family_H1.
  - apply family_H0.
  - rewrite QShield_typed; apply family_Q; try lia; constructor.
  - rewrite QH1_typed; apply family_Q; try lia; constructor.
Qed.

Lemma mixed_return_family c : mixed_return c ->
  exists d, Progress c d /\ ReturnFamily d.
Proof.
  intros [d [Hstep Htarget]]; exists d; split; [exact Hstep |].
  apply mixed_target_family; exact Htarget.
Qed.

Lemma return_family_live c : ReturnFamily c -> step c<>None.
Proof.
  intro H; destruct H;
    cbn [prefix_S22 prefix_H0 prefix_H1
      Qfront counter_pair step st scan]; discriminate.
Qed.

Lemma five_target_family c : five_prefix_target c -> ReturnFamily c.
Proof.
  intros [[a [b [d [r ->]]]] | [d [f [r ->]]]].
  - exact (family_S a b d r).
  - exact (family_H1 d f r).
Qed.

Lemma five_return_family c : five_return c ->
  exists d, Progress c d /\ ReturnFamily d.
Proof.
  intros [d [Hstep Htarget]]; exists d; split; [exact Hstep |].
  apply five_target_family; exact Htarget.
Qed.

Lemma K5_return_family a c x h r :
  24<=a -> 13<=c -> c mod 2=1 -> 3<=x -> 3<=h ->
  exists d, Progress (K5front a c x h r) d /\ ReturnFamily d.
Proof.
  intros Ha Hc Hodd Hx Hh.
  pose proof (Nat.div_mod c 2 ltac:(lia)) as Hdivide.
  apply five_return_family.
  eapply five_prefix_return_change.
  2: exact (K5_returns (a-24) (c/2-6) (x-3) (h-3) r).
  unfold K5front,prefix_K5; prefix_config_eq_fast.
Qed.

Lemma O5_return_family a k x offset r :
  24<=a -> 12<=k -> 3<=x -> (offset=1 \/ offset=2) ->
  exists d, Progress (O5front a k x offset r) d /\ ReturnFamily d.
Proof.
  intros Ha Hk Hx [Hoffset|Hoffset]; subst offset; apply five_return_family.
  - eapply five_prefix_return_change.
    2: exact (O5_1_returns (a-24) (k-12) (x-3) r).
    unfold O5front,prefix_O5_1; prefix_config_eq_fast.
  - eapply five_prefix_return_change.
    2: exact (O5_2_returns (a-24) (k-12) (x-3) r).
    unfold O5front,prefix_O5_2; prefix_config_eq_fast.
Qed.

Lemma short_target_family c : short_prefix_target c -> ReturnFamily c.
Proof.
  intros [[a [b [d [r ->]]]] | [d [f [r ->]]]].
  - exact (family_S a b d r).
  - exact (family_H1 d f r).
Qed.

Lemma short_return_family c : short_return c ->
  exists d, Progress c d /\ ReturnFamily d.
Proof.
  intros [d [Hstep Htarget]]; exists d; split; [exact Hstep |].
  apply short_target_family; exact Htarget.
Qed.

Lemma KEmpty_return_family x h s r :
  3<=x -> 3<=h -> 3<=s -> s mod 2=1 ->
  exists d, Progress (KEmptyFront (2*x+6*h+s+4) x h r) d /\ ReturnFamily d.
Proof.
  intros Hx Hh Hs Hodd.
  pose proof (Nat.div_mod s 2 ltac:(lia)) as Hdivide.
  apply short_return_family.
  eapply short_prefix_return_change.
  2: exact (KEmpty_returns (x-3) (h-3) (s/2-1) r).
  unfold KEmptyFront,prefix_KEmpty; prefix_config_eq_fast.
Qed.

Lemma BOddNonempty_return_family c x h r :
  13<=c -> c mod 2=1 -> 3<=x -> 3<=h ->
  exists d, Progress (BOddNonemptyFront c x h r) d /\ ReturnFamily d.
Proof.
  intros Hc Hodd Hx Hh.
  pose proof (Nat.div_mod c 2 ltac:(lia)) as Hdivide.
  apply short_return_family.
  eapply short_prefix_return_change.
  2: exact (BOddNonempty_returns (x-3) (h-3) (c/2-6) r).
  unfold BOddNonemptyFront,prefix_BOddNonempty; prefix_config_eq_fast.
Qed.

Lemma BOddEmpty_return_family x h s r :
  3<=x -> 3<=h -> 4<=s -> s mod 2=0 ->
  exists d, Progress (BOddEmptyFront (2*x+6*h+s+7) x h r) d /\ ReturnFamily d.
Proof.
  intros Hx Hh Hs Heven.
  pose proof (Nat.div_mod s 2 ltac:(lia)) as Hdivide.
  apply short_return_family.
  eapply short_prefix_return_change.
  2: exact (BOddEmpty_returns (x-3) (h-3) (s/2-2) r).
  unfold BOddEmptyFront,prefix_BOddEmpty; prefix_config_eq_fast.
Qed.

Lemma indices_positive indices :
  Forall (fun z => 5<=z) indices -> Forall (fun z => 1<=z) indices.
Proof. induction 1; constructor; auto; lia. Qed.

Lemma q_page_as_front x b indices s v r :
  q_page_output (2*x) b indices s v r =
  q_pages_front (q_page_a (2*x) b indices s) x b indices s v r.
Proof.
  unfold q_page_output,q_pages_front.
  replace (6*(2*x)+4) with (12*x+4) by lia.
  replace (3*(2*x)+1) with (6*x+1) by lia; reflexivity.
Qed.

Lemma q_page_size x b indices s : 3<=x -> 6<=b -> 3<=s ->
  62<=q_page_a (2*x) b indices s.
Proof. unfold q_page_a; lia. Qed.

Lemma q_pages_zero_family a x b indices s v r :
  62<=a -> 3<=x -> 6<=b -> Forall (fun z => 1<=z) indices -> a mod 4=0 ->
  exists d, Progress (q_pages_front a x b indices s v r) d /\ ReturnFamily d.
Proof.
  intros Ha Hx Hb Hindices Hmod.
  pose proof (Nat.div_mod a 4 ltac:(lia)) as Hdivide.
  set (k:=a/4-1).
  assert (Hk : 5<=k) by (unfold k; lia).
  assert (Hform : a=4*k+4) by (unfold k; lia).
  destruct (even_frontier_frame_shield k x b indices s v r Hk ltac:(lia) ltac:(lia) Hindices)
    as [clock [aa [rr [Hclock [Haa Hreturn]]]]].
  exists (shield aa (4*k+6) (6*x+2) rr); split.
  - unfold q_pages_front; rewrite Hform; exists clock; auto.
  - apply strong_shield_family; try lia.
    replace (4*k+6) with (2+(k+1)*4) by lia.
    rewrite Nat.mod_add by lia; reflexivity.
Qed.

Lemma q_pages_odd_family a x b indices s v r :
  62<=a -> 3<=x -> 6<=b -> Forall (fun z => 1<=z) indices -> a mod 2=1 ->
  exists d, Progress (q_pages_front a x b indices s v r) d /\ ReturnFamily d.
Proof.
  intros Ha Hx Hb Hindices Hmod.
  pose proof (Nat.div_mod a 2 ltac:(lia)) as Hdivide.
  set (k:=a/2-1).
  assert (Hk : 11<=k) by (unfold k; lia).
  assert (Hform : a=2*k+3) by (unfold k; lia).
  destruct (q_pages_odd k x b indices s v r Hk Hx Hb Hindices)
    as [aa [offset [tail [Haa [Hoffset Hreturn]]]]].
  destruct (O5_return_family aa (k+1) x offset tail Haa ltac:(lia) Hx Hoffset)
    as [d [Hnext Hd]].
  exists d; split; [|exact Hd].
  rewrite Hform; eapply progress_trans; eauto.
Qed.

Lemma q_pages_two_family x b indices s v r :
  3<=x -> 6<=b -> 3<=s -> Forall (fun z => 5<=z) indices ->
  q_page_a (2*x) b indices s mod 4=2 ->
  exists d, Progress (q_pages_front (q_page_a (2*x) b indices s) x b indices s v r) d /\
    ReturnFamily d.
Proof.
  intros Hx Hb Hs Hindices Hmod.
  set (a:=q_page_a (2*x) b indices s) in *.
  assert (Ha : 62<=a) by (unfold a; apply q_page_size; assumption).
  assert (Hfull : a=4*x+6*b+chain_growth indices+2*s+8) by (unfold a,q_page_a; lia).
  pose proof (Nat.div_mod a 4 ltac:(lia)) as Ha4.
  pose proof (Nat.div_mod a 2 ltac:(lia)) as Ha2.
  pose proof (Nat.mod_upper_bound a 2 ltac:(lia)) as Ham.
  set (k:=a/2-1).
  assert (Hform : a=2*k+2) by (unfold k; lia).
  assert (Hc : 13<=k+1) by lia.
  pose proof (Nat.div_mod (k+1) 2 ltac:(lia)) as Hc2.
  pose proof (Nat.mod_upper_bound (k+1) 2 ltac:(lia)) as Hcm.
  assert (Hodd : (k+1) mod 2=1) by lia.
  pose proof (Nat.div_mod b 2 ltac:(lia)) as Hb2.
  pose proof (Nat.mod_upper_bound b 2 ltac:(lia)) as Hbm.
  remember (b/2) as h.
  assert (Hcases : b=2*h \/ b=2*h+1) by lia.
  destruct Hcases as [Hbf|Hbf]; subst b; assert (Hh : 3<=h) by lia;
    destruct indices as [|z indices].
  - cbn [chain_growth] in Hfull.
    pose proof (Nat.div_mod s 2 ltac:(lia)) as Hs2.
    pose proof (Nat.mod_upper_bound s 2 ltac:(lia)) as Hsm.
    assert (Hsodd : s mod 2=1) by lia.
    assert (Hcounter : k+1=2*x+6*h+s+4) by lia.
    destruct (KEmpty_return_family x h s (frame_body s v r) Hx Hh Hs Hsodd)
      as [d [Hnext Hd]].
    exists d; split; [|exact Hd].
    rewrite Hform; eapply progress_trans.
    + apply q_pages_even_empty; lia.
    + rewrite Hcounter; exact Hnext.
  - pose proof (Forall_inv Hindices) as Hz.
    change (5<=z) in Hz.
    pose proof (indices_positive _ (Forall_inv_tail Hindices)) as Htail.
    destruct (q_pages_even_nonempty k x h z indices s v r Hx Hh ltac:(lia) Htail)
      as [aa [tail [Haa Hreturn]]].
    destruct (K5_return_family aa (k+1) x h tail Haa Hc Hodd Hx Hh)
      as [d [Hnext Hd]].
    exists d; split; [|exact Hd].
    rewrite Hform; eapply progress_trans; eauto.
  - cbn [chain_growth] in Hfull.
    pose proof (Nat.div_mod s 2 ltac:(lia)) as Hs2.
    pose proof (Nat.mod_upper_bound s 2 ltac:(lia)) as Hsm.
    assert (Hseven : s mod 2=0) by lia.
    assert (Hs4 : 4<=s) by lia.
    assert (Hcounter : k+1=2*x+6*h+s+7) by lia.
    destruct (BOddEmpty_return_family x h s (frame_body s v r) Hx Hh Hs4 Hseven)
      as [d [Hnext Hd]].
    exists d; split; [|exact Hd].
    rewrite Hform; eapply progress_trans.
    + apply q_pages_bodd_empty; lia.
    + rewrite Hcounter; exact Hnext.
  - destruct (BOddNonempty_return_family (k+1) x h (frame_pages z indices s v r)
      Hc Hodd Hx Hh) as [d [Hnext Hd]].
    exists d; split; [|exact Hd].
    rewrite Hform; eapply progress_trans.
    + apply q_pages_bodd_nonempty; lia.
    + exact Hnext.
Qed.

Lemma q_pages_family x b indices s v r :
  3<=x -> 6<=b -> 3<=s -> Forall (fun z => 5<=z) indices ->
  exists d, Progress (q_page_output (2*x) b indices s v r) d /\ ReturnFamily d.
Proof.
  intros Hx Hb Hs Hindices; rewrite q_page_as_front.
  pose proof (q_page_size x b indices s Hx Hb Hs) as Ha.
  pose proof (indices_positive _ Hindices) as Hpositive.
  set (a:=q_page_a (2*x) b indices s) in *.
  destruct (Nat.eq_dec (a mod 4) 0) as [Hz|Hz].
  - apply q_pages_zero_family; assumption.
  - destruct (Nat.eq_dec (a mod 4) 2) as [Ht|Ht].
    + apply q_pages_two_family; assumption.
    + apply q_pages_odd_family; try assumption.
      pose proof (Nat.div_mod a 4 ltac:(lia)) as H4.
      pose proof (Nat.mod_upper_bound a 4 ltac:(lia)) as H4m.
      pose proof (Nat.div_mod a 2 ltac:(lia)) as H2.
      pose proof (Nat.mod_upper_bound a 2 ltac:(lia)) as H2m; lia.
Qed.

Lemma Q_even_exit_family x b indices s v r :
  3<=x -> 6<=b -> 3<=s -> Forall (fun z => 5<=z) indices ->
  exists d, Progress (Qfront (2*x) (2*b+1)
    (exit_chain (2*x-1) indices s (v++[Three;Three]) r)) d /\ ReturnFamily d.
Proof.
  intros Hx Hb Hs Hindices.
  destruct (q_pages_family x b indices s v r Hx Hb Hs Hindices) as [d [Hnext Hd]].
  exists d; split; [|exact Hd].
  eapply progress_after; [apply Q_page_return; lia |exact Hnext].
Qed.

Lemma Q_odd_exit_family a b indices s v r : 3<=a -> 6<=b -> 3<=s ->
  exists d, Progress (Qfront (2*a+1) (2*b+1)
    (exit_chain (2*a) indices s (v++[Three;Three]) r)) d /\ ReturnFamily d.
Proof.
  intros Ha Hb Hs.
  destruct (Q_odd_chain_to_shield indices a b s (v++[Three;Three]) r ltac:(lia) ltac:(lia))
    as [aa [rr [Haa [Hd Hreturn]]]].
  exists (shield aa (12*a+10) (2*b+3) rr); split.
  - eexists; split; [|exact Hreturn]; unfold qodd_clock; lia.
  - apply strong_shield_family; try lia.
    replace (12*a+10) with (2+(3*a+2)*4) by lia.
    rewrite Nat.mod_add by lia; reflexivity.
Qed.

Lemma Q_family_return x y indices s v r :
  6<=x -> 13<=y -> 3<=s -> Forall (fun z => 5<=z) indices ->
  exists d, Progress (Qfront x y (exit_chain (x-1) indices s (v++[Three;Three]) r)) d /\
    ReturnFamily d.
Proof.
  intros Hx Hy Hs Hindices.
  destruct (Q_strong_chain_exit x y indices s (v++[Three;Three]) r Hx Hy Hindices)
    as [xf [b [output_indices [n [t [Hxf [Hb [Hpositive [Hlength [Hrun Hadvance]]]]]]]]]].
  pose proof (Nat.div_mod xf 2 ltac:(lia)) as Hdivide.
  pose proof (Nat.mod_upper_bound xf 2 ltac:(lia)) as Hmod.
  destruct (Nat.eq_dec (xf mod 2) 0) as [Heven|Hodd].
  - assert (Hform : xf=2*(xf/2)) by lia.
    destruct (Q_even_exit_family (xf/2) b output_indices s v r ltac:(lia) Hb Hs Hpositive)
      as [d [Hnext Hd]].
    exists d; split; [|exact Hd].
    eapply progress_after; [exact Hadvance |].
    rewrite Hform; exact Hnext.
  - assert (Hform : xf=2*(xf/2)+1) by lia.
    destruct (Q_odd_exit_family (xf/2) b output_indices s v r ltac:(lia) Hb Hs)
      as [d [Hnext Hd]].
    exists d; split; [|exact Hd].
    eapply progress_after; [exact Hadvance |].
    rewrite Hform.
    replace (2*(xf/2)+1-1) with (2*(xf/2)) by lia; exact Hnext.
Qed.

Lemma return_family_closed c : ReturnFamily c ->
  exists d, Progress c d /\ ReturnFamily d.
Proof.
  intro H; destruct H as [a b d r |d e f r |d f r |x y indices s v r Hx Hy Hs Hindices].
  - apply mixed_return_family; exact (S22_returns a b d r).
  - apply mixed_return_family; exact (H0_returns d e f r).
  - apply mixed_return_family; exact (H1_returns d f r).
  - exact (Q_family_return x y indices s v r Hx Hy Hs Hindices).
Qed.

Definition decoded_return_family (c : Q * tape) : Prop :=
  exists a, ReturnFamily a /\ c = decode a.

Lemma decoded_return_family_closed c : decoded_return_family c ->
  exists d, decoded_return_family d /\ c -[tm]->+ d.
Proof.
  intros [a [Ha ->]].
  destruct (return_family_closed a Ha) as [b [[n [Hn Hrun]] Hb]].
  exists (decode b); split.
  - exists b; auto.
  - rewrite <- Hrun; apply advance_progress; [exact Hn|].
    rewrite Hrun; apply return_family_live; exact Hb.
Qed.

Definition blank_family_entry := shield 59 70 14 (shield59_tail shield28_tail).

Definition blank_entry_clock := 64259+553376.

Lemma blank_to_family_entry : advance blank_entry_clock blank=blank_family_entry.
Proof.
  unfold blank_entry_clock.
  rewrite advance_add,blank_to_shield64259,shield28_to59; reflexivity.
Qed.

Lemma blank_entry_member : ReturnFamily blank_family_entry.
Proof.
  unfold blank_family_entry; apply strong_shield_family; try lia; reflexivity.
Qed.

(* Main result *)

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c' := decode blank_family_entry).
  - rewrite <- decode_blank, <- blank_to_family_entry; apply advance_evstep.
  - eapply progress_nonhalt with (P := decoded_return_family).
    + exact decoded_return_family_closed.
    + exists blank_family_entry; split; [exact blank_entry_member|reflexivity].
Qed.

Print Assumptions nonhalt.
