From BusyCoq Require Import Individual62.
From Coq Require Import Lia NArith List String Wf_nat.

Open Scope sym.
Open Scope list.

Module IndividualProof.

Definition tm := Eval compute in
  (TM_from_str "1RB1RE_1LC1LF_1LD1LC_1RA0LB_---0RF_0RD1RF").

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition U (p : nat) : list Sym := [1;1] ++ [1]^^p ++ [0;0].
Definition V (p : nat) : list Sym := 0 :: ([1]^^p ++ [0;1;1]).
Definition Rot (p : nat) : list Sym := ([1]^^p ++ [0;1;1]) ++ [0].

Lemma V_stream p s :
  V p *> s = 0 >> [1]^^p *> 0 >> 1 >> 1 >> s.
Proof.
  unfold V. cbn. rewrite Str_app_assoc. reflexivity.
Qed.

Lemma U_stream p s :
  U p *> s = 1 >> 1 >> [1]^^p *> [0;0] *> s.
Proof.
  unfold U. repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma U_split p s :
  [1]^^(p+2) *> [0] *> [0] *> s = U p *> s.
Proof.
  unfold U.
  replace (p+2) with (2+p) by lia.
  rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma U_ones p s :
  U p *> s = [1]^^(p+2) *> 0 >> 0 >> s.
Proof.
  unfold U.
  replace (p+2) with (2+p) by lia.
  rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma V_to_Rot p k s :
  (V p)^^k *> 0 >> s = 0 >> (Rot p)^^k *> s.
Proof.
  unfold V, Rot.
  apply lpow_rotate.
Qed.

Lemma V_to_Rot1 p s :
  V p *> 0 >> s = 0 >> Rot p *> s.
Proof.
  pose proof (V_to_Rot p 1 s) as H.
  cbn [lpow] in H.
  repeat rewrite app_nil_r in H.
  exact H.
Qed.

Lemma V_fold p X : [0] *> [1]^^p *> [0;1;1] *> X = V p *> X.
Proof. unfold V. cbn [Str_app]. repeat rewrite Str_app_assoc. reflexivity. Qed.

Lemma lpow_cons_stream (x : list Sym) k Y : x *> x^^k *> Y = x^^(S k) *> Y.
Proof. cbn [lpow]. rewrite Str_app_assoc. reflexivity. Qed.

Lemma V_to_Rot_const0 p k :
  (V p)^^k *> (const 0) = 0 >> (Rot p)^^k *> (const 0).
Proof. unfold V, Rot. apply lpow_rotate_const0. Qed.

Definition P  : list Sym := U 0.        
Definition Q4 : list Sym := U 2.        
Definition M5 : list Sym := U 3.        
Definition T3 : list Sym := U 1.        
Definition J3 : list Sym := [1;1;1;0].  
Definition K4 : list Sym := [1;1;1;1;0]. 
Definition MIDA : list Sym := [1;0;1;1;1;0;1;1;1;1].
Definition MIDB : list Sym := [1;0;1;1].

Definition pairw (a b : nat) : list Sym := [1]^^a ++ [0]^^b.
Definition sym_eqb (a b : Sym) : bool :=
  match a, b with
  | S0, S0 | S1, S1 => true
  | _, _ => false
  end.

Lemma sym_eqb_spec a b : sym_eqb a b = true <-> a = b.
Proof. destruct a, b; cbn; intuition congruence. Qed.

Fixpoint word_eqb (u v : list Sym) : bool :=
  match u, v with
  | [], [] => true
  | a :: u, b :: v => andb (sym_eqb a b) (word_eqb u v)
  | _, _ => false
  end.

Lemma word_eqb_spec u v : word_eqb u v = true <-> u = v.
Proof.
  gen v.
  induction u as [|a u IH]; intros [|b v]; cbn; try (intuition congruence).
  rewrite Bool.andb_true_iff, sym_eqb_spec, IH.
  intuition congruence.
Qed.

Definition chunk : Type := (list Sym * N)%type.
Definition side : Type := list chunk.

Fixpoint decodeS (s : side) : Stream Sym :=
  match s with
  | [] => const 0
  | (w, k) :: t => w^^(N.to_nat k) *> decodeS t
  end.

Definition conf (zl : side) (cur : Sym) (zr : side) : Q * tape :=
  (cur >> decodeS zl) <{{D}} decodeS zr.

Lemma lpow_nil_word (n : nat) (X : Stream Sym) :
  ([] : list Sym)^^n *> X = X.
Proof. induction n as [|n IH]; cbn; [reflexivity | exact IH]. Qed.

Lemma lpow_S_word (w : list Sym) (n : nat) (X : Stream Sym) :
  w^^(S n) *> X = w *> w^^n *> X.
Proof. cbn [lpow]. rewrite Str_app_assoc. reflexivity. Qed.

Fixpoint pop_bit (s : side) : Sym * side :=
  match s with
  | [] => (0, [])
  | ([], _) :: t => pop_bit t
  | (_, N0) :: t => pop_bit t
  | (b :: w, N.pos p) :: t =>
    (b,
     match w, Pos.pred_N p with
     | [], N0 => t
     | [], k' => ([b], k') :: t
     | _ :: _, N0 => (w, 1%N) :: t
     | _ :: _, k' => (w, 1%N) :: (b :: w, k') :: t
     end)
  end.

Lemma pop_bit_cons b w p t :
  pop_bit ((b :: w, N.pos p) :: t) =
  (b,
   match w, Pos.pred_N p with
   | [], N0 => t
   | [], k' => ([b], k') :: t
   | _ :: _, N0 => (w, 1%N) :: t
   | _ :: _, k' => (w, 1%N) :: (b :: w, k') :: t
   end).
Proof. reflexivity. Qed.

Lemma pop_bit_sound s :
  decodeS s = fst (pop_bit s) >> decodeS (snd (pop_bit s)).
Proof.
  induction s as [|[w k] t IH].
  - cbn. apply const_unfold.
  - destruct w as [|b w].
    + destruct k; cbn [pop_bit decodeS]; rewrite lpow_nil_word; exact IH.
    + destruct k as [|p].
      * cbn [pop_bit decodeS]. cbn [N.to_nat lpow Str_app]. exact IH.
      * rewrite pop_bit_cons.
        cbn [decodeS fst snd].
        destruct (N.to_nat (N.pos p)) as [|nk] eqn:Ek; [lia|].
        rewrite lpow_S_word. cbn [Str_app].
        f_equal.
        destruct w as [|c w]; destruct (Pos.pred_N p) as [|q] eqn:Eq;
          [ replace nk with O by lia; cbn; reflexivity
          | idtac
          | replace nk with O by lia;
            cbn [decodeS];
            replace (N.to_nat 1) with 1%nat by reflexivity;
            cbn [lpow];
            rewrite app_nil_r; cbn [lpow Str_app]; reflexivity
          | cbn [decodeS];
            replace (N.to_nat (N.pos q)) with nk by lia;
            replace (N.to_nat 1) with 1%nat by reflexivity;
            cbn [lpow]; rewrite app_nil_r;
            rewrite <- Str_app_assoc;
            reflexivity ].
        cbn [decodeS].
        replace (N.to_nat (N.pos q)) with nk by lia.
        cbn [Str_app].
        reflexivity.
Qed.

Lemma pop_bit_split s b s' :
  pop_bit s = (b, s') -> decodeS s = b >> decodeS s'.
Proof.
  intros H.
  rewrite (pop_bit_sound s), H.
  reflexivity.
Qed.

Fixpoint ones_prefix (w : list Sym) : nat * list Sym :=
  match w with
  | S1 :: w' => let (j, r) := ones_prefix w' in (S j, r)
  | _ => (O, w)
  end.

Lemma ones_prefix_split w :
  w = [1]^^(fst (ones_prefix w)) ++ snd (ones_prefix w).
Proof.
  induction w as [|a w IH].
  - reflexivity.
  - destruct a; cbn [ones_prefix].
    + reflexivity.
    + destruct (ones_prefix w) as [j r] eqn:E.
      cbn [fst snd] in *.
      cbn [lpow].
      change ([1] ^^ S j) with ([1] ++ [1]^^j).
      cbn [app].
      f_equal.
      exact IH.
Qed.

Lemma ones_prefix_head w :
  match snd (ones_prefix w) with
  | [] => True
  | a :: _ => a = 0
  end.
Proof.
  induction w as [|a w IH].
  - cbn. exact I.
  - destruct a; cbn [ones_prefix].
    + cbn. reflexivity.
    + destruct (ones_prefix w) as [j r]. cbn [snd] in *. exact IH.
Qed.

Fixpoint pop_ones (s : side) : N * side :=
  match s with
  | [] => (0%N, [])
  | (w, k) :: t =>
    match k with
    | N0 => pop_ones t
    | _ =>
      let (j, r) := ones_prefix w in
      match r with
      | [] =>
                let (n2, t2) := pop_ones t in
        ((N.of_nat j * k + n2)%N, t2)
      | _ :: _ =>
        match j with
        | O => (0%N, s)
        | _ =>
          match N.pred k with
          | N0 => (N.of_nat j, (r, 1%N) :: t)
          | k' => (N.of_nat j, (r, 1%N) :: (w, k') :: t)
          end
        end
      end
    end
  end.

Lemma lpow_ones_add (a b : nat) (X : Stream Sym) :
  [1]^^a *> [1]^^b *> X = [1]^^(a+b) *> X.
Proof. apply lpow_add'. Qed.

Lemma ones_pattern_pow (j : nat) (kn : nat) (X : Stream Sym) :
  ([1]^^j)^^kn *> X = [1]^^(kn * j) *> X.
Proof.
  induction kn as [|kn IH]; cbn [lpow].
  - reflexivity.
  - rewrite Str_app_assoc, IH.
    rewrite lpow_ones_add.
    replace (j + kn * j) with (S kn * j) by lia.
    reflexivity.
Qed.

Lemma pop_ones_sound s :
  decodeS s = [1]^^(N.to_nat (fst (pop_ones s))) *> decodeS (snd (pop_ones s))
  /\ exists r', decodeS (snd (pop_ones s)) = 0 >> r'.
Proof.
  induction s as [|[w k] t IH].
  - cbn. split.
    + reflexivity.
    + exists (const 0). apply const_unfold.
  - destruct k as [|p].
    + cbn [pop_ones decodeS]. cbn [N.to_nat lpow Str_app]. exact IH.
    + cbn [pop_ones].
      destruct (ones_prefix w) as [j r] eqn:E.
      pose proof (ones_prefix_split w) as Hw.
      pose proof (ones_prefix_head w) as Hh.
      rewrite E in Hw, Hh. cbn [fst snd] in Hw, Hh.
      destruct r as [|a r'].
      *         rewrite app_nil_r in Hw.
        destruct (pop_ones t) as [n2 t2] eqn:E2.
        cbn [fst snd] in *.
        destruct IH as [IH1 IH2].
        split; [|exact IH2].
        cbn [decodeS fst snd].
        rewrite Hw, ones_pattern_pow, IH1.
        rewrite lpow_ones_add.
        rewrite N2Nat.inj_add, N2Nat.inj_mul, Nat2N.id.
        f_equal. f_equal. lia.
      * destruct j as [|j'].
        --            cbn [fst snd].
           split.
           ++ cbn [N.to_nat lpow Str_app]. reflexivity.
           ++ cbn [decodeS].
              destruct (N.to_nat (N.pos p)) as [|nk] eqn:Ek; [lia|].
              rewrite lpow_S_word.
              cbn [lpow] in Hw.
              rewrite Hw. cbn [app].
              subst a.
              eexists. cbn [Str_app]. reflexivity.
        --            subst a.
           destruct (N.pred (N.pos p)) as [|q] eqn:Eq.
           ++ cbn [fst snd].
              assert (Hp1 : N.to_nat (N.pos p) = 1%nat) by lia.
              split.
              ** cbn [decodeS].
                 rewrite Hp1. cbn [lpow]. rewrite app_nil_r.
                 rewrite Hw at 1.
                 rewrite Str_app_assoc.
                 rewrite Nat2N.id.
                 replace (N.to_nat 1) with 1%nat by reflexivity.
                 cbn [lpow]. rewrite app_nil_r.
                 reflexivity.
              ** cbn [decodeS].
                 replace (N.to_nat 1) with 1%nat by reflexivity.
                 cbn [lpow]. rewrite app_nil_r.
                 eexists. cbn [Str_app]. reflexivity.
           ++ cbn [fst snd].
              split.
              ** cbn [decodeS].
                 destruct (N.to_nat (N.pos p)) as [|nk] eqn:Ek; [lia|].
                 rewrite lpow_S_word.
                 rewrite Hw at 1.
                 rewrite Str_app_assoc.
                 rewrite Nat2N.id.
                 replace (N.to_nat (N.pos q)) with nk by lia.
                 replace (N.to_nat 1) with 1%nat by reflexivity.
                 cbn [lpow]. rewrite app_nil_r.
                 reflexivity.
              ** cbn [decodeS].
                 replace (N.to_nat 1) with 1%nat by reflexivity.
                 cbn [lpow]. rewrite app_nil_r.
                 eexists. cbn [Str_app]. reflexivity.
Qed.

Definition push (c : chunk) (s : side) : side :=
  let (w, k) := c in
  match k with
  | N0 => s
  | _ =>
    match s with
    | (w', k') :: t => if word_eqb w w' then (w, (k + k')%N) :: t else c :: s
    | [] => [c]
    end
  end.

Lemma push_sound c s :
  decodeS (push c s) = (fst c)^^(N.to_nat (snd c)) *> decodeS s.
Proof.
  destruct c as [w k].
  cbn [fst snd].
  destruct k as [|p].
  - cbn [push N.to_nat lpow Str_app]. reflexivity.
  - destruct s as [|[w' k'] t].
    + reflexivity.
    + cbn [push].
      destruct (word_eqb w w') eqn:Ew.
      * apply word_eqb_spec in Ew. subst w'.
        cbn [decodeS].
        rewrite N2Nat.inj_add.
        rewrite <- lpow_add'.
        reflexivity.
      * reflexivity.
Qed.

Fixpoint push_bits (bits : list Sym) (s : side) : side :=
  match bits with
  | [] => s
  | b :: rest => push ([b], 1%N) (push_bits rest s)
  end.

Lemma push_bits_sound bits s :
  decodeS (push_bits bits s) = bits *> decodeS s.
Proof.
  induction bits as [|b bits IH].
  - reflexivity.
  - cbn [push_bits Str_app].
    rewrite push_sound, IH.
    cbn [fst snd].
    replace (N.to_nat 1) with 1%nat by reflexivity.
    cbn [lpow]. rewrite app_nil_r.
    reflexivity.
Qed.

Fixpoint flat (front : list chunk) : list Sym :=
  match front with
  | [] => []
  | (w, k) :: t => w^^(N.to_nat k) ++ flat t
  end.

Lemma decode_app front rest :
  decodeS (front ++ rest) = flat front *> decodeS rest.
Proof.
  induction front as [|[w k] t IH].
  - reflexivity.
  - cbn [flat app decodeS].
    rewrite IH, Str_app_assoc.
    reflexivity.
Qed.

Definition chunk_bitlen (c : chunk) : N :=
  (N.of_nat (List.length (fst c)) * snd c)%N.

Fixpoint peel_fuel (fuel : nat) (budget : N) (s : side)
  : list chunk * side :=
  match fuel with
  | O => ([], s)
  | S fuel =>
    match s with
    | [] => ([], [])
    | c :: t =>
      let bl := chunk_bitlen c in
      if (bl <=? budget)%N then
        let (front, rest) := peel_fuel fuel (budget - bl)%N t in
        (c :: front, rest)
      else ([], s)
    end
  end.

Definition peel (s : side) : list Sym * side :=
  let (front, rest) := peel_fuel 32 32%N s in
  (flat front, rest).

Lemma peel_fuel_split fuel budget s :
  s = fst (peel_fuel fuel budget s) ++ snd (peel_fuel fuel budget s).
Proof.
  gen budget s.
  induction fuel as [|fuel IH]; intros budget s.
  - reflexivity.
  - destruct s as [|c t]; [reflexivity|].
    cbn [peel_fuel].
    destruct (chunk_bitlen c <=? budget)%N.
    + destruct (peel_fuel fuel (budget - chunk_bitlen c) t) as [front rest] eqn:E.
      specialize (IH (budget - chunk_bitlen c)%N t).
      rewrite E in IH. cbn [fst snd] in IH.
      cbn [fst snd app].
      congruence.
    + reflexivity.
Qed.

Lemma peel_sound s :
  decodeS s = fst (peel s) *> decodeS (snd (peel s)).
Proof.
  unfold peel.
  destruct (peel_fuel 32 32 s) as [front rest] eqn:E.
  cbn [fst snd].
  pose proof (peel_fuel_split 32 32 s) as Hs.
  rewrite E in Hs. cbn [fst snd] in Hs.
  rewrite Hs at 1.
  apply decode_app.
Qed.

Fixpoint absorb_fuel (fuel : nat) (bits : list Sym) (s : side)
  : list Sym * side :=
  match fuel with
  | O => (bits, s)
  | S fuel =>
    match s with
    | (w, k) :: t =>
      let n := List.length w in
      let m := List.length bits in
      if andb (Nat.leb 1 n) (Nat.leb n m) then
        if word_eqb (List.skipn (m - n) bits) w then
          absorb_fuel fuel (List.firstn (m - n) bits) ((w, N.succ k) :: t)
        else (bits, s)
      else (bits, s)
    | [] => (bits, s)
    end
  end.

Definition absorb (bits : list Sym) (s : side) : list Sym * side :=
  absorb_fuel 32 bits s.

Lemma absorb_fuel_sound fuel bits s :
  let (bits', s') := absorb_fuel fuel bits s in
  bits *> decodeS s = bits' *> decodeS s'.
Proof.
  gen bits s.
  induction fuel as [|fuel IH]; intros bits s.
  - cbn. reflexivity.
  - destruct s as [|[w k] t].
    + reflexivity.
    + cbn [absorb_fuel].
      destruct (andb (Nat.leb 1 (List.length w))
                     (Nat.leb (List.length w) (List.length bits))) eqn:Eg;
        [|reflexivity].
      apply Bool.andb_true_iff in Eg.
      destruct Eg as [E1 E2].
      apply PeanoNat.Nat.leb_le in E1.
      apply PeanoNat.Nat.leb_le in E2.
      destruct (word_eqb (List.skipn (List.length bits - List.length w) bits) w)
        eqn:Es; [|reflexivity].
      apply word_eqb_spec in Es.
      specialize (IH (List.firstn (List.length bits - List.length w) bits)
                     ((w, N.succ k) :: t)).
      destruct (absorb_fuel fuel _ _) as [bits' s'] eqn:E.
      rewrite <- IH.
      rewrite <- (List.firstn_skipn (List.length bits - List.length w) bits) at 1.
      rewrite Es.
      cbn [decodeS].
      rewrite Str_app_assoc.
      rewrite N2Nat.inj_succ, lpow_S_word.
      reflexivity.
Qed.

Fixpoint runs (bits : list Sym) : side :=
  match bits with
  | [] => []
  | b :: rest => push ([b], 1%N) (runs rest)
  end.

Definition zstate : Type := (side * Sym * side)%type.

Definition zconf (z : zstate) : Q * tape :=
  let '(zl, cur, zr) := z in conf zl cur zr.

Fixpoint first_true (w : list Sym) (cands : list nat) : nat :=
  match cands with
  | [] => List.length w
  | d :: rest =>
    if andb (Nat.eqb (Nat.modulo (List.length w) d) 0)
            (word_eqb w ((List.firstn d w) ^^ (Nat.div (List.length w) d)))
    then d
    else first_true w rest
  end.

Definition prim_root (w : list Sym) : list Sym * nat :=
  let d := first_true w (List.seq 1 (List.length w)) in
  (List.firstn d w, Nat.div (List.length w) d).

Fixpoint merge_pass (s : side) : side :=
  match s with
  | [] => []
  | (w, k) :: t =>
    let (u, d) := prim_root w in
    push (u, (N.of_nat d * k)%N) (merge_pass t)
  end.

Definition pair_guard (c1 c2 : chunk) : bool :=
  match c1, c2 with
  | ([S1], a), ([S0], b) => andb (N.leb a 64) (N.leb b 64)
  | _, _ => false
  end.

Definition mk_pair (c1 c2 : chunk) : chunk :=
  (pairw (N.to_nat (snd c1)) (N.to_nat (snd c2)), 1%N).

Fixpoint pair_pass (s : side) : side :=
  match s with
  | [] => []
  | c1 :: t1 =>
    match t1 with
    | c2 :: t2 =>
      if pair_guard c1 c2
      then mk_pair c1 c2 :: pair_pass t2
      else c1 :: pair_pass t1
    | [] => [c1]
    end
  end.

Definition vform_guard (c1 c2 c3 c4 : chunk) : bool :=
  match c1, c2, c3, c4 with
  | ([S0], N.pos xH), ([S1], m), ([S0], N.pos xH), ([S1], r) =>
    andb (N.leb m 64) (N.leb 2 r)
  | _, _, _, _ => false
  end.

Fixpoint vform_pass (s : side) : side :=
  match s with
  | [] => []
  | c1 :: t1 =>
    match t1 with
    | c2 :: (c3 :: (c4 :: t2)) =>
      if vform_guard c1 c2 c3 c4
      then (V (N.to_nat (snd c2)), 1%N)
             :: push ([S1], (snd c4 - 2)%N) (vform_pass t2)
      else c1 :: vform_pass t1
    | _ => c1 :: vform_pass t1
    end
  end.

Definition compress_right (s : side) : side :=
  let (bits, rest0) := peel s in
  let (bits2, rest) := absorb bits rest0 in
  let head := runs bits2 ++ List.firstn 1 rest in
  merge_pass (pair_pass (merge_pass (pair_pass (merge_pass head))))
    ++ List.skipn 1 rest.

Definition compress_left (s : side) : side :=
  let (bits, rest0) := peel s in
  let (bits2, rest) := absorb bits rest0 in
  let head := runs bits2 ++ List.firstn 1 rest in
  merge_pass (vform_pass (merge_pass (vform_pass (merge_pass head))))
    ++ List.skipn 1 rest.

Definition znorm (z : zstate) : zstate :=
  let '(zl, cur, zr) := z in
  (compress_left zl, cur, compress_right zr).

Definition is_halt (z : zstate) : bool :=
  let '(zl, cur, zr) := z in
  match cur with
  | S0 =>
    let (b0, r1) := pop_bit zr in
    match b0 with
    | S1 => let (b1, _) := pop_bit r1 in
            match b1 with S0 => true | S1 => false end
    | S0 => false
    end
  | S1 => false
  end.

Definition op_clean (z : zstate) : option (zstate * N) :=
  let '(zl, cur, zr) := z in
  match zl, cur with
  | [], S0 =>
    match zr with
    | (w1, a) :: (w2, k2) :: rest =>
      if andb (andb (word_eqb w1 P) (word_eqb w2 M5))
              (andb (N.eqb k2 1) (N.leb 1 a)) then
        let handle :=
          fun (m : N) (rest2 : side) =>
            match rest2 with
            | (w4, k) :: rest3 =>
              if andb (word_eqb w4 J3) (N.leb 2 k) then
                let r := (k / 2)%N in
                let n := (k mod 2)%N in
                Some (([] : side, S0,
                      push (P, (a + 3*r)%N)
                        (push (M5, 1%N)
                          (push (T3, (m + r)%N)
                            (push (J3, n) rest3)))),
                      (r * (123 + 30*a + 36*m) + 63 * (r * (r-1)))%N)
              else None
            | [] => None
            end in
        match rest with
        | (w3, m) :: rest2 =>
          if word_eqb w3 T3 then handle m rest2
          else handle 0%N rest
        | [] => None
        end
      else None
    | _ => None
    end
  | _, _ => None
  end.

Definition op_four (z : zstate) : option (zstate * N) :=
  let '(zl, cur, zr) := z in
  match zl, cur with
  | [], S0 =>
    match zr with
    | (w1, a) :: (w2, m) :: (w3, k) :: rest =>
      if andb (andb (word_eqb w1 P) (word_eqb w2 Q4))
              (andb (word_eqb w3 K4)
                    (andb (N.leb 1 a) (andb (N.leb 1 m) (N.leb 2 k)))) then
        let r := (k / 2)%N in
        let n := (k mod 2)%N in
        Some (([] : side, S0,
              push (P, (a + 4*r)%N)
                (push (Q4, (m + r)%N)
                  (push (K4, n) rest))),
              (r * (128 + 40*a + 56*m) + 108 * (r * (r-1)))%N)
      else None
    | _ => None
    end
  | _, _ => None
  end.

Fixpoint pop_bits_expect (bits : list Sym) (s : side) : option side :=
  match bits with
  | [] => Some s
  | b :: rest =>
    let (b', s') := pop_bit s in
    if sym_eqb b b' then pop_bits_expect rest s' else None
  end.

Definition MIDA_B : list Sym := [0;1;1;1;0;1;1;1;1].
Definition MIDB_B : list Sym := [0;1;1].

Definition shift_apply (mid : list Sym) (x xo : list Sym) (z0 : bool)
    (per : N) (blockcost : N) (zl zr : side)
    : option (side * side * N) :=
  match pop_bits_expect mid zl with
  | Some s =>
    match s with
    | (w, k) :: t =>
      if word_eqb w x then
        let j0 := (k / per)%N in
        let rem0 := (k mod per)%N in
        let adjust :=
          if andb z0 (N.eqb rem0 0) then
            match pop_bit t with
            | (S0, _) => (j0, rem0)
            | (S1, _) => ((j0 - 1)%N, per)
            end
          else (j0, rem0) in
        let (j, rem) := adjust in
        if (1 <=? j)%N then
          Some (push_bits mid (push (x, rem) t), push (xo, j) zr,
                (j * blockcost)%N)
        else None
      else None
    | [] => None
    end
  | None => None
  end.

Definition op_shiftA (zl zr : side) : option (side * side * N) :=
  shift_apply MIDA_B (V 0) J3 false 1 24 zl zr.
Definition op_shiftB (zl zr : side) : option (side * side * N) :=
  shift_apply MIDB_B (V 1) K4 false 1 5 zl zr.
Definition op_shiftQ (zl zr : side) : option (side * side * N) :=
  shift_apply [1] [0;1;1] Q4 true 2 8 zl zr.

Definition op_shift (z : zstate) : option (zstate * N) :=
  let '(zl, cur, zr) := z in
  match cur with
  | S1 =>
    match op_shiftA zl zr with
    | Some (zl2, zr2, c) => Some ((zl2, S1, zr2), c)
    | None =>
      match op_shiftB zl zr with
      | Some (zl2, zr2, c) => Some ((zl2, S1, zr2), c)
      | None =>
        match op_shiftQ zl zr with
        | Some (zl2, zr2, c) => Some ((zl2, S1, zr2), c)
        | None => None
        end
      end
    end
  | S0 => None
  end.

Definition upat (w : list Sym) : option nat :=
  let (a, r) := ones_prefix w in
  match r with
  | [S0; S0] => match a with S (S p) => Some p | _ => None end
  | _ => None
  end.

Definition vpat (w : list Sym) : option nat :=
  match w with
  | S0 :: rest =>
    let (p, r) := ones_prefix rest in
    if word_eqb r [0;1;1] then Some p else None
  | _ => None
  end.

Definition op_bulkR (z : zstate) : option (zstate * N) :=
  let '(zl, cur, zr) := z in
  match cur with
  | S0 =>
    match zr with
    | (w, k) :: t =>
      match upat w with
      | Some p => Some ((push (V p, k) zl, S0, t),
                        (k * (N.of_nat p + 4))%N)
      | None => None
      end
    | [] => None
    end
  | S1 => None
  end.

Definition op_bulkL (z : zstate) : option (zstate * N) :=
  let '(zl, cur, zr) := z in
  match cur with
  | S1 =>
    match zl with
    | (w, k) :: rest =>
      match vpat w with
      | Some p =>
        match pop_bit rest with
        | (S0, rest') =>
          match pop_bit zr with
          | (S0, zr') =>
            Some ((push ([S0], 1%N) rest', S1,
                  push ([S0], 1%N) (push (U p, k) zr')),
                  (k * (N.of_nat p + 6))%N)
          | _ => None
          end
        | _ => None
        end
      | None => None
      end
    | [] => None
    end
  | S0 => None
  end.

Definition op_section (z : zstate) : zstate * N :=
  let '(zl, cur, zr) := z in
  match cur with
  | S0 =>
    let (b0, r1) := pop_bit zr in
    match b0 with
    | S0 =>
      let (b1, r2) := pop_bit r1 in
      match b1 with
      | S0 =>
                let (n, l1) := pop_ones zl in
        let (_, l2) := pop_bit l1 in
        let (cur2, l3) := pop_bit l2 in
        ((l3, cur2, push ([S1], (n + 4)%N) r2), (n + 6)%N)
      | S1 =>
                let (m, r3) := pop_ones r2 in
        let (_, r4) := pop_bit r3 in
        let (cur2, r5) := pop_bit r4 in
        ((push ([S0], 1%N) (push ([S1], (m + 3)%N) zl), cur2, r5),
         (m + 6)%N)
      end
    | S1 =>
      let (b1, r2) := pop_bit r1 in
      match b1 with
      | S0 => (z, 0%N)       | S1 =>
                let (m, r3) := pop_ones r2 in
        let (_, r4) := pop_bit r3 in
        let (cur2, r5) := pop_bit r4 in
        ((push ([S0], 1%N)
           (push ([S1], m)
             (push ([S0], 1%N)
               (push ([S1], 2%N) zl))), cur2, r5), (m + 4)%N)
      end
    end
  | S1 =>
    let (l0, l1s) := pop_bit zl in
    match l0 with
    | S0 =>
            let (m, l2) := pop_ones l1s in
      let (_, l3) := pop_bit l2 in
      let (cur2, l4) := pop_bit l3 in
      ((l4, cur2, push ([S1], (m + 2)%N) (push ([S0], 1%N) zr)),
       (m + 3)%N)
    | S1 =>
      let (l1b, l2s) := pop_bit l1s in
      match l1b with
      | S0 =>
                ((push ([S0], 1%N) l2s, S1, push ([S0], 1%N) zr), 3%N)
      | S1 =>
                let (cur2, r2) := pop_bit zr in
        ((push ([S0], 1%N) zl, cur2, r2), 5%N)
      end
    end
  end.

Definition zstep (z : zstate) : option (zstate * N) :=
  if is_halt z then None
  else
    let zc :=
      match op_clean z with
      | Some zc => zc
      | None =>
        match op_four z with
        | Some zc => zc
        | None =>
          match op_shift z with
          | Some zc => zc
          | None =>
            match op_bulkR z with
            | Some zc => zc
            | None =>
              match op_bulkL z with
              | Some zc => zc
              | None => op_section z
              end
            end
          end
        end
      end in
    Some (znorm (fst zc), snd zc).

Fixpoint zrun (p : positive) (z : zstate) (acc : N)
  : option zstate * N :=
  match p with
  | xH =>
    match zstep z with
    | Some (z2, c) => (Some z2, (acc + c)%N)
    | None => (None, acc)
    end
  | xO q =>
    match zrun q z acc with
    | (Some z2, acc2) => zrun q z2 acc2
    | (None, acc2) => (None, acc2)
    end
  | xI q =>
    match zrun q z acc with
    | (Some z2, acc2) =>
      match zrun q z2 acc2 with
      | (Some z3, acc3) =>
        match zstep z3 with
        | Some (z4, c) => (Some z4, (acc3 + c)%N)
        | None => (None, acc3)
        end
      | (None, acc3) => (None, acc3)
      end
    | (None, acc2) => (None, acc2)
    end
  end.

Definition zinit : zstate := ([], S0, [([S1], 3%N)]).

Lemma pop_ones_split s n s' :
  pop_ones s = (n, s') ->
  decodeS s = [1]^^(N.to_nat n) *> decodeS s' /\
  exists r', decodeS s' = 0 >> r'.
Proof.
  intros H.
  pose proof (pop_ones_sound s) as [H1 H2].
  rewrite H in H1, H2. cbn [fst snd] in *.
  split; assumption.
Qed.

Lemma push_run_decode (b : Sym) (n : N) (s : side) :
  decodeS (push ([b], n) s) = [b]^^(N.to_nat n) *> decodeS s.
Proof. apply push_sound. Qed.

Notation "c =( n )=> c'" := (c -[ tm ]->> n / c') (at level 40, n at next level).

Lemma cmul_refl' n (c c' : Q * tape) :
  n = O -> c = c' -> c =( n )=> c'.
Proof. intros -> ->. apply multistep_0. Qed.

Ltac cstep := eapply multistep_S; [prove_step|].
Ltac cfinish := apply cmul_refl'; [reflexivity | simpl_tape; reflexivity].
Ltac cexec := repeat cstep; cfinish.

Lemma cmul_trans_eq {n m : nat} (k : nat) c c' c'' :
  c =( n )=> c' -> c' =( m )=> c'' -> k = (n + m)%nat -> c =( k )=> c''.
Proof. intros H1 H2 ->. eapply multistep_trans; eauto. Qed.

Lemma cscan_C_left n l r :
  l <* [1]^^n <{{C}} r =( n )=> l <{{C}} [1]^^n *> r.
Proof.
  gen l r.
  induction n as [|n IH]; intros l r.
  - cfinish.
  - cbn [lpow]. simpl_tape.
    cstep.
    eapply cmul_trans_eq.
    + apply IH.
    + apply cmul_refl'; [reflexivity|].
      rewrite lpow_shift1. reflexivity.
    + lia.
Qed.

Lemma cscan_F_right n l r :
  l {{F}}> [1]^^n *> r =( n )=> l <* [1]^^n {{F}}> r.
Proof.
  gen l r.
  induction n as [|n IH]; intros l r.
  - cfinish.
  - cbn [lpow]. simpl_tape.
    cstep.
    eapply cmul_trans_eq.
    + apply IH.
    + apply cmul_refl'; [reflexivity|].
      rewrite lpow_shift1. reflexivity.
    + lia.
Qed.

Lemma csection_D0_00 n l r :
  l <* [0] <* [1]^^n <* [0] <{{D}} [0;0] *> r =( n + 6 )=>
  l <{{D}} [1]^^(n+4) *> r.
Proof.
  replace (n + 6)%nat with (S (S (S (S (S (n + 1)))))) by lia.
  do 5 cstep.
  eapply cmul_trans_eq.
  - apply cscan_C_left.
  - cstep.
    apply cmul_refl'; [reflexivity|].
    simpl_tape.
    rewrite <- lpow_shift1.
    replace (n+4) with (S (S (S (S n)))) by lia.
    cbn [lpow]. simpl_tape. reflexivity.
  - lia.
Qed.

Lemma csection_D0_01 n l r :
  l <* [0] <{{D}} [0;1] *> [1]^^n *> [0] *> r =( n + 6 )=>
  l <* [1]^^(n+3) <* [0] {{D}}> r.
Proof.
  replace (n + 6)%nat with (S (S (S (S (S (n + 1)))))) by lia.
  do 5 cstep.
  eapply cmul_trans_eq.
  - apply cscan_F_right.
  - cstep.
    apply cmul_refl'; [reflexivity|].
    simpl_tape.
    replace (n+3) with (S (S (S n))) by lia.
    cbn [lpow]. simpl_tape. reflexivity.
  - lia.
Qed.

Lemma csection_D0_10 l r :
  l <* [0] <{{D}} [1;0] *> r =( 2 )=>
  l <* [1;1] {{E}}> [0] *> r.
Proof. cexec. Qed.

Lemma csection_D0_11 n l r :
  l <* [0] <{{D}} [1;1] *> [1]^^n *> [0] *> r =( n + 4 )=>
  l <* [0;1;1] <* [1]^^n <* [0] {{D}}> r.
Proof.
  replace (n + 4)%nat with (S (S (S (n + 1)))) by lia.
  do 3 cstep.
  eapply cmul_trans_eq.
  - apply cscan_F_right.
  - cstep.
    apply cmul_refl'; [reflexivity|].
    simpl_tape. reflexivity.
  - lia.
Qed.

Lemma csection_D1_0 n l r :
  l <* [0] <* [1]^^n <* [1;0] <{{D}} r =( n + 3 )=>
  l <{{D}} [1]^^(n+2) *> [0] *> r.
Proof.
  replace (n + 3)%nat with (S (S (n + 1))) by lia.
  do 2 cstep.
  eapply cmul_trans_eq.
  - apply cscan_C_left.
  - cstep.
    apply cmul_refl'; [reflexivity|].
    simpl_tape.
    rewrite <- lpow_shift1.
    replace (n+2) with (S (S n)) by lia.
    cbn [lpow]. simpl_tape. reflexivity.
  - lia.
Qed.

Lemma csection_D1_1_left l r :
  l <* [1;1;0] <{{D}} r =( 3 )=> l <* [1;0] <{{D}} [0] *> r.
Proof. cexec. Qed.

Lemma csection_D1_1_right l r :
  l <* [1;1;1] <{{D}} r =( 5 )=> l <* [0;1;1] {{D}}> r.
Proof. cexec. Qed.

Lemma ctraverse_right_U_one p l r :
  l <* [0] <{{D}} U p *> r =( p + 4 )=>
  l <* V p <* [0] <{{D}} r.
Proof.
  eapply cmul_trans_eq.
  - rewrite U_stream.
    change (1 >> 1 >> [1]^^p *> [0;0] *> r)
      with ([1;1] *> [1]^^p *> [0] *> ([0] *> r)).
    apply csection_D0_11.
  - apply cmul_refl'; [reflexivity|].
    rewrite V_stream. reflexivity.
  - lia.
Qed.

Lemma ctraverse_right_U p k l r :
  l <* [0] <{{D}} (U p)^^k *> r =( k * (p + 4) )=>
  l <* (V p)^^k <* [0] <{{D}} r.
Proof.
  gen l r.
  induction k as [|k IH]; intros l r.
  - cfinish.
  - cbn [lpow]. rewrite Str_app_assoc.
    eapply cmul_trans_eq.
    + apply ctraverse_right_U_one.
    + eapply cmul_trans_eq.
      * apply IH.
      * apply cmul_refl'; [reflexivity|].
        rewrite Str_app_assoc, lpow_shift'.
        reflexivity.
      * reflexivity.
    + lia.
Qed.

Lemma ctraverse_left_Rot_one p l r :
  l <* Rot p <* [1;0] <{{D}} [0] *> r =( p + 6 )=>
  l <* [1;0] <{{D}} [0] *> U p *> r.
Proof.
  eapply cmul_trans_eq.
  - unfold Rot.
    repeat rewrite Str_app_assoc.
    apply (csection_D1_0 p (l <* [1;1;0]) ([0] *> r)).
  - eapply cmul_trans_eq.
    + apply csection_D1_1_left.
    + apply cmul_refl'; [reflexivity|].
      rewrite U_ones.
      reflexivity.
    + reflexivity.
  - lia.
Qed.

Lemma ctraverse_left_Rot p k l r :
  l <* (Rot p)^^k <* [1;0] <{{D}} [0] *> r =( k * (p + 6) )=>
  l <* [1;0] <{{D}} [0] *> (U p)^^k *> r.
Proof.
  gen l r.
  induction k as [|k IH]; intros l r.
  - cfinish.
  - cbn [lpow]. repeat rewrite Str_app_assoc.
    eapply cmul_trans_eq.
    + apply ctraverse_left_Rot_one.
    + eapply cmul_trans_eq.
      * apply IH.
      * apply cmul_refl'; [reflexivity|].
        rewrite lpow_shift'.
        reflexivity.
      * reflexivity.
    + lia.
Qed.

Lemma cshiftL_ctx (x x' mid : list Sym) (c : nat)
    (Hone : forall l r, l <* x <* mid <{{D}} r =( c )=>
                        l <* mid <{{D}} x' *> r) :
  forall n l r, l <* x^^n <* mid <{{D}} r =( n * c )=>
                l <* mid <{{D}} x'^^n *> r.
Proof.
  intros n.
  induction n as [|n IH]; intros l r.
  - cfinish.
  - replace (x^^(S n)) with (x ++ x^^n) by reflexivity.
    rewrite Str_app_assoc.
    eapply cmul_trans_eq.
    + apply (Hone (l <* x^^n) r).
    + eapply cmul_trans_eq.
      * apply (IH l (x' *> r)).
      * apply cmul_refl'; [reflexivity|].
        replace (x'^^(S n)) with (x' ++ x'^^n) by reflexivity.
        rewrite Str_app_assoc, lpow_shift'.
        reflexivity.
      * reflexivity.
    + lia.
Qed.

Lemma cbridgeA_one l r :
  l <* V 0 <* MIDA <{{D}} r =( 24 )=> l <* MIDA <{{D}} J3 *> r.
Proof.
  change (V 0) with ([0;0;1;1] : list Sym).
  unfold MIDA, J3.
  cexec.
Qed.

Lemma cbridgeB_one l r :
  l <* V 1 <* MIDB <{{D}} r =( 5 )=> l <* MIDB <{{D}} K4 *> r.
Proof.
  change (V 1) with ([0;1;0;1;1] : list Sym).
  unfold MIDB, K4.
  cexec.
Qed.

Lemma cshiftQ_one l r :
  l <* [1;1;0;1;1;0] <* [1;1;0] <{{D}} r =( 8 )=>
  l <* [1;1;0] <{{D}} Q4 *> r.
Proof. unfold Q4, U. cexec. Qed.

Lemma cbridgeA n l r :
  l <* (V 0)^^n <* MIDA <{{D}} r =( n * 24 )=>
  l <* MIDA <{{D}} J3^^n *> r.
Proof. apply cshiftL_ctx, cbridgeA_one. Qed.

Lemma cbridgeB n l r :
  l <* (V 1)^^n <* MIDB <{{D}} r =( n * 5 )=>
  l <* MIDB <{{D}} K4^^n *> r.
Proof. apply cshiftL_ctx, cbridgeB_one. Qed.

Lemma cshiftQ_bulk j l r :
  l <* [1;1;0;1;1;0]^^j <* [1;1;0] <{{D}} r =( j * 8 )=>
  l <* [1;1;0] <{{D}} Q4^^j *> r.
Proof. apply cshiftL_ctx, cshiftQ_one. Qed.

Lemma cleft_edge_close w :
  0inf <* [1;0] <{{D}} [0] *> w =( 3 )=> 0inf <* [0] <{{D}} U 0 *> w.
Proof. unfold U. cexec. Qed.

Lemma ctraverse_left_Rot_one' p l r :
  l <* Rot p <* [1;0] <{{D}} r =( p + 6 )=>
  l <* [1;0] <{{D}} [0] *> [1]^^(p+2) *> [0] *> r.
Proof.
  eapply cmul_trans_eq.
  - unfold Rot.
    repeat rewrite Str_app_assoc.
    apply (csection_D1_0 p (l <* [1;1;0]) r).
  - eapply cmul_trans_eq.
    + apply csection_D1_1_left.
    + apply cmul_refl'; reflexivity.
    + reflexivity.
  - lia.
Qed.

Lemma ctraverse_left_Rot_gen p k l r :
  l <* (Rot p)^^(S k) <* [1;0] <{{D}} r =( S k * (p + 6) )=>
  l <* [1;0] <{{D}} [0] *> (U p)^^k *> [1]^^(p+2) *> [0] *> r.
Proof.
  gen l r.
  induction k as [|k IH]; intros l r.
  - cbn [lpow]. rewrite app_nil_r.
    eapply cmul_trans_eq.
    + apply ctraverse_left_Rot_one'.
    + apply cmul_refl'; [reflexivity|].
      cbn [lpow Str_app]. reflexivity.
    + lia.
  - replace ((Rot p)^^(S (S k))) with (Rot p ++ (Rot p)^^(S k))
      by reflexivity.
    rewrite Str_app_assoc.
    eapply cmul_trans_eq.
    + apply ctraverse_left_Rot_one'.
    + eapply cmul_trans_eq.
      * apply (IH l ([0] *> [1]^^(p+2) *> [0] *> r)).
      * apply cmul_refl'; [reflexivity|].
        rewrite U_split, lpow_shift'.
        replace ((U p)^^(S k)) with (U p ++ (U p)^^k) by reflexivity.
        rewrite Str_app_assoc.
        reflexivity.
      * reflexivity.
    + lia.
Qed.

Lemma cclose_left a w :
  0inf <* (Rot 0)^^(S a) <* [1;0] <{{D}} [0] *> w =( 6*a + 9 )=>
  0inf <* [0] <{{D}} (U 0)^^(S (S a)) *> w.
Proof.
  eapply cmul_trans_eq.
  - apply (ctraverse_left_Rot_gen 0 a 0inf ([0] *> w)).
  - eapply cmul_trans_eq.
    + rewrite (U_split 0).
      apply cleft_edge_close.
    + apply cmul_refl'; [reflexivity|].
      rewrite lpow_shift'.
      repeat rewrite lpow_cons_stream.
      reflexivity.
    + reflexivity.
  - lia.
Qed.

Lemma cclean_step a m w :
  0inf <* [0] <{{D}} (U 0)^^(S a) *> U 3 *> (U 1)^^m *> [1;1;1;0;1] *> w
  =( 41 + 10*a + 12*m )=>
  0inf <* [0] <{{D}} (U 0)^^(S (S a)) *> U 3 *> (U 1)^^m *> [1;1;1;0] *> w.
Proof.
  eapply cmul_trans_eq.
  - apply ctraverse_right_U.
  - eapply cmul_trans_eq.
    + apply ctraverse_right_U_one.
    + eapply cmul_trans_eq.
      * apply ctraverse_right_U.
      * eapply cmul_trans_eq.
        -- apply (csection_D0_11 1
             (0inf <* (V 0)^^(S a) <* V 3 <* (V 1)^^m) ([1] *> w)).
        -- eapply cmul_trans_eq.
           ++ rewrite V_fold, lpow_cons_stream.
              rewrite V_to_Rot_const0, V_to_Rot1, V_to_Rot.
              apply (ctraverse_left_Rot_gen 1 m
                       (0inf <* (Rot 0)^^(S a) <* Rot 3) w).
           ++ eapply cmul_trans_eq.
              ** apply (ctraverse_left_Rot_one' 3 (0inf <* (Rot 0)^^(S a))).
              ** eapply cmul_trans_eq.
                 --- rewrite (U_split 3).
                     change ([1]^^(1+2) *> [0] *> w) with ([1;1;1;0] *> w).
                     apply cclose_left.
                 --- apply cmul_refl'; reflexivity.
                 --- reflexivity.
              ** reflexivity.
           ++ reflexivity.
        -- reflexivity.
      * reflexivity.
    + reflexivity.
  - lia.
Qed.

Lemma cfour_step a m w :
  0inf <* [0] <{{D}} (U 0)^^(S a) *> (U 2)^^m *> [1;1;1;1;0;1] *> w
  =( 27 + 10*a + 14*m )=>
  0inf <* [0] <{{D}} (U 0)^^(S (S a)) *> (U 2)^^m *> [1;1;1;1;0] *> w.
Proof.
  eapply cmul_trans_eq.
  - apply ctraverse_right_U.
  - eapply cmul_trans_eq.
    + apply ctraverse_right_U.
    + eapply cmul_trans_eq.
      * apply (csection_D0_11 2
          (0inf <* (V 0)^^(S a) <* (V 2)^^m) ([1] *> w)).
      * eapply cmul_trans_eq.
        -- rewrite V_fold, lpow_cons_stream.
           rewrite V_to_Rot_const0, V_to_Rot.
           apply (ctraverse_left_Rot_gen 2 m (0inf <* (Rot 0)^^(S a)) w).
        -- eapply cmul_trans_eq.
           ++ change ([1]^^(2+2) *> [0] *> w) with ([1;1;1;1;0] *> w).
              apply cclose_left.
           ++ apply cmul_refl'; reflexivity.
           ++ reflexivity.
        -- reflexivity.
      * reflexivity.
    + reflexivity.
  - lia.
Qed.

Lemma cclean_round a m n s :
  0inf <* [0] <{{D}} P^^(S a) *> M5 *> T3^^m *> J3^^(2+n) *> s
  =( 153 + 30*a + 36*m )=>
  0inf <* [0] <{{D}} P^^(S (a+3)) *> M5 *> T3^^(S m) *> J3^^n *> s.
Proof.
  unfold P, M5, T3, J3.
  change ([1;1;1;0]^^(2+n) *> s)
    with ([1;1;1;0;1] *> ([1;1;0] *> [1;1;1;0]^^n *> s)).
  eapply cmul_trans_eq.
  - apply cclean_step.
  - change ([1;1;1;0] *> [1;1;0] *> [1;1;1;0]^^n *> s)
      with ([1;1;1;0;1] *> ([1;0] *> [1;1;1;0]^^n *> s)).
    eapply cmul_trans_eq.
    + apply cclean_step.
    + change ([1;1;1;0] *> [1;0] *> [1;1;1;0]^^n *> s)
        with ([1;1;1;0;1] *> ([0] *> [1;1;1;0]^^n *> s)).
      eapply cmul_trans_eq.
      * apply cclean_step.
      * apply cmul_refl'; [reflexivity|].
        change ([1;1;1;0] *> [0] *> [1;1;1;0]^^n *> s)
          with (U 1 *> [1;1;1;0]^^n *> s).
        rewrite lpow_shift', lpow_cons_stream.
        replace (S (a+3)) with (S (S (S (S a)))) by lia.
        reflexivity.
      * reflexivity.
    + reflexivity.
  - lia.
Qed.

Lemma cfour_round a m n s :
  0inf <* [0] <{{D}} P^^(S a) *> Q4^^m *> K4^^(2+n) *> s
  =( 168 + 40*a + 56*m )=>
  0inf <* [0] <{{D}} P^^(S (a+4)) *> Q4^^(S m) *> K4^^n *> s.
Proof.
  unfold P, Q4, K4.
  change ([1;1;1;1;0]^^(2+n) *> s)
    with ([1;1;1;1;0;1] *> ([1;1;1;0] *> [1;1;1;1;0]^^n *> s)).
  eapply cmul_trans_eq.
  - apply cfour_step.
  - change ([1;1;1;1;0] *> [1;1;1;0] *> [1;1;1;1;0]^^n *> s)
      with ([1;1;1;1;0;1] *> ([1;1;0] *> [1;1;1;1;0]^^n *> s)).
    eapply cmul_trans_eq.
    + apply cfour_step.
    + change ([1;1;1;1;0] *> [1;1;0] *> [1;1;1;1;0]^^n *> s)
        with ([1;1;1;1;0;1] *> ([1;0] *> [1;1;1;1;0]^^n *> s)).
      eapply cmul_trans_eq.
      * apply cfour_step.
      * change ([1;1;1;1;0] *> [1;0] *> [1;1;1;1;0]^^n *> s)
          with ([1;1;1;1;0;1] *> ([0] *> [1;1;1;1;0]^^n *> s)).
        eapply cmul_trans_eq.
        -- apply cfour_step.
        -- apply cmul_refl'; [reflexivity|].
           change ([1;1;1;1;0] *> [0] *> [1;1;1;1;0]^^n *> s)
             with (U 2 *> [1;1;1;1;0]^^n *> s).
           rewrite lpow_shift', lpow_cons_stream.
           replace (S (a+4)) with (S (S (S (S (S a))))) by lia.
           reflexivity.
        -- reflexivity.
      * reflexivity.
    + reflexivity.
  - lia.
Qed.

Lemma cclean_rounds r a m n s :
  0inf <* [0] <{{D}} P^^(S a) *> M5 *> T3^^m *> J3^^(2*r+n) *> s
  =( r * (153 + 30*a + 36*m) + 63 * (r * (r-1)) )=>
  0inf <* [0] <{{D}} P^^(S (a+3*r)) *> M5 *> T3^^(m+r) *> J3^^n *> s.
Proof.
  gen a m n.
  induction r as [|r IH]; intros a m n.
  - apply cmul_refl'; [lia|].
    replace (a+3*0) with a by lia.
    replace (m+0) with m by lia.
    replace (2*0+n) with n by lia.
    reflexivity.
  - replace (2 * S r + n) with (2 + (2*r+n)) by lia.
    eapply cmul_trans_eq.
    + apply cclean_round.
    + eapply cmul_trans_eq.
      * apply IH.
      * apply cmul_refl'; [reflexivity|].
        replace (a+3+3*r) with (a+3*S r) by lia.
        replace (S m + r) with (m + S r) by lia.
        reflexivity.
      * reflexivity.
    + nia.
Qed.

Lemma cfour_rounds r a m n s :
  0inf <* [0] <{{D}} P^^(S a) *> Q4^^m *> K4^^(2*r+n) *> s
  =( r * (168 + 40*a + 56*m) + 108 * (r * (r-1)) )=>
  0inf <* [0] <{{D}} P^^(S (a+4*r)) *> Q4^^(m+r) *> K4^^n *> s.
Proof.
  gen a m n.
  induction r as [|r IH]; intros a m n.
  - apply cmul_refl'; [lia|].
    replace (a+4*0) with a by lia.
    replace (m+0) with m by lia.
    replace (2*0+n) with n by lia.
    reflexivity.
  - replace (2 * S r + n) with (2 + (2*r+n)) by lia.
    eapply cmul_trans_eq.
    + apply cfour_round.
    + eapply cmul_trans_eq.
      * apply IH.
      * apply cmul_refl'; [reflexivity|].
        replace (a+4+4*r) with (a+4*S r) by lia.
        replace (S m + r) with (m + S r) by lia.
        reflexivity.
      * reflexivity.
    + nia.
Qed.

Lemma cblank_tape_start :
  c0 =( 4 )=> 0inf <* [0] <{{D}} [1;1;1] *> 0inf.
Proof. unfold c0. cexec. Qed.

Lemma chalts_at_D0_10 l r :
  halts_in tm (l <* [0] <{{D}} [1;0] *> r) 2.
Proof.
  exists (l <* [1;1] {{E}}> [0] *> r).
  split.
  - apply csection_D0_10.
  - constructor.
Qed.

Lemma op_section_sound z :
  is_halt z = false ->
  zconf z =( N.to_nat (snd (op_section z)) )=> zconf (fst (op_section z)).
Proof.
  destruct z as [[zl cur] zr].
  unfold is_halt, op_section, zconf, conf.
  destruct cur.
  - destruct (pop_bit zr) as [b0 r1] eqn:E0.
    pose proof (pop_bit_split zr b0 r1 E0) as D0.
    destruct b0.
    + destruct (pop_bit r1) as [b1 r2] eqn:E1.
      pose proof (pop_bit_split r1 b1 r2 E1) as D1.
      destruct b1; intros _.
      *         destruct (pop_ones zl) as [n l1] eqn:E2.
        destruct (pop_ones_split zl n l1 E2) as [D2 [rl D2h]].
        destruct (pop_bit l1) as [bz l2] eqn:E3.
        pose proof (pop_bit_split l1 bz l2 E3) as D3.
        assert (Hbz : bz = 0)
          by (rewrite D3 in D2h; injection D2h as Hb _; exact Hb).
        subst bz.
        destruct (pop_bit l2) as [cur2 l3] eqn:E4.
        pose proof (pop_bit_split l2 cur2 l3 E4) as D4.
        cbn [fst snd].
        rewrite D0, D1, D2, D3, D4.
        rewrite push_run_decode.
        replace (N.to_nat (n + 4)) with (N.to_nat n + 4)%nat by lia.
        pose proof (csection_D0_00 (N.to_nat n)
                     (cur2 >> decodeS l3) (decodeS r2)) as H.
        applys_eq H; first [lia | reflexivity].
      *         destruct (pop_ones r2) as [m r3] eqn:E2.
        destruct (pop_ones_split r2 m r3 E2) as [D2 [rr D2h]].
        destruct (pop_bit r3) as [bz r4] eqn:E3.
        pose proof (pop_bit_split r3 bz r4 E3) as D3.
        assert (Hbz : bz = 0)
          by (rewrite D3 in D2h; injection D2h as Hb _; exact Hb).
        subst bz.
        destruct (pop_bit r4) as [cur2 r5] eqn:E4.
        pose proof (pop_bit_split r4 cur2 r5 E4) as D4.
        cbn [fst snd].
        rewrite D0, D1, D2, D3, D4.
        rewrite push_run_decode, push_run_decode.
        replace (N.to_nat 1) with 1%nat by reflexivity.
        cbn [lpow]. rewrite app_nil_r.
        replace (N.to_nat (m + 3)) with (N.to_nat m + 3)%nat by lia.
        pose proof (csection_D0_01 (N.to_nat m)
                     (decodeS zl) (cur2 >> decodeS r5)) as H.
        applys_eq H; first [lia | reflexivity].
    + destruct (pop_bit r1) as [b1 r2] eqn:E1.
      pose proof (pop_bit_split r1 b1 r2 E1) as D1.
      destruct b1.
      * intros H. discriminate.
      * intros _.
        destruct (pop_ones r2) as [m r3] eqn:E2.
        destruct (pop_ones_split r2 m r3 E2) as [D2 [rr D2h]].
        destruct (pop_bit r3) as [bz r4] eqn:E3.
        pose proof (pop_bit_split r3 bz r4 E3) as D3.
        assert (Hbz : bz = 0)
          by (rewrite D3 in D2h; injection D2h as Hb _; exact Hb).
        subst bz.
        destruct (pop_bit r4) as [cur2 r5] eqn:E4.
        pose proof (pop_bit_split r4 cur2 r5 E4) as D4.
        cbn [fst snd].
        rewrite D0, D1, D2, D3, D4.
        repeat rewrite push_run_decode.
        replace (N.to_nat 1) with 1%nat by reflexivity.
        replace (N.to_nat 2) with 2%nat by reflexivity.
        cbn [lpow]. repeat rewrite app_nil_r.
        pose proof (csection_D0_11 (N.to_nat m)
                     (decodeS zl) (cur2 >> decodeS r5)) as H.
        applys_eq H; first [lia | reflexivity].
  - intros _.
    destruct (pop_bit zl) as [l0 l1s] eqn:E0.
    pose proof (pop_bit_split zl l0 l1s E0) as D0.
    destruct l0.
    + destruct (pop_ones l1s) as [m l2] eqn:E2.
      destruct (pop_ones_split l1s m l2 E2) as [D2 [rl D2h]].
      destruct (pop_bit l2) as [bz l3] eqn:E3.
      pose proof (pop_bit_split l2 bz l3 E3) as D3.
      assert (Hbz : bz = 0)
        by (rewrite D3 in D2h; injection D2h as Hb _; exact Hb).
      subst bz.
      destruct (pop_bit l3) as [cur2 l4] eqn:E4.
      pose proof (pop_bit_split l3 cur2 l4 E4) as D4.
      cbn [fst snd].
      rewrite D0, D2, D3, D4.
      repeat rewrite push_run_decode.
      replace (N.to_nat 1) with 1%nat by reflexivity.
      cbn [lpow]. rewrite app_nil_r.
      replace (N.to_nat (m + 2)) with (N.to_nat m + 2)%nat by lia.
      pose proof (csection_D1_0 (N.to_nat m)
                   (cur2 >> decodeS l4) (decodeS zr)) as H.
      applys_eq H; first [lia | reflexivity].
    + destruct (pop_bit l1s) as [l1b l2s] eqn:E1.
      pose proof (pop_bit_split l1s l1b l2s E1) as D1.
      destruct l1b.
      * cbn [fst snd].
        rewrite D0, D1.
        repeat rewrite push_run_decode.
        replace (N.to_nat 1) with 1%nat by reflexivity.
        cbn [lpow]. repeat rewrite app_nil_r.
        pose proof (csection_D1_1_left (decodeS l2s) (decodeS zr)) as H.
        applys_eq H; reflexivity.
      * destruct (pop_bit zr) as [cur2 r2] eqn:E2.
        pose proof (pop_bit_split zr cur2 r2 E2) as D2.
        cbn [fst snd].
        repeat rewrite push_run_decode.
        rewrite D0, D1, D2.
        replace (N.to_nat 1) with 1%nat by reflexivity.
        cbn [lpow]. repeat rewrite app_nil_r.
        pose proof (csection_D1_1_right (decodeS l2s) (cur2 >> decodeS r2)) as H.
        applys_eq H; reflexivity.
Qed.

Lemma some_pair_inv {A B} (a a' : A) (b b' : B) :
  Some (a, b) = Some (a', b') -> a' = a /\ b' = b.
Proof. intros E. injection E. auto. Qed.

Lemma some_triple_inv {A B C} (a a' : A) (b b' : B) (c c' : C) :
  Some (a, b, c) = Some (a', b', c') -> a' = a /\ b' = b /\ c' = c.
Proof. intros E. injection E. auto. Qed.

Lemma upat_spec w p : upat w = Some p -> w = U p.
Proof.
  unfold upat.
  destruct (ones_prefix w) as [a r] eqn:E.
  pose proof (ones_prefix_split w) as Hw.
  rewrite E in Hw. cbn [fst snd] in Hw.
  destruct r as [|[] [|[] [|z r]]]; try discriminate;
    destruct a as [|[|q]]; try discriminate.
  intros H. injection H as <-.
  rewrite Hw.
  unfold U.
  change ([1]^^(S (S q))) with ([1] ++ [1]^^(S q)).
  change ([1]^^(S q)) with ([1] ++ [1]^^q).
  cbn [app].
  reflexivity.
Qed.

Lemma vpat_spec w p : vpat w = Some p -> w = V p.
Proof.
  unfold vpat.
  destruct w as [|x rest]; try discriminate.
  destruct x; try discriminate.
  destruct (ones_prefix rest) as [q r] eqn:E.
  pose proof (ones_prefix_split rest) as Hr.
  rewrite E in Hr. cbn [fst snd] in Hr.
  destruct (word_eqb r [0;1;1]) eqn:Er; try discriminate.
  apply word_eqb_spec in Er. subst r.
  intros H. injection H as <-.
  rewrite Hr.
  unfold V.
  reflexivity.
Qed.

Lemma pop_bits_expect_sound bits s s' :
  pop_bits_expect bits s = Some s' ->
  decodeS s = bits *> decodeS s'.
Proof.
  gen s.
  induction bits as [|b bits IH]; intros s.
  - cbn. intros H. injection H as <-. reflexivity.
  - cbn [pop_bits_expect].
    destruct (pop_bit s) as [b' s2] eqn:E.
    pose proof (pop_bit_split s b' s2 E) as D.
    destruct (sym_eqb b b') eqn:Eb; [|discriminate].
    apply sym_eqb_spec in Eb. subst b'.
    intros H.
    rewrite D, (IH s2 H).
    reflexivity.
Qed.

Lemma div1 (k : N) : (k / 1)%N = k.
Proof. apply N.div_1_r. Qed.

Lemma mod1 (k : N) : (k mod 1)%N = 0%N.
Proof. apply N.mod_1_r. Qed.

Lemma k_split (k : N) :
  N.to_nat k = (2 * N.to_nat (k / 2) + N.to_nat (k mod 2))%nat.
Proof.
  rewrite (N.div_mod k 2) at 1 by lia.
  rewrite N2Nat.inj_add, N2Nat.inj_mul.
  reflexivity.
Qed.

Lemma x2_pow (j : nat) (X : Stream Sym) :
  ([0;1;1] : list Sym)^^(2*j) *> X = ([0;1;1;0;1;1] : list Sym)^^j *> X.
Proof.
  replace (2*j) with (j*2) by lia.
  rewrite lpow_mul.
  change ([0;1;1]^^2) with ([0;1;1;0;1;1] : list Sym).
  reflexivity.
Qed.

Lemma x2_rotate (j : nat) (X : Stream Sym) :
  ([0;1;1;0;1;1] : list Sym)^^j *> [0] *> X =
  [0] *> ([1;1;0;1;1;0] : list Sym)^^j *> X.
Proof.
  change ([0;1;1;0;1;1] : list Sym) with ([0] ++ [1;1;0;1;1]).
  change ([1;1;0;1;1;0] : list Sym) with ([1;1;0;1;1] ++ [0]).
  apply lpow_rotate'.
Qed.

Lemma op_bulkR_sound z z' c :
  op_bulkR z = Some (z', c) -> zconf z =( N.to_nat c )=> zconf z'.
Proof.
  destruct z as [[zl cur] zr].
  unfold op_bulkR.
  destruct cur; [|discriminate].
  destruct zr as [|[w k] t]; [discriminate|].
  destruct (upat w) as [p|] eqn:Eu; [|discriminate].
  apply upat_spec in Eu. subst w.
  intros H.
  destruct (some_pair_inv _ _ _ _ H) as [Ez Ec].
  rewrite Ez, Ec.
  unfold zconf, conf.
  rewrite push_sound. cbn [fst snd decodeS].
  pose proof (ctraverse_right_U p (N.to_nat k) (decodeS zl) (decodeS t)) as HC.
  applys_eq HC.
  repeat f_equal; lia.
Qed.

Lemma cbulkL_stream p k (L R : Stream Sym) :
  (1 >> (V p)^^k *> 0 >> L) <{{D}} (0 >> R) =( k * (p + 6) )=>
  (1 >> 0 >> L) <{{D}} (0 >> (U p)^^k *> R).
Proof.
  pose proof (V_to_Rot p k L) as Hr.
  pose proof (ctraverse_left_Rot p k L R) as H.
  applys_eq H; try reflexivity.
  rewrite Hr. reflexivity.
Qed.

Lemma op_bulkL_sound z z' c :
  op_bulkL z = Some (z', c) -> zconf z =( N.to_nat c )=> zconf z'.
Proof.
  destruct z as [[zl cur] zr].
  unfold op_bulkL.
  destruct cur; [discriminate|].
  destruct zl as [|[w k] rest]; [discriminate|].
  destruct (vpat w) as [p|] eqn:Ev; [|discriminate].
  apply vpat_spec in Ev. subst w.
  destruct (pop_bit rest) as [b rest'] eqn:E1.
  pose proof (pop_bit_split rest b rest' E1) as D1.
  destruct b; [|discriminate].
  destruct (pop_bit zr) as [b2 zr'] eqn:E2.
  pose proof (pop_bit_split zr b2 zr' E2) as D2.
  destruct b2; [|discriminate].
  intros H.
  destruct (some_pair_inv _ _ _ _ H) as [Ez Ec].
  rewrite Ez, Ec.
  unfold zconf, conf.
  cbn [decodeS].
  repeat rewrite push_sound. cbn [fst snd].
  replace (N.to_nat 1) with 1%nat by reflexivity.
  cbn [lpow]. repeat rewrite app_nil_r.
  rewrite D1, D2.
  pose proof (cbulkL_stream p (N.to_nat k) (decodeS rest') (decodeS zr')) as HC.
  applys_eq HC.
  repeat f_equal; lia.
Qed.

Lemma op_shiftA_sound zl zr zl' zr' c :
  op_shiftA zl zr = Some (zl', zr', c) ->
  (1 >> decodeS zl) <{{D}} decodeS zr =( N.to_nat c )=>
  (1 >> decodeS zl') <{{D}} decodeS zr'.
Proof.
  unfold op_shiftA, shift_apply.
  destruct (pop_bits_expect MIDA_B zl) as [sA|] eqn:EA; [|discriminate].
  apply pop_bits_expect_sound in EA.
  destruct sA as [|[w k] t]; [discriminate|].
  destruct (word_eqb w (V 0)) eqn:Ew; [|discriminate].
  apply word_eqb_spec in Ew; subst w.
  rewrite div1, mod1.
  cbn [andb].
  destruct (1 <=? k)%N eqn:Ek; [|discriminate].
  intros H.
  destruct (some_triple_inv _ _ _ _ _ _ H) as [E1 [E2 E3]].
  rewrite E1, E2, E3, EA.
  rewrite push_bits_sound, push_sound, push_sound.
  cbn [fst snd decodeS N.to_nat lpow Str_app].
  pose proof (cbridgeA (N.to_nat k) (decodeS t) (decodeS zr)) as HB.
  applys_eq HB; try reflexivity.
  lia.
Qed.

Lemma op_shiftB_sound zl zr zl' zr' c :
  op_shiftB zl zr = Some (zl', zr', c) ->
  (1 >> decodeS zl) <{{D}} decodeS zr =( N.to_nat c )=>
  (1 >> decodeS zl') <{{D}} decodeS zr'.
Proof.
  unfold op_shiftB, shift_apply.
  destruct (pop_bits_expect MIDB_B zl) as [sB|] eqn:EB; [|discriminate].
  apply pop_bits_expect_sound in EB.
  destruct sB as [|[w k] t]; [discriminate|].
  destruct (word_eqb w (V 1)) eqn:Ew; [|discriminate].
  apply word_eqb_spec in Ew; subst w.
  rewrite div1, mod1.
  cbn [andb].
  destruct (1 <=? k)%N eqn:Ek; [|discriminate].
  intros H.
  destruct (some_triple_inv _ _ _ _ _ _ H) as [E1 [E2 E3]].
  rewrite E1, E2, E3, EB.
  rewrite push_bits_sound, push_sound, push_sound.
  cbn [fst snd decodeS N.to_nat lpow Str_app].
  pose proof (cbridgeB (N.to_nat k) (decodeS t) (decodeS zr)) as HB.
  applys_eq HB; try reflexivity.
  lia.
Qed.

Lemma cshiftQ_stream (j : nat) (Z R : Stream Sym) :
  (1 >> 1 >> ([0;1;1] : list Sym)^^(2*j) *> 0 >> Z) <{{D}} R =( j * 8 )=>
  (1 >> 1 >> 0 >> Z) <{{D}} Q4^^j *> R.
Proof.
  pose proof (cshiftQ_bulk j Z R) as H.
  applys_eq H; try reflexivity.
  change (0 >> Z) with ([0] *> Z).
  rewrite x2_pow, x2_rotate.
  reflexivity.
Qed.

Lemma op_shiftQ_sound zl zr zl' zr' c :
  op_shiftQ zl zr = Some (zl', zr', c) ->
  (1 >> decodeS zl) <{{D}} decodeS zr =( N.to_nat c )=>
  (1 >> decodeS zl') <{{D}} decodeS zr'.
Proof.
  unfold op_shiftQ, shift_apply.
  destruct (pop_bits_expect [1] zl) as [sQ|] eqn:EQ; [|discriminate].
  apply pop_bits_expect_sound in EQ.
  destruct sQ as [|[w k] t]; [discriminate|].
  destruct (word_eqb w [0;1;1]) eqn:Ew; [|discriminate].
  apply word_eqb_spec in Ew; subst w.
  cbn [andb]. cbv beta zeta iota.
  destruct (N.eqb (k mod 2) 0) eqn:Erem.
  - destruct (pop_bit t) as [b t2] eqn:Et.
    pose proof (pop_bit_split t b t2 Et) as Dt.
    destruct b.
    + destruct (1 <=? k / 2)%N eqn:Ej; [|discriminate].
      intros H.
      destruct (some_triple_inv _ _ _ _ _ _ H) as [E1 [E2 E3]].
      apply N.eqb_eq in Erem.
      rewrite E1, E2, E3, EQ.
      rewrite push_bits_sound, push_sound, push_sound.
      cbn [fst snd].
      rewrite Erem.
      cbn [N.to_nat lpow Str_app].
      rewrite Dt.
      pose proof (cshiftQ_stream (N.to_nat (k / 2)) (decodeS t2) (decodeS zr))
        as HQ.
      pose proof (k_split k) as KS.
      rewrite Erem in KS. cbn [N.to_nat] in KS.
      applys_eq HQ.
      * lia.
      * cbn [decodeS].
        rewrite KS, Dt.
        rewrite PeanoNat.Nat.add_0_r.
        reflexivity.
    + destruct (1 <=? k / 2 - 1)%N eqn:Ej; [|discriminate].
      intros H.
      destruct (some_triple_inv _ _ _ _ _ _ H) as [E1 [E2 E3]].
      apply N.eqb_eq in Erem.
      apply N.leb_le in Ej.
      rewrite E1, E2, E3, EQ.
      rewrite push_bits_sound, push_sound, push_sound.
      cbn [fst snd].
      replace (N.to_nat 2) with 2%nat by reflexivity.
      pose proof (cshiftQ_stream (N.to_nat (k / 2 - 1))
                    ([1;1] *> ([0;1;1] : list Sym)^^1 *> decodeS t)
                    (decodeS zr)) as HQ.
      pose proof (k_split k) as KS.
      rewrite Erem in KS. cbn [N.to_nat] in KS.
      rewrite N2Nat.inj_sub in HQ.
      replace (N.to_nat 1) with 1%nat in HQ by reflexivity.
      replace (N.to_nat (k / 2 - 1)) with (N.to_nat (k / 2) - 1)%nat
        by (rewrite N2Nat.inj_sub; reflexivity).
      applys_eq HQ.
      * lia.
      * cbn [decodeS].
        rewrite KS.
        replace (2 * N.to_nat (k / 2) + 0)%nat
          with (2 * (N.to_nat (k / 2) - 1) + 2)%nat by lia.
        rewrite <- lpow_add'.
        cbn [lpow Str_app app].
        reflexivity.
  - destruct (1 <=? k / 2)%N eqn:Ej; [|discriminate].
    intros H.
    destruct (some_triple_inv _ _ _ _ _ _ H) as [E1 [E2 E3]].
    apply N.eqb_neq in Erem.
    pose proof (N.mod_upper_bound k 2 ltac:(lia)) as Hub.
    assert (Hrem : (k mod 2)%N = 1%N) by lia.
    rewrite E1, E2, E3, EQ.
    rewrite push_bits_sound, push_sound, push_sound.
    cbn [fst snd].
    rewrite Hrem.
    replace (N.to_nat 1) with 1%nat by reflexivity.
    pose proof (cshiftQ_stream (N.to_nat (k / 2))
                  ([1;1] *> decodeS t) (decodeS zr)) as HQ.
    pose proof (k_split k) as KS.
    rewrite Hrem in KS. cbn [N.to_nat] in KS.
    applys_eq HQ.
    + lia.
    + cbn [decodeS].
      rewrite KS.
      rewrite <- lpow_add'.
      cbn [lpow Str_app app].
      reflexivity.
Qed.

Lemma op_shift_sound z z' c :
  op_shift z = Some (z', c) -> zconf z =( N.to_nat c )=> zconf z'.
Proof.
  destruct z as [[zl cur] zr].
  unfold op_shift.
  destruct cur; [discriminate|].
  destruct (op_shiftA zl zr) as [[[zl2 zr2] c2]|] eqn:EA.
  { intros H.
    destruct (some_pair_inv _ _ _ _ H) as [Ez Ec].
    rewrite Ez, Ec.
    apply (op_shiftA_sound zl zr zl2 zr2 c2 EA). }
  destruct (op_shiftB zl zr) as [[[zl2 zr2] c2]|] eqn:EB.
  { intros H.
    destruct (some_pair_inv _ _ _ _ H) as [Ez Ec].
    rewrite Ez, Ec.
    apply (op_shiftB_sound zl zr zl2 zr2 c2 EB). }
  destruct (op_shiftQ zl zr) as [[[zl2 zr2] c2]|] eqn:EQ; [|discriminate].
  intros H.
  destruct (some_pair_inv _ _ _ _ H) as [Ez Ec].
  rewrite Ez, Ec.
  apply (op_shiftQ_sound zl zr zl2 zr2 c2 EQ).
Qed.

Lemma conf_leftedge (zr : side) :
  conf [] S0 zr = (0inf <* [0] <{{D}} decodeS zr).
Proof. reflexivity. Qed.

Lemma op_clean_sound z z' c :
  op_clean z = Some (z', c) -> zconf z =( N.to_nat c )=> zconf z'.
Proof.
  destruct z as [[zl cur] zr].
  unfold op_clean.
  destruct zl as [|? ?]; [|discriminate].
  destruct cur; [|discriminate].
  destruct zr as [|[w1 a] [|[w2 k2] rest]]; try discriminate.
  destruct (word_eqb w1 P) eqn:E1; [|discriminate].
  destruct (word_eqb w2 M5) eqn:E2; cbn [andb]; [|discriminate].
  destruct (N.eqb k2 1) eqn:E3; cbn [andb]; [|discriminate].
  destruct (N.leb 1 a) eqn:E4; cbn [andb]; [|discriminate].
  apply word_eqb_spec in E1; subst w1.
  apply word_eqb_spec in E2; subst w2.
  apply N.eqb_eq in E3; subst k2.
  apply N.leb_le in E4.
  cbv beta zeta.
  assert (CORE : forall (m : N) (rest2 : side) (out : zstate * N),
      match rest2 with
      | (w4, k) :: rest3 =>
        if andb (word_eqb w4 J3) (N.leb 2 k) then
          Some (([] : side, S0,
                push (P, (a + 3*(k/2))%N)
                  (push (M5, 1%N)
                    (push (T3, (m + k/2)%N)
                      (push (J3, (k mod 2)%N) rest3)))),
                ((k/2) * (123 + 30*a + 36*m) + 63 * ((k/2) * (k/2-1)))%N)
        else None
      | [] => None
      end = Some out ->
      conf [] S0 (((P, a) :: (M5, 1%N) :: (T3, m) :: rest2)) =(
        N.to_nat (snd out) )=>
      zconf (fst out)).
  { intros m rest2 out.
    destruct rest2 as [|[w4 k] rest3]; [discriminate|].
    destruct (word_eqb w4 J3) eqn:E5; cbn [andb]; [|discriminate].
    destruct (N.leb 2 k) eqn:E6; [|discriminate].
    apply word_eqb_spec in E5; subst w4.
    apply N.leb_le in E6.
    intros H.
    assert (Ez : fst out = ([] : side, S0,
                push (P, (a + 3*(k/2))%N)
                  (push (M5, 1%N)
                    (push (T3, (m + k/2)%N)
                      (push (J3, (k mod 2)%N) rest3))))) by
      (destruct out; cbn [fst]; congruence).
    assert (Ec : snd out =
      ((k/2) * (123 + 30*a + 36*m) + 63 * ((k/2) * (k/2-1)))%N) by
      (destruct out; cbn [snd]; congruence).
    rewrite Ez, Ec.
    unfold zconf.
    rewrite conf_leftedge, conf_leftedge.
    repeat rewrite push_sound. cbn [fst snd decodeS].
    destruct (N.to_nat a) as [|a'] eqn:Ea; [lia|].
    pose proof (cclean_rounds (N.to_nat (k/2)) a' (N.to_nat m)
                  (N.to_nat (k mod 2)) (decodeS rest3)) as HC.
    pose proof (k_split k) as KS.
    unfold P, M5, T3, J3 in *.
    applys_eq HC.
    - repeat rewrite ?N2Nat.inj_add, ?N2Nat.inj_mul, ?N2Nat.inj_sub;
        cbn [N.to_nat Pos.to_nat Pos.iter_op]; nia.
    - replace (N.to_nat 1) with 1%nat by reflexivity.
      cbn [lpow]. rewrite app_nil_r.
      rewrite KS. reflexivity.
    - repeat f_equal;
        repeat rewrite ?N2Nat.inj_add, ?N2Nat.inj_mul;
        cbn [N.to_nat Pos.to_nat Pos.iter_op]; lia.
  }
  destruct rest as [|[w3 m] rest2].
  - intros H. discriminate.
  - destruct (word_eqb w3 T3) eqn:E5.
    + apply word_eqb_spec in E5; subst w3.
      intros H.
      apply (CORE m rest2 (z', c) H).
    + intros H.
      specialize (CORE 0%N ((w3, m) :: rest2) (z', c) H).
      assert (EC : conf [] S0 ((P, a) :: (M5, 1%N) :: (w3, m) :: rest2) =
                   conf [] S0
                     ((P, a) :: (M5, 1%N) :: (T3, 0%N) :: (w3, m) :: rest2)).
      { rewrite conf_leftedge, conf_leftedge.
        cbn [decodeS].
        replace (N.to_nat 0) with O by reflexivity.
        cbn [lpow Str_app].
        reflexivity. }
      change (zconf ([], S0, (P, a) :: (M5, 1%N) :: (w3, m) :: rest2))
        with (conf [] S0 ((P, a) :: (M5, 1%N) :: (w3, m) :: rest2)).
      rewrite EC.
      exact CORE.
Qed.

Lemma op_four_sound z z' c :
  op_four z = Some (z', c) -> zconf z =( N.to_nat c )=> zconf z'.
Proof.
  destruct z as [[zl cur] zr].
  unfold op_four.
  destruct zl as [|? ?]; [|discriminate].
  destruct cur; [|discriminate].
  destruct zr as [|[w1 a] [|[w2 m] [|[w3 k] rest]]]; try discriminate.
  destruct (word_eqb w1 P) eqn:E1; [|discriminate].
  destruct (word_eqb w2 Q4) eqn:E2; cbn [andb]; [|discriminate].
  destruct (word_eqb w3 K4) eqn:E3; cbn [andb]; [|discriminate].
  destruct (N.leb 1 a) eqn:E4; cbn [andb]; [|discriminate].
  destruct (N.leb 1 m) eqn:E5; cbn [andb]; [|discriminate].
  destruct (N.leb 2 k) eqn:E6; [|discriminate].
  apply word_eqb_spec in E1; subst w1.
  apply word_eqb_spec in E2; subst w2.
  apply word_eqb_spec in E3; subst w3.
  apply N.leb_le in E4.
  apply N.leb_le in E5.
  apply N.leb_le in E6.
  cbv beta zeta.
  intros H.
  assert (Ez : z' = ([] : side, S0,
            push (P, (a + 4*(k/2))%N)
              (push (Q4, (m + k/2)%N)
                (push (K4, (k mod 2)%N) rest)))) by congruence.
  assert (Ec : c = ((k/2) * (128 + 40*a + 56*m) + 108 * ((k/2) * (k/2-1)))%N)
    by congruence.
  rewrite Ez, Ec.
  unfold zconf.
  rewrite conf_leftedge, conf_leftedge.
  repeat rewrite push_sound. cbn [fst snd decodeS].
  destruct (N.to_nat a) as [|a'] eqn:Ea; [lia|].
  destruct (N.to_nat m) as [|m'] eqn:Em; [lia|].
  pose proof (cfour_rounds (N.to_nat (k/2)) a' (S m')
                (N.to_nat (k mod 2)) (decodeS rest)) as HF.
  pose proof (k_split k) as KS.
  unfold P, Q4, K4 in *.
  applys_eq HF.
  - repeat rewrite ?N2Nat.inj_add, ?N2Nat.inj_mul, ?N2Nat.inj_sub;
      cbn [N.to_nat Pos.to_nat Pos.iter_op]; nia.
  - rewrite KS. reflexivity.
  - repeat f_equal;
      repeat rewrite ?N2Nat.inj_add, ?N2Nat.inj_mul;
      cbn [N.to_nat Pos.to_nat Pos.iter_op]; lia.
Qed.

Lemma is_halt_sound z :
  is_halt z = true -> halts_in tm (zconf z) 2.
Proof.
  destruct z as [[zl cur] zr].
  unfold is_halt.
  destruct cur; [|discriminate].
  destruct (pop_bit zr) as [b0 r1] eqn:E0.
  pose proof (pop_bit_split zr b0 r1 E0) as D0.
  destruct b0; [discriminate|].
  destruct (pop_bit r1) as [b1 r2] eqn:E1.
  pose proof (pop_bit_split r1 b1 r2 E1) as D1.
  destruct b1; [|discriminate].
  intros _.
  unfold zconf, conf.
  rewrite D0, D1.
  apply (chalts_at_D0_10 (decodeS zl) (decodeS r2)).
Qed.

Definition dstream (s : side) (rest : Stream Sym) : Stream Sym :=
  fold_right (fun c X => (fst c)^^(N.to_nat (snd c)) *> X) rest s.

Lemma dstream_cons w k t rest :
  dstream ((w,k) :: t) rest = w^^(N.to_nat k) *> dstream t rest.
Proof. reflexivity. Qed.

Lemma dstream_decode s : decodeS s = dstream s (const 0).
Proof.
  induction s as [|[w k] t IH]; cbn [decodeS]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma dstream_app s1 s2 rest :
  dstream (s1 ++ s2) rest = dstream s1 (dstream s2 rest).
Proof.
  induction s1 as [|[w k] t IH]; cbn [app]; [reflexivity|].
  rewrite dstream_cons, dstream_cons, IH. reflexivity.
Qed.

Lemma push_dstream c s rest :
  dstream (push c s) rest = (fst c)^^(N.to_nat (snd c)) *> dstream s rest.
Proof.
  destruct c as [w k].
  cbn [fst snd].
  destruct k as [|p].
  - cbn [push N.to_nat lpow Str_app]. reflexivity.
  - destruct s as [|[w' k'] t].
    + reflexivity.
    + cbn [push].
      destruct (word_eqb w w') eqn:Ew.
      * apply word_eqb_spec in Ew. subst w'.
        rewrite dstream_cons, dstream_cons.
        rewrite N2Nat.inj_add, <- lpow_add'.
        reflexivity.
      * reflexivity.
Qed.

Lemma prim_root_spec w :
  w = (fst (prim_root w))^^(snd (prim_root w)).
Proof.
  unfold prim_root.
  set (cands := List.seq 1 (List.length w)).
  assert (HC : forall d, In d cands -> (1 <= d)%nat).
  { subst cands. intros d Hd. apply in_seq in Hd. lia. }
  clearbody cands.
  induction cands as [|d cs IH]; cbn [first_true].
  -     destruct w as [|a w'].
    + reflexivity.
    + cbn [fst snd].
      rewrite List.firstn_all2 by lia.
      rewrite PeanoNat.Nat.div_same by (cbn [List.length]; lia).
      cbn [lpow]. rewrite app_nil_r. reflexivity.
  - destruct (andb (Nat.eqb (Nat.modulo (List.length w) d) 0)
              (word_eqb w (List.firstn d w ^^ (Nat.div (List.length w) d))))
      eqn:Eg.
    + apply Bool.andb_true_iff in Eg.
      destruct Eg as [_ E2].
      apply word_eqb_spec in E2.
      cbn [fst snd].
      exact E2.
    + apply IH. intros e He. apply HC. right. exact He.
Qed.

Lemma merge_pass_dstream s rest :
  dstream (merge_pass s) rest = dstream s rest.
Proof.
  gen rest.
  induction s as [|[w k] t IH]; intros rest; [reflexivity|].
  cbn [merge_pass].
  destruct (prim_root w) as [u d] eqn:E.
  pose proof (prim_root_spec w) as Hw.
  rewrite E in Hw. cbn [fst snd] in Hw.
  rewrite push_dstream. cbn [fst snd].
  rewrite IH.
  rewrite dstream_cons.
  rewrite Hw.
  rewrite N2Nat.inj_mul, Nat2N.id.
  replace (d * N.to_nat k)%nat with (N.to_nat k * d)%nat by lia.
  rewrite lpow_mul.
  reflexivity.
Qed.

Lemma pairw_flat (a b : nat) (X : Stream Sym) :
  pairw a b *> X = [1]^^a *> [0]^^b *> X.
Proof. unfold pairw. rewrite Str_app_assoc. reflexivity. Qed.

Lemma pair_guard_spec c1 c2 :
  pair_guard c1 c2 = true ->
  c1 = ([S1], snd c1) /\ c2 = ([S0], snd c2).
Proof.
  destruct c1 as [w1 a], c2 as [w2 b].
  unfold pair_guard.
  destruct w1 as [|x [|? ?]]; try discriminate;
    destruct x; try discriminate;
    destruct w2 as [|y [|? ?]]; try discriminate;
    destruct y; try discriminate.
  cbn [snd]. auto.
Qed.

Lemma pair_pass_dstream s rest :
  dstream (pair_pass s) rest = dstream s rest.
Proof.
  revert rest.
  induction s as [s IH] using (induction_ltof1 _ (@List.length chunk));
    intros rest.
  destruct s as [|c1 t1]; [reflexivity|].
  cbn [pair_pass].
  destruct t1 as [|c2 t2]; [reflexivity|].
  destruct (pair_guard c1 c2) eqn:G.
  - destruct (pair_guard_spec c1 c2 G) as [E1 E2].
    destruct c1 as [w1 a], c2 as [w2 b].
    cbn [snd] in E1, E2.
    assert (Ew1 : w1 = [S1]) by congruence.
    assert (Ew2 : w2 = [S0]) by congruence.
    subst w1 w2.
    unfold mk_pair. cbn [fst snd].
    rewrite !dstream_cons.
    rewrite (IH t2) by (unfold ltof; cbn [List.length]; lia).
    replace (N.to_nat 1) with 1%nat by reflexivity.
    cbn [lpow]. rewrite app_nil_r.
    rewrite pairw_flat.
    reflexivity.
  - destruct c1 as [w1 a1].
    rewrite !dstream_cons.
    rewrite (IH (c2 :: t2)) by (unfold ltof; cbn [List.length]; lia).
    destruct c2 as [w2 b2].
    rewrite !dstream_cons.
    reflexivity.
Qed.

Lemma vform_guard_spec c1 c2 c3 c4 :
  vform_guard c1 c2 c3 c4 = true ->
  c1 = ([S0], 1%N) /\ c2 = ([S1], snd c2) /\ c3 = ([S0], 1%N) /\
  c4 = ([S1], snd c4) /\ (2 <= snd c4)%N.
Proof.
  destruct c1 as [w1 a], c2 as [w2 b], c3 as [w3 c], c4 as [w4 d].
  destruct w1 as [|[|] [|? ?]]; try discriminate;
    destruct a as [|[a|a|]]; try discriminate;
    destruct w2 as [|[|] [|? ?]]; try discriminate;
    destruct w3 as [|[|] [|? ?]]; try discriminate;
    destruct c as [|[c|c|]]; try discriminate;
    destruct w4 as [|[|] [|? ?]]; try discriminate.
  cbn [snd].
  intros H.
  apply Bool.andb_true_iff in H.
  destruct H as [_ H2].
  apply N.leb_le in H2.
  auto 6.
Qed.

Lemma vform_pass_dstream s rest :
  dstream (vform_pass s) rest = dstream s rest.
Proof.
  revert rest.
  induction s as [s IH] using (induction_ltof1 _ (@List.length chunk));
    intros rest.
  destruct s as [|c1 t1]; [reflexivity|].
  cbn [vform_pass].
  destruct t1 as [|c2 [|c3 [|c4 t2]]];
    try (destruct c1 as [w1 a1];
         rewrite !dstream_cons;
         rewrite (IH _) by (unfold ltof; cbn [List.length]; lia);
         rewrite ?dstream_cons;
         repeat (match goal with
                 | c : chunk |- _ => destruct c as [? ?]
                 end; rewrite ?dstream_cons);
         reflexivity);
    try reflexivity.
  destruct (vform_guard c1 c2 c3 c4) eqn:G.
  - destruct (vform_guard_spec c1 c2 c3 c4 G) as [E1 [E2 [E3 [E4 Hr]]]].
    destruct c1 as [w1 a], c2 as [w2 m], c3 as [w3 c], c4 as [w4 r].
    cbn [snd] in *.
    assert (Ew1 : w1 = [S0]) by congruence.
    assert (Ea : a = 1%N) by congruence.
    assert (Ew2 : w2 = [S1]) by congruence.
    assert (Ew3 : w3 = [S0]) by congruence.
    assert (Ec : c = 1%N) by congruence.
    assert (Ew4 : w4 = [S1]) by congruence.
    subst w1 a w2 w3 c w4.
    rewrite !dstream_cons.
    rewrite push_dstream. cbn [fst snd].
    rewrite (IH t2) by (unfold ltof; cbn [List.length]; lia).
    replace (N.to_nat 1) with 1%nat by reflexivity.
    cbn [lpow]. rewrite !app_nil_r.
    (* V m *> 1^(r-2) *> T  =  0 *> 1^m *> 0 *> 1^r *> T *)
    unfold V.
    cbn [Str_app].
    rewrite !Str_app_assoc.
    cbn [Str_app].
    f_equal.
    replace (N.to_nat r) with (2 + N.to_nat (r - 2))%nat by lia.
    rewrite lpow_add.
    rewrite !Str_app_assoc.
    change ([1]^^2) with ([1;1] : list Sym).
    cbn [Str_app].
    reflexivity.
  - destruct c1 as [w1 a1], c2 as [w2 a2], c3 as [w3 a3], c4 as [w4 a4].
    rewrite !dstream_cons.
    rewrite (IH (_ :: _ :: _ :: t2))
      by (unfold ltof; cbn [List.length]; lia).
    rewrite !dstream_cons.
    reflexivity.
Qed.

Lemma runs_dstream (bits : list Sym) (X : Stream Sym) :
  dstream (runs bits) X = bits *> X.
Proof.
  induction bits as [|b bits IH]; [reflexivity|].
  cbn [runs].
  rewrite push_dstream. cbn [fst snd].
  rewrite IH.
  replace (N.to_nat 1) with 1%nat by reflexivity.
  cbn [lpow]. rewrite app_nil_r.
  reflexivity.
Qed.

Lemma decode_dstream_app (A B : side) :
  decodeS (A ++ B) = dstream A (decodeS B).
Proof.
  rewrite dstream_decode, dstream_app, <- dstream_decode.
  reflexivity.
Qed.

Lemma compress_right_sound s :
  decodeS (compress_right s) = decodeS s.
Proof.
  unfold compress_right.
  destruct (peel s) as [bits rest0] eqn:EP.
  pose proof (peel_sound s) as HP.
  rewrite EP in HP. cbn [fst snd] in HP.
  pose proof (absorb_fuel_sound 32 bits rest0) as HA.
  unfold absorb.
  destruct (absorb_fuel 32 bits rest0) as [bits2 rest] eqn:EA.
  rewrite decode_dstream_app.
  rewrite merge_pass_dstream, pair_pass_dstream, merge_pass_dstream,
    pair_pass_dstream, merge_pass_dstream.
  rewrite dstream_app.
  rewrite runs_dstream.
  rewrite <- decode_dstream_app.
  rewrite List.firstn_skipn.
  rewrite HP, HA.
  reflexivity.
Qed.

Lemma compress_left_sound s :
  decodeS (compress_left s) = decodeS s.
Proof.
  unfold compress_left.
  destruct (peel s) as [bits rest0] eqn:EP.
  pose proof (peel_sound s) as HP.
  rewrite EP in HP. cbn [fst snd] in HP.
  pose proof (absorb_fuel_sound 32 bits rest0) as HA.
  unfold absorb.
  destruct (absorb_fuel 32 bits rest0) as [bits2 rest] eqn:EA.
  rewrite decode_dstream_app.
  rewrite merge_pass_dstream, vform_pass_dstream, merge_pass_dstream,
    vform_pass_dstream, merge_pass_dstream.
  rewrite dstream_app.
  rewrite runs_dstream.
  rewrite <- decode_dstream_app.
  rewrite List.firstn_skipn.
  rewrite HP, HA.
  reflexivity.
Qed.

Lemma znorm_conf z : zconf (znorm z) = zconf z.
Proof.
  destruct z as [[zl cur] zr].
  unfold znorm, zconf, conf.
  rewrite compress_left_sound, compress_right_sound.
  reflexivity.
Qed.

Lemma zstep_sound_next z z' c :
  zstep z = Some (z', c) -> zconf z =( N.to_nat c )=> zconf z'.
Proof.
  unfold zstep.
  destruct (is_halt z) eqn:Eh; [discriminate|].
  intros H.
  destruct (some_pair_inv _ _ _ _ H) as [Ez Ec].
  rewrite Ez, Ec, znorm_conf.
  destruct (op_clean z) as [[z1 c1]|] eqn:E1.
  { cbn [fst snd]. apply (op_clean_sound z z1 c1 E1). }
  destruct (op_four z) as [[z1 c1]|] eqn:E2.
  { cbn [fst snd]. apply (op_four_sound z z1 c1 E2). }
  destruct (op_shift z) as [[z1 c1]|] eqn:E3.
  { cbn [fst snd]. apply (op_shift_sound z z1 c1 E3). }
  destruct (op_bulkR z) as [[z1 c1]|] eqn:E4.
  { cbn [fst snd]. apply (op_bulkR_sound z z1 c1 E4). }
  destruct (op_bulkL z) as [[z1 c1]|] eqn:E5.
  { cbn [fst snd]. apply (op_bulkL_sound z z1 c1 E5). }
  apply (op_section_sound z Eh).
Qed.

Lemma zstep_sound_halt z :
  zstep z = None -> halts_in tm (zconf z) 2.
Proof.
  unfold zstep.
  destruct (is_halt z) eqn:Eh.
  - intros _. apply (is_halt_sound z Eh).
  - destruct (match op_clean z with Some zc => zc | None =>
              match op_four z with Some zc => zc | None =>
              match op_shift z with Some zc => zc | None =>
              match op_bulkR z with Some zc => zc | None =>
              match op_bulkL z with Some zc => zc | None =>
              op_section z end end end end end) as [z1 c1].
    discriminate.
Qed.

Lemma chalts_in_trans (n m : nat) c c' :
  c =( n )=> c' ->
  halts_in tm c' m ->
  halts_in tm c (n + m).
Proof.
  intros H1 [ch [H2 H3]].
  exists ch.
  split; [eapply multistep_trans; eauto | exact H3].
Qed.

Lemma zrun_sound (p : positive) (z : zstate) (acc : N) :
  match zrun p z acc with
  | (Some z', acc') =>
      exists d : N, acc' = (acc + d)%N /\
      zconf z =( N.to_nat d )=> zconf z'
  | (None, acc') =>
      exists d : N, acc' = (acc + d)%N /\
      halts_in tm (zconf z) (N.to_nat d + 2)
  end.
Proof.
  gen z acc.
  induction p as [q IHq|q IHq|]; intros z acc; cbn [zrun].
  -     pose proof (IHq z acc) as H1.
    destruct (zrun q z acc) as [[z1|] acc1] eqn:E1.
    + destruct H1 as [d1 [Hd1 HS1]].
      pose proof (IHq z1 acc1) as H2.
      destruct (zrun q z1 acc1) as [[z2|] acc2] eqn:E2.
      * destruct H2 as [d2 [Hd2 HS2]].
        destruct (zstep z2) as [[z3 c]|] eqn:E3.
        -- exists (d1 + d2 + c)%N.
           split; [lia|].
           eapply cmul_trans_eq.
           ++ exact HS1.
           ++ eapply cmul_trans_eq.
              ** exact HS2.
              ** apply (zstep_sound_next z2 z3 c E3).
              ** reflexivity.
           ++ lia.
        -- exists (d1 + d2)%N.
           split; [lia|].
           replace (N.to_nat (d1 + d2) + 2)%nat
             with (N.to_nat d1 + (N.to_nat d2 + 2))%nat by lia.
           eapply chalts_in_trans; [exact HS1|].
           eapply chalts_in_trans; [exact HS2|].
           apply (zstep_sound_halt z2 E3).
      * destruct H2 as [d2 [Hd2 HH2]].
        exists (d1 + d2)%N.
        split; [lia|].
        replace (N.to_nat (d1 + d2) + 2)%nat
          with (N.to_nat d1 + (N.to_nat d2 + 2))%nat by lia.
        eapply chalts_in_trans; [exact HS1 | exact HH2].
    + destruct H1 as [d1 [Hd1 HH1]].
      exists d1. auto.
  -     pose proof (IHq z acc) as H1.
    destruct (zrun q z acc) as [[z1|] acc1] eqn:E1.
    + destruct H1 as [d1 [Hd1 HS1]].
      pose proof (IHq z1 acc1) as H2.
      destruct (zrun q z1 acc1) as [[z2|] acc2] eqn:E2.
      * destruct H2 as [d2 [Hd2 HS2]].
        exists (d1 + d2)%N.
        split; [lia|].
        eapply cmul_trans_eq; [exact HS1 | exact HS2 | lia].
      * destruct H2 as [d2 [Hd2 HH2]].
        exists (d1 + d2)%N.
        split; [lia|].
        replace (N.to_nat (d1 + d2) + 2)%nat
          with (N.to_nat d1 + (N.to_nat d2 + 2))%nat by lia.
        eapply chalts_in_trans; [exact HS1 | exact HH2].
    + destruct H1 as [d1 [Hd1 HH1]].
      exists d1. auto.
  -     destruct (zstep z) as [[z1 c]|] eqn:E1.
    + exists c.
      split; [lia|].
      apply (zstep_sound_next z z1 c E1).
    + exists 0%N.
      split; [lia|].
      cbn [N.to_nat].
      apply (zstep_sound_halt z E1).
Qed.

Lemma zinit_conf : c0 =( 4 )=> zconf zinit.
Proof.
  eapply cmul_trans_eq.
  - apply cblank_tape_start.
  - apply cmul_refl'; [reflexivity|].
    unfold zinit, zconf, conf.
    cbn [decodeS].
    replace (N.to_nat 3) with 3%nat by reflexivity.
    cbn [lpow Str_app].
    reflexivity.
  - reflexivity.
Qed.

Lemma multistep_split (n m : nat) (c c'' : Q * tape) :
  c =( n + m )=> c'' ->
  exists c', c =( n )=> c' /\ c' =( m )=> c''.
Proof.
  gen c.
  induction n as [|n IH]; intros c H.
  - exists c. split; [apply multistep_0 | exact H].
  - cbn [Nat.add] in H.
    inverts H as Hstep Hrest.
    destruct (IH _ Hrest) as [cmid [Ha Hb]].
    exists cmid.
    split; [eapply multistep_S; eauto | exact Hb].
Qed.

Lemma halts_in_unique n1 n2 (c : Q * tape) :
  halts_in tm c n1 -> halts_in tm c n2 -> n1 = n2.
Proof.
  intros [ch1 [R1 H1]] [ch2 [R2 H2]].
  destruct (PeanoNat.Nat.lt_trichotomy n1 n2) as [Hlt|[Heq|Hgt]];
    [| exact Heq |].
  - exfalso.
    replace n2 with (n1 + (n2 - n1))%nat in R2 by lia.
    destruct (multistep_split _ _ _ _ R2) as [cmid [Ra Rb]].
    pose proof (multistep_deterministic _ _ _ _ _ R1 Ra); subst cmid.
    destruct (n2 - n1)%nat as [|k] eqn:Ek; [lia|].
    inverts Rb as Hstep Hrest.
    exact (halted_no_step _ _ _ H1 Hstep).
  - exfalso.
    replace n1 with (n2 + (n1 - n2))%nat in R1 by lia.
    destruct (multistep_split _ _ _ _ R1) as [cmid [Ra Rb]].
    pose proof (multistep_deterministic _ _ _ _ _ R2 Ra); subst cmid.
    destruct (n1 - n2)%nat as [|k] eqn:Ek; [lia|].
    inverts Rb as Hstep Hrest.
    exact (halted_no_step _ _ _ H2 Hstep).
Qed.

(* Main results *)

Definition halt_steps : N :=
  3084308671325587968605861214780872830370624441351430%N.

Lemma zrun_total :
  zrun 4194304%positive zinit 0%N = (None, (halt_steps - 6)%N).
Proof. vm_cast_no_check (eq_refl (@None zstate, (halt_steps - 6)%N)). Qed.

Theorem tm_halts_in : halts_in tm c0 (N.to_nat halt_steps).
Proof.
  pose proof (zrun_sound 4194304%positive zinit 0%N) as H.
  rewrite zrun_total in H.
  destruct H as [d [Hd HH]].
  assert (Ed : d = (halt_steps - 6)%N) by lia.
  rewrite Ed in HH.
  replace (N.to_nat halt_steps)
    with (4 + (N.to_nat (halt_steps - 6)%N + 2))%nat
    by (unfold halt_steps; lia).
  eapply chalts_in_trans; [apply zinit_conf | exact HH].
Qed.

Theorem tm_halts : halts tm c0.
Proof.
  exists (N.to_nat halt_steps).
  apply tm_halts_in.
Qed.

Theorem tm_halt_steps_minimal :
  forall n, halts_in tm c0 n -> n = N.to_nat halt_steps.
Proof.
  intros n Hn.
  exact (halts_in_unique n (N.to_nat halt_steps) c0 Hn tm_halts_in).
Qed.

End IndividualProof.
