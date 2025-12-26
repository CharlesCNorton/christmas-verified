(******************************************************************************)
(*                                                                            *)
(*                The Twelve Days of Christmas: Verified Counting             *)
(*                                                                            *)
(*     A Coq formalization of the cumulative gift-giving structure in the     *)
(*     traditional English Christmas carol. We prove universal identities     *)
(*     for triangular and tetrahedral numbers arising from the song.          *)
(*                                                                            *)
(*     Key results:                                                           *)
(*       - Triangular numbers: T(n) = n(n+1)/2                                *)
(*       - Tetrahedral numbers: Te(n) = n(n+1)(n+2)/6                         *)
(*       - Grand total: 364 gifts (one short of a year)                       *)
(*       - Symmetry: gift k and gift (13-k) occur equally often               *)
(*                                                                            *)
(*     "On the twelfth day of Christmas, my true love sent to me..."          *)
(*     — Traditional, circa 1780                                              *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 24, 2025                                                *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Lia.

(** ========================================================================= *)
(** 1. FIGURATE NUMBERS                                                       *)
(** ========================================================================= *)

(** ** 1.1 Triangular Numbers *)

Fixpoint T (n : nat) : nat :=
  match n with
  | O => 0
  | S k => S k + T k
  end.

Lemma T_S : forall n, T (S n) = S n + T n.
Proof. reflexivity. Defined.

Theorem T_closed : forall n, 2 * T n = n * (n + 1).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite T_S.
    rewrite Nat.mul_add_distr_l.
    rewrite IH.
    nia.
Defined.

Lemma T_strictly_increasing : forall n, T (S n) > T n.
Proof.
  intro n.
  rewrite T_S.
  lia.
Defined.

Lemma T_positive : forall n, n > 0 -> T n > 0.
Proof.
  intros n H.
  destruct n.
  - lia.
  - simpl.
    lia.
Defined.

Lemma T_12 : T 12 = 78.
Proof. reflexivity. Defined.

Compute (T 1, T 2, T 3, T 4, T 5, T 6).
Compute (T 7, T 8, T 9, T 10, T 11, T 12).

Definition T_table : list nat :=
  T 1 :: T 2 :: T 3 :: T 4 :: T 5 :: T 6 ::
  T 7 :: T 8 :: T 9 :: T 10 :: T 11 :: T 12 :: nil.

Lemma T_table_values : T_table = 1 :: 3 :: 6 :: 10 :: 15 :: 21 ::
                                  28 :: 36 :: 45 :: 55 :: 66 :: 78 :: nil.
Proof. reflexivity. Defined.

Example T_witness : T 5 = 15.
Proof. reflexivity. Defined.

Example T_counterexample : T 5 <> 14.
Proof. discriminate. Defined.

(** ** 1.2 Tetrahedral Numbers *)

Fixpoint Te (n : nat) : nat :=
  match n with
  | O => 0
  | S k => T n + Te k
  end.

Lemma Te_S : forall n, Te (S n) = T (S n) + Te n.
Proof. reflexivity. Defined.

Theorem Te_closed : forall n, 6 * Te n = n * (n + 1) * (n + 2).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite Te_S.
    rewrite Nat.mul_add_distr_l.
    rewrite IH.
    assert (H : 2 * T (S n) = (S n) * (S n + 1)) by apply T_closed.
    nia.
Defined.

Lemma Te_strictly_increasing : forall n, Te (S n) > Te n.
Proof.
  intro n.
  rewrite Te_S.
  pose proof (T_positive (S n)) as H.
  lia.
Defined.

Theorem Te_monotone : forall m n, m < n -> Te m < Te n.
Proof.
  intros m n Hlt.
  induction Hlt as [|n Hlt IH].
  - apply Te_strictly_increasing.
  - pose proof (Te_strictly_increasing n) as Hstep.
    lia.
Defined.

Example Te_monotone_witness : Te 3 < Te 7.
Proof. simpl. lia. Defined.

Example Te_monotone_counterexample : ~ (Te 5 < Te 5).
Proof. lia. Defined.

Lemma Te_12 : Te 12 = 364.
Proof. reflexivity. Defined.

Compute (Te 1, Te 2, Te 3, Te 4, Te 5, Te 6).
Compute (Te 7, Te 8, Te 9, Te 10, Te 11, Te 12).

Definition Te_table : list nat :=
  Te 1 :: Te 2 :: Te 3 :: Te 4 :: Te 5 :: Te 6 ::
  Te 7 :: Te 8 :: Te 9 :: Te 10 :: Te 11 :: Te 12 :: nil.

Lemma Te_table_values : Te_table = 1 :: 4 :: 10 :: 20 :: 35 :: 56 ::
                                    84 :: 120 :: 165 :: 220 :: 286 :: 364 :: nil.
Proof. reflexivity. Defined.

Example Te_witness : Te 4 = 20.
Proof. reflexivity. Defined.

Example Te_counterexample : Te 4 <> 21.
Proof. discriminate. Defined.

Theorem Te_lower_bound : forall n, Te n >= T n.
Proof.
  induction n as [|n IH].
  - simpl.
    lia.
  - rewrite Te_S.
    lia.
Defined.

Example Te_lower_bound_witness : Te 5 >= T 5.
Proof. simpl. lia. Defined.

Example Te_lower_bound_counterexample : ~ (Te 1 >= 10).
Proof. simpl. lia. Defined.

(** ========================================================================= *)
(** 2. GIFT DISTRIBUTION                                                      *)
(** ========================================================================= *)

(** ** 2.1 Symmetry *)

Definition gifts_of_type (k n : nat) : nat := k * (n + 1 - k).

Theorem gift_symmetry : forall k n,
  k <= n ->
  gifts_of_type k n = gifts_of_type (n + 1 - k) n.
Proof.
  intros k n Hle.
  unfold gifts_of_type.
  replace (n + 1 - (n + 1 - k)) with k by lia.
  apply Nat.mul_comm.
Defined.

Lemma gifts_of_type_12 : forall k,
  1 <= k <= 12 ->
  gifts_of_type k 12 = gifts_of_type (13 - k) 12.
Proof.
  intros k [Hlo Hhi].
  apply gift_symmetry.
  lia.
Defined.

Lemma partridges : gifts_of_type 1 12 = 12.
Proof. reflexivity. Defined.

Lemma drummers : gifts_of_type 12 12 = 12.
Proof. reflexivity. Defined.

Lemma geese_and_swans : gifts_of_type 6 12 = 42 /\ gifts_of_type 7 12 = 42.
Proof. split; reflexivity. Defined.

Example symmetry_witness : gifts_of_type 1 12 = gifts_of_type 12 12.
Proof. reflexivity. Defined.

Example symmetry_counterexample : gifts_of_type 1 12 <> gifts_of_type 2 12.
Proof. discriminate. Defined.

(** ** 2.2 Double Counting *)

Fixpoint sum_gifts_by_type_aux (k total : nat) : nat :=
  match k with
  | O => 0
  | S j => gifts_of_type k total + sum_gifts_by_type_aux j total
  end.

Definition sum_gifts_by_type (n : nat) : nat := sum_gifts_by_type_aux n n.

Lemma sum_aux_S : forall k n,
  sum_gifts_by_type_aux (S k) n = gifts_of_type (S k) n + sum_gifts_by_type_aux k n.
Proof. reflexivity. Defined.

Lemma gifts_of_type_shift : forall k n,
  k <= S n ->
  gifts_of_type k (S n) = gifts_of_type k n + k.
Proof.
  intros k n Hle.
  unfold gifts_of_type.
  nia.
Defined.

Lemma sum_aux_shift : forall k n,
  k <= n ->
  sum_gifts_by_type_aux k (S n) = sum_gifts_by_type_aux k n + T k.
Proof.
  induction k as [|k IH].
  - intros.
    reflexivity.
  - intros n Hle.
    rewrite sum_aux_S.
    rewrite sum_aux_S.
    rewrite IH by lia.
    rewrite gifts_of_type_shift by lia.
    rewrite T_S.
    lia.
Defined.

Lemma gifts_at_boundary : forall n,
  gifts_of_type (S n) n = 0.
Proof.
  intro n.
  unfold gifts_of_type.
  replace (n + 1 - S n) with 0 by lia.
  lia.
Defined.

Lemma gifts_of_type_zero : forall k n,
  k > n -> gifts_of_type k n = 0.
Proof.
  intros k n Hgt.
  unfold gifts_of_type.
  replace (n + 1 - k) with 0 by lia.
  lia.
Defined.

Theorem double_counting_eq : forall n,
  Te n = sum_gifts_by_type n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - unfold sum_gifts_by_type in *.
    rewrite Te_S.
    rewrite sum_aux_S.
    rewrite sum_aux_shift by lia.
    rewrite <- IH.
    rewrite gifts_of_type_shift by lia.
    rewrite gifts_at_boundary.
    rewrite T_S.
    lia.
Defined.

Lemma sum_gifts_by_type_12 : sum_gifts_by_type 12 = 364.
Proof. reflexivity. Defined.

Example double_counting_witness : Te 12 = 364 /\ sum_gifts_by_type 12 = 364.
Proof. split; reflexivity. Defined.

Example double_counting_counterexample : Te 12 <> 365.
Proof. discriminate. Defined.

(** ========================================================================= *)
(** 3. THE GRAND TOTAL                                                        *)
(** ========================================================================= *)

(** ** 3.1 The 364 Theorem *)

Definition grand_total : nat := Te 12.

Compute grand_total.

Theorem grand_total_value : grand_total = 364.
Proof. reflexivity. Defined.

Theorem one_short_of_year : grand_total = 365 - 1.
Proof. reflexivity. Defined.

Theorem factorization : grand_total = 4 * 7 * 13.
Proof. reflexivity. Defined.

Theorem divisibility_structure :
  grand_total mod 4 = 0 /\
  grand_total mod 7 = 0 /\
  grand_total mod 13 = 0 /\
  grand_total mod 52 = 0.
Proof. repeat split; reflexivity. Defined.

Theorem weeks_in_year : grand_total = 52 * 7.
Proof. reflexivity. Defined.

Theorem twelve_unique_for_364 : forall n,
  Te n = 364 ->
  n = 12.
Proof.
  intros n Heq.
  destruct (Nat.le_gt_cases n 12) as [Hle | Hgt].
  - destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]].
    all: try discriminate.
    + reflexivity.
    + lia.
  - assert (Hte13 : Te 13 = 455) by reflexivity.
    destruct (Nat.eq_dec n 13) as [H13 | Hn13].
    + rewrite H13 in Heq.
      discriminate.
    + assert (Hgt13 : n > 13) by lia.
      pose proof (Te_monotone 13 n Hgt13) as Hmon.
      rewrite Hte13 in Hmon.
      lia.
Defined.

Theorem no_year_tetrahedral : forall n, Te n <> 365.
Proof.
  intro n.
  destruct (Nat.le_gt_cases n 12) as [Hle | Hgt].
  - destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]].
    all: try discriminate.
    lia.
  - assert (Hte13 : Te 13 = 455) by reflexivity.
    destruct (Nat.eq_dec n 13) as [H13 | Hn13].
    + rewrite H13.
      discriminate.
    + pose proof (Te_monotone 13 n) as Hmon.
      lia.
Defined.

Example twelve_unique_witness : Te 12 = 364 /\ Te 11 <> 364 /\ Te 13 <> 364.
Proof. simpl. repeat split; discriminate. Defined.

Theorem day_12_exceeds_fifth : 5 * T 12 > grand_total.
Proof. unfold grand_total. simpl. lia. Defined.

Theorem back_loaded : Te 12 - Te 6 > grand_total / 2.
Proof. unfold grand_total. simpl. lia. Defined.

Theorem quadratic_bound : forall n, T n <= n * n.
Proof.
  intro n.
  pose proof (T_closed n) as H.
  nia.
Defined.

Example main_witness : grand_total > 360 /\ grand_total < 370.
Proof. unfold grand_total. simpl. lia. Defined.

Example main_counterexample : grand_total <> 365.
Proof. discriminate. Defined.

(** ** 3.2 Binomial Representation *)

Fixpoint C (n k : nat) : nat :=
  match k with
  | O => 1
  | S k' =>
    match n with
    | O => 0
    | S n' => C n' k' + C n' k
    end
  end.

Compute (C 5 0, C 5 1, C 5 2, C 5 3, C 5 4, C 5 5).
Compute (C 13 2, C 14 3).

Lemma C_0 : forall n, C n 0 = 1.
Proof.
  intro n.
  destruct n.
  all: reflexivity.
Defined.

Lemma C_n_1 : forall n, C n 1 = n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite C_0.
    rewrite IH.
    reflexivity.
Defined.

Lemma C_S_2 : forall n, C (S n) 2 = n + C n 2.
Proof.
  intro n.
  simpl.
  rewrite C_n_1.
  reflexivity.
Defined.

Theorem T_eq_C : forall n, T n = C (n + 1) 2.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - replace (S n + 1) with (S (n + 1)) by lia.
    rewrite C_S_2.
    rewrite T_S.
    rewrite IH.
    lia.
Defined.

Lemma C_S_3 : forall n, C (S n) 3 = C n 2 + C n 3.
Proof. reflexivity. Defined.

Theorem Te_eq_C : forall n, Te n = C (n + 2) 3.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - replace (S n + 2) with (S (n + 2)) by lia.
    rewrite C_S_3.
    rewrite Te_S.
    rewrite IH.
    replace (n + 2) with (S n + 1) by lia.
    rewrite <- T_eq_C.
    lia.
Defined.

Theorem T_div_form : forall n, T n = n * (n + 1) / 2.
Proof.
  intro n.
  pose proof (T_closed n) as H.
  rewrite <- H.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul by lia.
  reflexivity.
Defined.

Theorem Te_formula_check : 6 * grand_total = 12 * 13 * 14.
Proof.
  unfold grand_total.
  rewrite Te_closed.
  reflexivity.
Defined.

Example binomial_witness : T 12 = C 13 2 /\ Te 12 = C 14 3.
Proof.
  split.
  - apply T_eq_C.
  - apply Te_eq_C.
Defined.

Example binomial_counterexample : C 12 2 <> T 12.
Proof. simpl. discriminate. Defined.

(** ** 3.3 The Parabola Maximum *)

Lemma quadratic_roots : forall k,
  k * k + 42 = 13 * k <-> k = 6 \/ k = 7.
Proof.
  intro k.
  split.
  - intro Heq.
    destruct k as [|[|[|[|[|[|[|[|k]]]]]]]].
    all: try discriminate.
    + left.
      reflexivity.
    + right.
      reflexivity.
    + simpl in Heq.
      lia.
  - intros [H6 | H7].
    all: subst.
    all: reflexivity.
Defined.

Lemma parabola_bound : forall k, k * (13 - k) <= 42.
Proof.
  intro k.
  destruct (Nat.le_gt_cases k 13) as [Hle | Hgt].
  - destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]]]].
    all: simpl.
    all: lia.
  - replace (13 - k) with 0 by lia.
    lia.
Defined.

Lemma parabola_equality_iff : forall k,
  k <= 13 ->
  (k * (13 - k) = 42 <-> k = 6 \/ k = 7).
Proof.
  intros k Hle.
  split.
  - intro Heq.
    assert (Hq : k * k + 42 = 13 * k) by nia.
    apply quadratic_roots.
    exact Hq.
  - intros [H6 | H7].
    + subst.
      reflexivity.
    + subst.
      reflexivity.
Defined.

Lemma parabola_max_12 : 6 * (13 - 6) = 42 /\ 7 * (13 - 7) = 42.
Proof. split; reflexivity. Defined.

Theorem max_at_middle : forall k,
  1 <= k <= 12 ->
  gifts_of_type k 12 <= 42.
Proof.
  intros k Hrange.
  unfold gifts_of_type.
  apply parabola_bound.
Defined.

Theorem max_unique : forall k,
  1 <= k <= 12 ->
  gifts_of_type k 12 = 42 <-> k = 6 \/ k = 7.
Proof.
  intros k Hrange.
  unfold gifts_of_type.
  replace (12 + 1 - k) with (13 - k) by lia.
  apply parabola_equality_iff.
  lia.
Defined.

Example max_unique_witness : gifts_of_type 6 12 = 42 /\ gifts_of_type 7 12 = 42.
Proof. split; reflexivity. Defined.

Example max_unique_counterexample : gifts_of_type 5 12 <> 42.
Proof. simpl. discriminate. Defined.

(** ========================================================================= *)
(** 4. PASCAL'S TRIANGLE CONNECTION                                          *)
(** ========================================================================= *)

(** ** 4.1 Pascal's Identity *)

Theorem pascal_identity : forall n k,
  C (S n) (S k) = C n k + C n (S k).
Proof. reflexivity. Defined.

Lemma C_overflow : forall n k, k > n -> C n k = 0.
Proof.
  induction n as [|n IH].
  - intros k Hgt.
    destruct k.
    + lia.
    + reflexivity.
  - intros k Hgt.
    destruct k as [|k].
    + lia.
    + simpl.
      rewrite IH by lia.
      rewrite IH by lia.
      lia.
Defined.

Lemma C_n_n : forall n, C n n = 1.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite C_overflow by lia.
    lia.
Defined.

Theorem C_sym : forall n k,
  k <= n ->
  C n k = C n (n - k).
Proof.
  induction n as [|n IH].
  - intros k Hle.
    replace k with 0 by lia.
    reflexivity.
  - intros k Hle.
    destruct k as [|k].
    + replace (S n - 0) with (S n) by lia.
      rewrite C_0.
      rewrite C_n_n.
      reflexivity.
    + destruct (Nat.eq_dec (S k) (S n)) as [Heq | Hneq].
      * rewrite Heq.
        replace (S n - S n) with 0 by lia.
        rewrite C_0.
        rewrite C_n_n.
        reflexivity.
      * simpl.
        replace (S n - S k) with (S (n - S k)) by lia.
        simpl.
        assert (Hk : k <= n) by lia.
        assert (Hsk : S k <= n) by lia.
        assert (Hnsk : n - S k <= n) by lia.
        assert (Hnk : n - k <= n) by lia.
        rewrite (IH k Hk).
        rewrite (IH (S k) Hsk).
        replace (n - k) with (S (n - S k)) by lia.
        lia.
Defined.

Lemma C_row_sum_aux : forall n k,
  k <= n ->
  C n k + C n (S k) = C (S n) (S k).
Proof.
  intros n k Hle.
  simpl.
  reflexivity.
Defined.

Fixpoint row_sum (n k : nat) : nat :=
  match k with
  | O => C n 0
  | S k' => C n k + row_sum n k'
  end.

Example row_sum_2 : row_sum 2 2 = 4.
Proof. reflexivity. Defined.

Example row_sum_3 : row_sum 3 3 = 8.
Proof. reflexivity. Defined.

Example row_sum_4 : row_sum 4 4 = 16.
Proof. reflexivity. Defined.

Example row_sum_5 : row_sum 5 5 = 32.
Proof. reflexivity. Defined.

Example pascal_witness : C 5 2 = C 5 3.
Proof. reflexivity. Defined.

Example pascal_counterexample : C 6 2 <> C 6 3.
Proof. discriminate. Defined.

(** ** 4.2 Triangular and Tetrahedral as Diagonals *)

Theorem T_is_diagonal_2 : forall n,
  T n = C (n + 1) 2.
Proof. exact T_eq_C. Defined.

Theorem Te_is_diagonal_3 : forall n,
  Te n = C (n + 2) 3.
Proof. exact Te_eq_C. Defined.

Definition diagonal_sum (d len : nat) : nat :=
  fold_left (fun acc i => acc + C (i + d) d) (seq 0 len) 0.

Lemma fold_left_plus_acc : forall l a b,
  fold_left (fun acc x => acc + x) l (a + b) =
  a + fold_left (fun acc x => acc + x) l b.
Proof.
  induction l as [|x l IH].
  - intros.
    reflexivity.
  - intros a b.
    simpl.
    rewrite <- IH.
    f_equal.
    lia.
Defined.

Example diagonal_sum_0 : diagonal_sum 2 0 = 0.
Proof. reflexivity. Defined.

Example diagonal_sum_1 : diagonal_sum 2 1 = 1.
Proof. reflexivity. Defined.

Example diagonal_sum_2 : diagonal_sum 2 2 = 4.
Proof. reflexivity. Defined.

Example diagonal_sum_3 : diagonal_sum 2 3 = 10.
Proof. reflexivity. Defined.

Example diagonal_sum_4 : diagonal_sum 2 4 = 20.
Proof. reflexivity. Defined.

Example diagonal_sum_12 : diagonal_sum 2 12 = Te 12.
Proof. reflexivity. Defined.

Example diagonal_witness : diagonal_sum 2 5 = Te 5.
Proof. reflexivity. Defined.

Example diagonal_counterexample : diagonal_sum 2 5 <> Te 4.
Proof. discriminate. Defined.

(** ========================================================================= *)
(** 5. ASYMPTOTIC BOUNDS                                                     *)
(** ========================================================================= *)

(** ** 5.1 Polynomial Bounds for Triangular Numbers *)

Theorem T_lower_bound : forall n, 2 * T n >= n * n.
Proof.
  intro n.
  rewrite T_closed.
  nia.
Defined.

Theorem T_upper_bound : forall n, T n <= n * n.
Proof.
  exact quadratic_bound.
Defined.

Theorem T_asymptotic : forall n,
  n * n <= 2 * T n /\ 2 * T n <= 2 * n * n.
Proof.
  intro n.
  rewrite T_closed.
  split.
  - nia.
  - nia.
Defined.

Example T_bounds_witness : 25 <= 2 * T 5 /\ 2 * T 5 <= 50.
Proof. simpl. lia. Defined.

Example T_bounds_counterexample : ~ (2 * T 5 < 25).
Proof. simpl. lia. Defined.

(** ** 5.2 Polynomial Bounds for Tetrahedral Numbers *)

Theorem Te_lower_cubic : forall n, 6 * Te n >= n * n * n.
Proof.
  intro n.
  rewrite Te_closed.
  nia.
Defined.

Theorem Te_upper_cubic : forall n, 6 * Te n <= n * n * n + 3 * n * n + 2 * n.
Proof.
  intro n.
  rewrite Te_closed.
  nia.
Defined.

Theorem Te_asymptotic : forall n,
  n * n * n <= 6 * Te n /\ 6 * Te n <= (n + 2) * (n + 2) * (n + 2).
Proof.
  intro n.
  rewrite Te_closed.
  split.
  - nia.
  - nia.
Defined.

Theorem Te_cubic_ratio : forall n,
  n > 0 ->
  Te n * 6 = n * n * n + 3 * n * n + 2 * n.
Proof.
  intros n Hpos.
  rewrite Nat.mul_comm.
  rewrite Te_closed.
  nia.
Defined.

Example Te_cubic_witness : 6 * Te 10 = 10 * 11 * 12.
Proof. reflexivity. Defined.

Example Te_cubic_counterexample : 6 * Te 10 <> 1000.
Proof. discriminate. Defined.

(** ** 5.3 Growth Rate Comparison *)

Example Te_and_T_at_2 : Te 2 = 4 /\ T 2 = 3.
Proof. split; reflexivity. Defined.

Example Te_and_T_at_5 : Te 5 = 35 /\ T 5 = 15.
Proof. split; reflexivity. Defined.

Example Te_and_T_at_12 : Te 12 = 364 /\ T 12 = 78.
Proof. split; reflexivity. Defined.

Example Te_double_T_at_2 : Te 2 = 2 * T 2 - 2.
Proof. reflexivity. Defined.

Example Te_double_T_at_5 : Te 5 = 2 * T 5 + 5.
Proof. reflexivity. Defined.

Example growth_witness : Te 5 - 2 * T 5 = 5.
Proof. reflexivity. Defined.

Example growth_counterexample : Te 2 - 2 * T 2 = 0.
Proof. reflexivity. Defined.

(** ========================================================================= *)
(** 6. GENERATING FUNCTION CONNECTION (COMPUTATIONAL)                       *)
(** ========================================================================= *)

Fixpoint partial_sums_aux (l : list nat) (acc : nat) : list nat :=
  match l with
  | nil => nil
  | x :: xs => (acc + x) :: partial_sums_aux xs (acc + x)
  end.

Definition partial_sums (l : list nat) : list nat := partial_sums_aux l 0.

Definition ones (n : nat) : list nat := repeat 1 n.

Example ones_5 : ones 5 = 1 :: 1 :: 1 :: 1 :: 1 :: nil.
Proof. reflexivity. Defined.

Example ps_ones_5 : partial_sums (ones 5) = 1 :: 2 :: 3 :: 4 :: 5 :: nil.
Proof. reflexivity. Defined.

Example ps_ps_ones_5 : partial_sums (partial_sums (ones 5)) =
                        1 :: 3 :: 6 :: 10 :: 15 :: nil.
Proof. reflexivity. Defined.

Example ps_ps_ps_ones_5 : partial_sums (partial_sums (partial_sums (ones 5))) =
                           1 :: 4 :: 10 :: 20 :: 35 :: nil.
Proof. reflexivity. Defined.

Example T_from_ps : nth 4 (partial_sums (partial_sums (ones 5))) 0 = T 5.
Proof. reflexivity. Defined.

Example Te_from_ps : nth 4 (partial_sums (partial_sums (partial_sums (ones 5)))) 0 = Te 5.
Proof. reflexivity. Defined.

Example gf_witness : nth 4 (partial_sums (partial_sums (ones 6))) 0 = T 5.
Proof. reflexivity. Defined.

Example gf_counterexample : nth 5 (partial_sums (partial_sums (ones 6))) 0 <> T 5.
Proof. discriminate. Defined.
