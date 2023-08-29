import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Core
import Mathlib.Algebra.BigOperators.Basic
import Turan4.NbhdRes
import Turan4.Turanpartition


open Finset Nat Turanpartition

open scoped BigOperators

namespace SimpleGraph

section Multipartite


variable {α : Type _} [Fintype α]  [DecidableEq α]


-- given a t+1 partition on A form the complete multi-partite graph on A
-- with all edges present between different parts in M.A and no edges involving vertices outside A or inside any part of A
@[reducible]
def mp (M : MultiPart α) : SimpleGraph α
    where
  Adj x y :=
    ∃ i ∈ range (M.t + 1),
      ∃ j ∈ range (M.t + 1), i ≠ j ∧ (x ∈ M.P i ∧ y ∈ M.P j ∨ x ∈ M.P j ∧ y ∈ M.P i)
  symm := by
    intro x y hxy
    obtain ⟨i, hi, j, hj, ne, ⟨hx, hy⟩⟩ := hxy
    · refine' ⟨j, hj, i, hi, ne.symm, _⟩; left; exact ⟨hy, hx⟩
    · refine' ⟨i, hi, j, hj, ne, _⟩; left; rwa [and_comm]
  loopless := by
    intro x; push_neg;push_neg; intro i hi j hj ne
    constructor <;> intro hxi hxj
    apply not_disjoint_iff.2 ⟨x, hxi, hxj⟩ (M.disj i hi j hj ne)
    apply not_disjoint_iff.2 ⟨x, hxj, hxi⟩ (M.disj i hi j hj ne)

instance mpDecidableRel {M: MultiPart α} : DecidableRel (mp M).Adj := by infer_instance

instance NeighborMpSet.memDecidable (v : α) : DecidablePred (· ∈ (mp M).neighborSet v) := by
  infer_instance

-- instance multiPartiteFintype : Fintype (mp M).edgeSetEmbedding := by infer_instance

--any vertex in α but not in A is isolated
theorem no_nbhrs {M : MultiPart α} (hA : v ∉ M.A) : ¬(mp M).Adj v w :=
  by
  contrapose! hA
  obtain ⟨i, hi, j, hj, _, hv⟩ := hA; 
  cases hv with
  | inl hv => exact (sub_part hi) hv.1
  | inr hv =>  exact (sub_part hj) hv.1

-- having any neighbour implies the vertex is in A
theorem nbhrs_imp {M : MultiPart α} : (mp M).Adj v w → v ∈ M.A := 
by 
  intro h1; by_contra h;
  exact no_nbhrs h h1

-- if v and w belong to parts P i and P j and vw is an edge then i≠j
theorem mp_adj_imp {M : MultiPart α} (hi : i ∈ range (M.t + 1))
    (hj : j ∈ range (M.t + 1)) (hvi : v ∈ M.P i) (hwj : w ∈ M.P j) : (mp M).Adj v w → i ≠ j :=
  by
  intro h; cases' h with a ha
  obtain ⟨har, b, hbr, abne, ab⟩ := ha; 
  cases ab with
  | inl ab => 
    have ai := uniq_part hi har hvi ab.1; have bj := uniq_part hj hbr hwj ab.2
    rwa [← ai, ← bj] at abne 
  | inr ab => 
    have aj := uniq_part hj har hwj ab.2; have bi := uniq_part hi hbr hvi ab.1
    rw [← aj, ← bi] at abne 
    exact abne.symm

--if v and w are in distinct parts then they are adjacent
theorem mp_imp_adj {M : MultiPart α} (hi : i ∈ range (M.t + 1))
    (hj : j ∈ range (M.t + 1)) (hvi : v ∈ M.P i) (hwj : w ∈ M.P j) : i ≠ j → (mp M).Adj v w := by
  intro h; refine' ⟨i, hi, j, hj, h, _⟩; left; exact ⟨hvi, hwj⟩

--if v in P i and vw is an edge then w ∉ P i
theorem not_nbhr_same_part {M : MultiPart α} (hi : i ∈ range (M.t + 1))
    (hv : v ∈ M.P i) : (mp M).Adj v w → w ∉ M.P i := 
by 
  intro h1; by_contra h;
  apply mp_adj_imp hi hi hv h h1; rfl

-- given two vertices in the same part they are not adjacent
theorem not_nbhr_same_part' {M : MultiPart α}(hi : i ∈ range (M.t + 1))
    (hv : v ∈ M.P i) (hw : w ∈ M.P i) : ¬(mp M).Adj v w := 
by 
  intro h1; contrapose hw;
  exact not_nbhr_same_part hi hv h1

-- if v in P i  and w in A\(P i) then vw is an edge
theorem nbhr_diff_parts {M : MultiPart α} (hi : i ∈ range (M.t + 1))
    (hv : v ∈ M.P i) (hw : w ∈ M.A \ M.P i) : (mp M).Adj v w :=
  by
  rw [mem_sdiff] at hw 
  cases' hw with hA hni
  rw [M.uni] at hA ; rw [mem_biUnion] at hA 
  obtain ⟨j, hj1, hj2⟩ := hA
  refine' mp_imp_adj hi hj1 hv hj2 _; intro h; rw [h] at hni ; exact hni hj2

--if v is in P i then its nbhd is A\(P i)
theorem mp_nbhd {M : MultiPart α} (hv : i ∈ range (M.t + 1) ∧ v ∈ M.P i) :
    (mp M).neighborFinset v = M.A \ M.P i := by
  ext; constructor;
  · rw [mem_neighborFinset]; intro h; rw [adj_comm] at h 
    rw [mem_sdiff]; refine' ⟨nbhrs_imp h, _⟩; exact not_nbhr_same_part hv.1 hv.2 h.symm
  · rw [mem_neighborFinset]; exact nbhr_diff_parts hv.1 hv.2

-- degree sum over all vertices i.e. 2*e(mp M)
def mpDsum (M : MultiPart α) : ℕ :=
  ∑ v in M.A, (mp M).degree v

-- degree of vertex in P i is card(A\P i)
theorem mp_deg {M : MultiPart α} (hv : i ∈ range (M.t + 1) ∧ v ∈ M.P i) :
    (mp M).degree v = (M.A \ M.P i).card := by rw [degree]; rw [mp_nbhd hv]

-- degree of v in P i as |A|- |P i|
theorem mp_deg_diff {M : MultiPart α} (hv : i ∈ range (M.t + 1) ∧ v ∈ M.P i) :
    (mp M).degree v = M.A.card - (M.P i).card := by rw [mp_deg hv]; exact card_sdiff (sub_part hv.1)

-- sum of degrees as sum over parts
theorem mp_deg_sum (M : MultiPart α) :
    ∑ v in M.A, (mp M).degree v = ∑ i in range (M.t + 1), (M.P i).card * (M.A \ M.P i).card :=
  by
  nth_rw 1 [M.uni]
  rw [sum_biUnion (pair_disjoint M)]; apply Finset.sum_congr rfl _
  intro x hx; rw [Finset.card_eq_sum_ones, sum_mul, one_mul]; apply Finset.sum_congr rfl _
  intro v hv; exact mp_deg ⟨hx, hv⟩

--- same using squares of part sizes and avoiding the cursed tsubtraction
theorem mp_deg_sum_sq' (M : MultiPart α) :
    ∑ v in M.A, (mp M).degree v + ∑ i in range (M.t + 1), (M.P i).card ^ 2 = M.A.card ^ 2 :=
  by
  rw [mp_deg_sum M]; rw [pow_two]; nth_rw 1 [card_uni]; rw [← sum_add_distrib]; rw [sum_mul]
  refine' Finset.sum_congr rfl _
  intro x hx; rw [pow_two]; rw [← mul_add]; rw [card_part_uni hx]

-- expressed  as |A|^2- ∑ degrees squared
theorem mp_deg_sum_sq (M : MultiPart α) :
    ∑ v in M.A, (mp M).degree v = M.A.card ^ 2 - ∑ i in range (M.t + 1), (M.P i).card ^ 2 :=
  eq_tsub_of_add_eq (mp_deg_sum_sq' M)

-- turanPartition partition corresponds to balanced partition sizes so if we have two turanPartition partitions
-- of same set A into the same number of parts then their degree sums are the the same
theorem turanPartition_deg_sum_eq (M N : MultiPart α) :
    M.A = N.A → M.t = N.t → TuranPartition M → TuranPartition N → mpDsum M = mpDsum N :=
  by
  intro hA ht iM iN; unfold mpDsum; rw [mp_deg_sum_sq, mp_deg_sum_sq, hA];
  rw [turanPartition_iff_not_moveable, Moveable, Classical.not_not] at *
  apply congr_arg _
  have hN := turan_bal iN; rw [← ht, ← hA] at hN 
  have := bal_turan_help' (turan_bal iM) hN; rwa [← ht]

-- this is the part of the degree sum that has changed by moving a vertex
theorem mp_deg_sum_move_help {M : MultiPart α}  (hvi : i ∈ range (M.t + 1) ∧ v ∈ M.P i) (hj : j ∈ range (M.t + 1) ∧ j ≠ i)
    (hc : (M.P j).card + 1 < (M.P i).card) :
    (M.P i).card * (M.A \ M.P i).card + (M.P j).card * (M.A \ M.P j).card <
      ((move M hvi hj).P i).card * ((move M hvi hj).A \ (move M hvi hj).P i).card +
        ((move M hvi hj).P j).card * ((move M hvi hj).A \ (move M hvi hj).P j).card :=
by
  rw [move_Pcard hvi hj hvi.1, move_Pcard hvi hj hj.1, move_Pcard_sdiff hvi hj hvi.1,
    move_Pcard_sdiff hvi hj hj.1]
  split_ifs with h h_1 h_2 h_3 h_4 h_5 h_6 h_7; 
  · exfalso; exact h.1 rfl; 
  · exfalso; exact h.1 rfl;
  · exfalso; exact h.1 rfl;
  · exfalso; apply h_4.2 rfl; 
  · exfalso; exact hj.2 h_5
  · rw [card_sdiff (sub_part hvi.1)]; rw [card_sdiff (sub_part hj.1)]
    exact move_change hc (two_parts hvi.1 hj.1 hj.2.symm)
  · exfalso; exact h_6.2 rfl
  · contradiction
  · contradiction
  
-- this is the part of the degree sum that hasn't changed by moving a vertex
theorem mp_deg_sum_move_help2 {M : MultiPart α}
    (hvi : i ∈ range (M.t + 1) ∧ v ∈ M.P i) (hj : j ∈ range (M.t + 1) ∧ j ≠ i) :
    ∑ x : ℕ in ((range (M.t + 1)).erase j).erase i,
        ((move M hvi hj).P x).card * ((move M hvi hj).A \ (move M hvi hj).P x).card =
      ∑ y : ℕ in ((range (M.t + 1)).erase j).erase i, (M.P y).card * (M.A \ M.P y).card :=
by
  apply sum_congr rfl _; intro k hk; rw [move_Pcard hvi hj]; rw [move_Pcard_sdiff hvi hj];
  split_ifs with h h_1;
  · rfl
  · exfalso; rw [h_1] at hk ; exact not_mem_erase i _ hk;
  · exfalso; push_neg at h ; simp_all only [Ne.def, not_false_iff, mem_erase, eq_self_iff_true]
  · exact mem_of_mem_erase (mem_of_mem_erase hk); 
  · exact mem_of_mem_erase (mem_of_mem_erase hk)

-- given a vertex v ∈ P i and a part P j such that card(P j)+1 < card(P i) then moving v from Pi to Pj will increase the sum of degrees
-- putting the two previous lemmas together tells us that the move has increased the degree sum
theorem mp_deg_sum_move {M : MultiPart α} (hvi : i ∈ range (M.t + 1) ∧ v ∈ M.P i)
    (hj : j ∈ range (M.t + 1) ∧ j ≠ i) (hc : (M.P j).card + 1 < (M.P i).card) :
    ∑ w in M.A, (mp M).degree w < ∑ w in (move M hvi hj).A, (mp (move M hvi hj)).degree w :=
  by
  rw [mp_deg_sum M, mp_deg_sum (move M hvi hj), move_t hvi hj]
  rw [← sum_erase_add (range (M.t + 1)) _ hj.1, ← sum_erase_add (range (M.t + 1)) _ hj.1]
  rw [← sum_erase_add ((range (M.t + 1)).erase j) _ (mem_erase_of_ne_of_mem hj.2.symm hvi.1)]
  rw [← sum_erase_add ((range (M.t + 1)).erase j) _ (mem_erase_of_ne_of_mem hj.2.symm hvi.1)]
  rw [mp_deg_sum_move_help2]
  rw [add_assoc, add_assoc]; refine' (add_lt_add_iff_left _).mpr _;
  exact mp_deg_sum_move_help hvi hj hc

-- equivalently moving v from P i to P j reduces sum of sum_sq_c of part sizes (basically edges in the complement of mp)
theorem sumSqC_dec (M : MultiPart α) (hvi : i ∈ range (M.t + 1) ∧ v ∈ M.P i)
    (hj : j ∈ range (M.t + 1) ∧ j ≠ i) (hc : (M.P j).card + 1 < (M.P i).card) :
    sumSqC (move M hvi hj) < sumSqC M := by
  unfold sumSqC
  have h3 := mp_deg_sum_move hvi hj hc
  have h1 := mp_deg_sum_sq' M; 
  have h2 := mp_deg_sum_sq' (move M hvi hj); 
  rw [move_a, move_t] at *
  rw [← h2] at h1 ;  linarith


-- Given any partition M we can find a turanPartition on the same set with the same number of parts.
theorem moved (M : MultiPart α) :
    ∃ N : MultiPart α, N.A = M.A ∧ N.t = M.t ∧ TuranPartition N ∧ mpDsum M ≤ mpDsum N :=
by
  -- have : WellFounded (InvImage (· < ·) (fun M => (@sumSqC α _ _ M)))
  -- · exact InvImage.wf _ Nat.lt_wfRel.wf
  apply WellFounded.recursion (InvImage.wf sumSqC Nat.lt_wfRel.wf) M
  intro X h
  by_cases h' : TuranPartition X; 
  · exact ⟨X, rfl, rfl, h', le_rfl⟩;
  · obtain ⟨i, hi, j, hj, v, hv, ne, hc⟩ := not_turanPartition_imp h'
    set Y := move X ⟨hi, hv⟩ ⟨hj, ne⟩ with hY
    specialize h Y (sumSqC_dec X ⟨hi, hv⟩ ⟨hj, ne⟩ hc)
    rw [move_t, move_a] at h ; have := mp_deg_sum_move ⟨hi, hv⟩ ⟨hj, ne⟩ hc;
    rw [← mpDsum, ← mpDsum, ← hY] at this 
    obtain ⟨N, h1, h2, h3, h4⟩ := h; 
    refine ⟨N, h1, h2, h3, ?_⟩; 
    exact this.le.trans h4

-- Only Turan graphs maximize number of edges:
-- given a turanPartition and any other partition on the same set and into same number of parts
-- that is not-turan, the degree sum of the former is strictly larger
theorem moved_max (M N : MultiPart α) :
    M.A = N.A → M.t = N.t → TuranPartition M → ¬TuranPartition N → mpDsum N < mpDsum M :=
by
  intro hA ht him h1
  obtain ⟨i, hi, j, hj, v, hv, ne, hc⟩ := not_turanPartition_imp h1
  set O := move N ⟨hi, hv⟩ ⟨hj, ne⟩;
  have Ns : mpDsum N < mpDsum O := mp_deg_sum_move ⟨hi, hv⟩ ⟨hj, ne⟩ hc
  obtain ⟨Q, QA, Qt, Qim, Qs⟩ := moved O; 
  have := turanPartition_deg_sum_eq M Q -- _ _ him Qim;
  rw [this]
  · exact lt_of_lt_of_le Ns Qs;
  · rw [hA, QA]; have NOA : N.A = O.A := move_a ⟨hi, hv⟩ ⟨hj, ne⟩; exact NOA
  · rw [ht, Qt]; have NOt : N.t = O.t := move_t ⟨hi, hv⟩ ⟨hj, ne⟩; exact NOt
  · exact him 
  · exact Qim 

-- the degree sum of any complete (t+1)-partite graph is at most twice the turan numb of parts and set size
theorem turan_bound_M (M : MultiPart α) : mpDsum M ≤ 2 * turanNumb M.t M.A.card :=
by
  obtain ⟨N, hA, ht, iN, sN⟩ := moved M
  apply le_trans sN _; apply le_of_eq
  rw [turanPartition_iff_not_moveable] at iN ; rw [Moveable] at iN ; rw [Classical.not_not] at iN ;
  rw [← hA]; rw [← ht]
  have := bal_turan_bd (turan_bal iN)
  rw [sumSq] at this ; rw [mpDsum]; rw [mp_deg_sum_sq];-- unfold P' at this 
  rw [← this, add_comm]; simp only [add_tsub_cancel_right]

-- so if we have a partition of α then the number of edges is at most the turan number
theorem turan_max_edges (M : MultiPart α) :
    M.A = univ → (mp M).edgeFinset.card ≤ turanNumb M.t (Fintype.card α) :=
  by
  intro hA; apply (mul_le_mul_left (by norm_num : 0 < 2)).mp
  rw [← sum_degrees_eq_twice_card_edges]; have := turan_bound_M M; unfold mpDsum at this ;
  rw [hA] at this 
  rwa [card_univ] at this 

-- Now reformulate our bound to say that any complete multipartite graph on α that attains the turan bound is a turanPartition
theorem turan_eq_imp (M : MultiPart α) (hu : M.A = univ) :
    (mp M).edgeFinset.card = turanNumb M.t (Fintype.card α) → TuranPartition M :=
  by
  intro h; contrapose h; apply Nat.ne_of_lt; obtain ⟨N, NA, Nt, iN, le⟩ := moved M
  apply (mul_lt_mul_left (by norm_num : 0 < 2)).mp; rw [← sum_degrees_eq_twice_card_edges]
  have lt := moved_max N M NA Nt iN h
  have le2 := turan_bound_M N; unfold mpDsum at *; rw [hu] at *; rw [NA] at *; rw [Nt] at *;
  rw [card_univ] at *
  exact lt_of_lt_of_le lt le2


-- finally need to verify that any turan partition does indeed attain the upper bound
theorem turan_imm_imp_eq (M : MultiPart α) (hu : M.A = univ) (ht : M.t = t) :
    TuranPartition M → (mp M).edgeFinset.card = turanNumb t (Fintype.card α) :=
  by
  rw [turanPartition_iff_not_moveable]; unfold Moveable; rw [Classical.not_not]
  intro iM; apply (mul_right_inj' (by norm_num : 2 ≠ 0)).mp
  rw [← sum_degrees_eq_twice_card_edges, ← hu, ← ht]
  rw [mp_deg_sum_sq, ← card_univ, ← hu]
  simp only [← bal_turan_bd (turan_bal iM), sumSq, add_tsub_cancel_left]

--- next few results for counting degrees in mp once a new part has been inserted.
-- vertices in new part are adjacent to all old vertices
--- should have used lemmas from multipartite for this...
-- this says that the degree of any vertex in the new part equals the sum over the old parts
theorem mp_com (M : MultiPart α) (h : Disjoint M.A C) :
    ∀ v ∈ C, (mp (minsert M h)).degRes v M.A = M.A.card :=
by
  intro v hv; rw [degRes]; congr; ext a
  rw [mem_res_nbhd_iff];
  simp only [mem_neighborFinset, mem_range, Ne.def, exists_prop, and_iff_left_iff_imp]
  intro ha; obtain ⟨j, hjr, hjm⟩ := inv_part ha
  use j; rw [insert_t]
  refine' ⟨_, _, _, _, _⟩; 
  · rw [mem_range] at *; apply hjr.trans (lt_succ_self _) 
  · exact M.t + 1; 
  · exact lt_succ_self _
  · intro eq; rw [eq] at hjr ; exact not_mem_range_self hjr
  · right; rw [insert_P]; split_ifs with h; 
    · exfalso; exact h rfl; 
    · rw [insert_P]; refine' ⟨hv, _⟩;
      split_ifs with h_2; 
      · exact hjm;
      · push_neg at h_2 ; exfalso; rw [h_2] at hjr ; exact not_mem_range_self hjr


-- given two vertices in the old partition they are adjacent in the partition with 
-- C inserted iff they were already adjacent
theorem mp_old_adj (M : MultiPart α) (h : Disjoint M.A C) :
    v ∈ M.A → w ∈ M.A → ((mp M).Adj v w ↔ (mp (minsert M h)).Adj v w) :=
  by
  intro hv hw
  constructor;
  · intro hins; obtain ⟨k, hkr, l, hlr, lnek, lkc⟩ := hins
    use k; rw [insert_t]; rw [mem_range] at *; refine' ⟨hkr.trans (lt_succ_self _), l, _, lnek, _⟩;
    · rw [mem_range]; exact hlr.trans (lt_succ_self _)
    · simp [insert_P]
      split_ifs with h_1 h_2 h_3;
      · exfalso; rw [← h_1] at hkr ; exact lt_irrefl k hkr
      · exfalso; rw [← h_1] at hkr ; exact lt_irrefl k hkr
      · exfalso; rw [← h_3] at hlr ; exact lt_irrefl l hlr
      · exact lkc
  · intro hins; obtain ⟨k, hkr, l, hlr, lnek, lkc⟩ := hins; rw [insert_t] at hkr ;
    rw [insert_t] at hlr 
    refine' ⟨k, _, l, _, lnek, _⟩;
    · rw [mem_range] at *
      by_contra h'; 
      have : k = M.t + 1 
      · push_neg at h'; apply le_antisymm (le_of_lt_succ hkr) h'
      cases lkc with
      | inl lkc => 
        rw [this] at lkc 
        apply not_disjoint_iff.2 ⟨v, hv, insert_C M h lkc.1⟩ h
      | inr lkc => 
        rw [this] at lkc ; apply not_disjoint_iff.2 ⟨w, hw, insert_C M h lkc.2⟩ h
    · rw [mem_range] at *
      by_contra h'; 
      have : l = M.t + 1 
      · push_neg at h'; apply le_antisymm (le_of_lt_succ hlr) h' 
      cases lkc with
      | inl lkc => 
        rw [this] at lkc 
        apply not_disjoint_iff.2 ⟨w, hw, insert_C M h lkc.2⟩ h
      | inr lkc =>   
        rw [this] at lkc 
        apply not_disjoint_iff.2 ⟨v, hv, insert_C M h lkc.1⟩ h
    · cases lkc with
      | inl lkc => 
        rw [insert_P, insert_P] at lkc ; split_ifs at lkc with  h_1 h_2;
        · left; exact lkc
        · exfalso; exact not_disjoint_iff.2 ⟨w, hw, lkc.2⟩ h
        · exfalso; exact not_disjoint_iff.2 ⟨v, hv, lkc.1⟩ h
        · exfalso; exact not_disjoint_iff.2 ⟨w, hw, lkc.2⟩ h
      | inr lkc =>   
        rw [insert_P, insert_P] at lkc ; split_ifs at lkc with h_1 h_2;
        · right; exact lkc
        · exfalso; exact not_disjoint_iff.2 ⟨w, hw, lkc.2⟩ h
        · exfalso; exact not_disjoint_iff.2 ⟨v, hv, lkc.1⟩ h
        · exfalso; exact not_disjoint_iff.2 ⟨w, hw, lkc.2⟩ h

-- previous lemma interpreted in terms of res nbhds
theorem mp_old_nbhdRes (M : MultiPart α) (h : Disjoint M.A C) :
    ∀ v ∈ M.A, (mp (minsert M h)).nbhdRes v M.A = (mp M).nbhdRes v M.A :=
  by
  --  set H: simple_graph α:= (mp (minsert M h)),
  intro v hv;
  ext; constructor;
  · intro ha; rw [mem_res_nbhd_iff] at *; refine' ⟨ha.1, _⟩
    rw [mem_neighborFinset]; rw [mem_neighborFinset] at ha ;
    exact (mp_old_adj M h hv ha.1).mpr ha.2
  · intro ha; rw [mem_res_nbhd_iff] at *; refine' ⟨ha.1, _⟩
    rw [mem_neighborFinset]; rw [mem_neighborFinset] at ha ;
    exact (mp_old_adj M h hv ha.1).mp ha.2

-- .. and in terms of deg res
theorem mp_old_degRes (M : MultiPart α) (h : Disjoint M.A C) :
    ∀ v ∈ M.A, (mp (minsert M h)).degRes v M.A = (mp M).degRes v M.A := 
by 
  intro v hv; rw [degRes];
  rw [degRes]; rw [mp_old_nbhdRes M h v hv]

-- so sum of deg res to old partition over old partition is unchanged
theorem mp_old_sum (M : MultiPart α) (h : Disjoint M.A C) :
    ∑ v in M.A, (mp (minsert M h)).degRes v M.A = ∑ v in M.A, (mp M).degRes v M.A :=
  sum_congr rfl (mp_old_degRes M h)

-- vertices in the new part are not adjacent to each other
theorem mp_int_adj (M : MultiPart α) (h : Disjoint M.A C) :
    v ∈ C → w ∈ C → ¬(mp (minsert M h)).Adj v w :=
  by
  intro hv hw; have vin := insert_P' M h v hv
  have win := insert_P' M h w hw
  have := self_mem_range_succ (M.t + 1); rw [← insert_t M h] at this 
  contrapose win; push_neg at win ; exact not_nbhr_same_part this vin win

-- so their deg res to the new part is zero
theorem mp_int_degRes (M : MultiPart α) (h : Disjoint M.A C) :
    ∀ v ∈ C, (mp (minsert M h)).degRes v C = 0 :=
  by
  intro v hv; rw [degRes]; rw [card_eq_zero]; by_contra h'
  obtain ⟨w, hw, adw⟩ := (mp (minsert M h)).exists_mem_nempty h'
  exact (mp_int_adj M h hv hw) adw

-- so the sum of their deg res to new part is also zero i.e. e(C)=0
theorem mp_int_sum (M : MultiPart α) (h : Disjoint M.A C) :
    ∑ v in C, (mp (minsert M h)).degRes v C = 0 := 
by 
  simp only [sum_eq_zero_iff]; intro x hx;
  exact mp_int_degRes M h x hx

--- Counting edges in complete multipartite graphs:  
--- if we add in a new part C then the sum of degrees over new vertex set
--  is sum over old + 2 edges in bipartite join
-- ie 2*e(M')=2*e(M)+2*e(M,C)
theorem mp_count (M : MultiPart α) (h : Disjoint M.A C) :
    ∑ v in M.A, (mp M).degRes v M.A + 2 * M.A.card * C.card =
      ∑ v in (Turanpartition.minsert M h).A, (mp (Turanpartition.minsert M h)).degRes v (Turanpartition.minsert M h).A :=
by
  set H : SimpleGraph α := mp (minsert M h) with hH
  simp [insert_AB]; rw [sum_union h]; rw [H.degRes_add_sum' h, H.degRes_add_sum' h]
  rw [add_assoc, mp_int_sum M h, add_zero]
  rw [←add_assoc, card_eq_sum_ones C, mul_sum]; simp_rw  [hH]; 
  rw [mp_old_sum M h,add_assoc, add_right_inj,mul_one]
  rw [ H.bip_count',← sum_add_distrib]
  apply sum_congr rfl; 
  intro x hx
  rw [(by norm_num : 2 = 1 + 1), add_mul, one_mul];
  rw [mp_com M h x hx]

--- Any complete (t+1)-partite graph is (t+2)-clique free.
theorem mp_cliqueFree (M : MultiPart α) : M.t = t → M.A = univ → (mp M).CliqueFree (t + 2) :=
by
  intro ht hA; by_contra h; unfold CliqueFree at h ; push_neg at h 
  obtain ⟨S, hs1, hs2⟩ := h; rw [isClique_iff] at hs1 
  -- would now like to invoke the pigeonhole principle 
  -- have t+2 pigeons in t+1 classes so two in some class which are then non-adjacent...
  -- i did try to find this in mathlib but it was late so...
  suffices ∃ i ∈ range (M.t + 1), 1 < (S ∩ M.P i).card
  by
    obtain ⟨i, hi, hc⟩ := this; rw [one_lt_card_iff] at hc 
    obtain ⟨a, b, ha, hb, ne⟩ := hc; rw [mem_inter] at *
    have nadj := not_nbhr_same_part' hi ha.2 hb.2
    exact nadj (hs1 ha.1 hb.1 ne)
  by_contra h; push_neg at h 
  have ub : ∑ i in  (range (M.t + 1)), (S ∩ M.P i).card ≤ M.t + 1 
  · dsimp;  
    nth_rw 2 [← card_range (M.t + 1)];
    nth_rw 1 [card_eq_sum_ones]
    apply sum_le_sum h
  nth_rw 2 [ht] at ub 
  have uni := biUnion_parts M; rw [hA] at uni 
  have sin := inter_univ S; rw [uni, inter_biUnion] at sin 
  rw [← sin, card_biUnion] at hs2 ;
  apply not_succ_le_self _ (hs2 ▸ ub)
  intro x hx y hy ne
  apply disj_of_disj_inter S S (M.disj x hx y hy ne)

end Multipartite

end SimpleGraph

