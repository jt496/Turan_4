import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Core
import Mathlib.Algebra.BigOperators.Basic
import Turan4.MiscFinset

open Finset Nat

open scoped BigOperators

namespace SimpleGraph

-- When counting edges in graphs we often want to consider subgraphs induced by a set of vertices
-- or subgraphs between two (possibly disjoint) sets of vertices 
-- For this purpose we introduce the restricted neighbourhood a vertex to a finset.
-- this is G.nbhdRes v A = A ∩ G.neighborFinset v
-- the restricted nbhd of a set of vertices
section NbhdRes

variable {α : Type _} (G : SimpleGraph α) [Fintype α]  [DecidableEq α] [DecidableRel G.Adj]

-- restricted nbhd is the part of nbhd in A

def nbhdRes (v : α) (A : Finset α) : Finset α :=
  A ∩ G.neighborFinset v

lemma nbhdRes_filter (v : α) (A : Finset α) : G.nbhdRes v A = A.filter (fun x ↦ G.Adj v x):=
by
  ext x; rw [nbhdRes,mem_inter,mem_filter,mem_neighborFinset]

-- restriction of degree to A
def degRes (v : α) (A : Finset α) : ℕ :=
  (G.nbhdRes v A).card


-- restricting to univ is no restriction at all
theorem degRes_univ (v : α) : G.degRes v univ = G.degree v := 
by 
  rw [degRes, degree]; congr;
  rw [nbhdRes, univ_inter]

-- we only define this over A restricted to A (could be broader)
-- max deg res is zero if A is empty
-- could replace this with (G.ind A).max_degree
def maxDegRes (A : Finset α) : ℕ :=
  Option.getD (A.image fun v => G.degRes v A).max 0

-- if A.Nonempty then there is a vertex of maxDegRes A
theorem exists_max_res_deg_vertex (hA : A.Nonempty) :
    ∃ v ∈ A, G.maxDegRes A = G.degRes v A :=
by
  obtain ⟨t, ht⟩ := max_of_nonempty (Nonempty.image hA (fun v => G.degRes v A))
  obtain ⟨a, ha1, ha2⟩:=mem_image.1 (mem_of_max ht)
  refine ⟨a, ha1,?_⟩
  rw [maxDegRes,ht,ha2]
  rfl
  
-- The maxDegRes over A is at least the degRes of any particular vertex in A.
theorem degRes_le_maxDegRes (hvA : v ∈ A) : G.degRes v A ≤ G.maxDegRes A :=
by
  obtain ⟨t, ht⟩ := Finset.max_of_mem (mem_image_of_mem (fun v => G.degRes v A) hvA)
  have := mem_image_of_mem (fun v => G.degRes v A) hvA
  have := Finset.le_max_of_eq this ht
  rwa [maxDegRes, ht]

-- bound on sum of degRes given max degRes (also a bound on e(C) for C ⊆ A)
-- or equiv if C ⊆ A then 2*e(G[C])+e(G[C,A\C])≤ (G.ind A).max_degree * |C|
theorem maxDegRes_sum_le (hC : C ⊆ A) :
    ∑ v in C, G.degRes v A ≤ G.maxDegRes A * C.card :=
  by
  rw [card_eq_sum_ones, mul_sum, mul_one]
  apply sum_le_sum _; intro i hi; exact G.degRes_le_maxDegRes (hC hi)

-- restricted degree to A is sum of ones over each neighbour of v in A
theorem degRes_ones (v : α) (A : Finset α) : G.degRes v A = ∑ x in G.nbhdRes v A, 1 :=
  card_eq_sum_ones _

--- if the restricted nbhd is non-empty then v has a neighbor in A
theorem exists_mem_nempty (hA : ¬G.nbhdRes v A = ∅) : ∃ w ∈ A, G.Adj v w :=
  by
  rw [nbhdRes] at hA ; contrapose! hA
  rw [eq_empty_iff_forall_not_mem]
  intro x hx; rw [mem_inter, mem_neighborFinset] at hx 
  exact hA x hx.1 hx.2

-- member of the restricted nhd iff in nbhd and in A
theorem mem_res_nbhd_iff (v w : α) (A : Finset α) :
    w ∈ G.nbhdRes v A ↔ w ∈ A ∧ w ∈ G.neighborFinset v := 
by 
  rw [nbhdRes, mem_inter]

lemma subset_res_nbhd (h: B ⊆ G.nbhdRes v A) (hb: b ∈ B): G.Adj v b:=
by
  exact (mem_neighborFinset _ _ _).1 ((G.mem_res_nbhd_iff _ _ _).1 (h hb)).2  

-- v is not a neighbor of itself
theorem not_mem_nbhd (v : α) : v ∉ G.neighborFinset v := 
by 
  rw [mem_neighborFinset];
  exact G.loopless v

-- nor is v a restricted neighbor of itself
theorem not_mem_res_nbhd (v : α) (A : Finset α) : v ∉ G.nbhdRes v A := 
by 
  rw [mem_res_nbhd_iff];
  push_neg; intro _; exact G.not_mem_nbhd v

-- restricted nbhd is contained in A
theorem sub_res_nbhd_A (v : α) (A : Finset α) : G.nbhdRes v A ⊆ A := 
by 
  intro x; rw [mem_res_nbhd_iff];
  intro h; exact h.1

-- -- restricted nbhd of member is stictly contained in A
-- theorem ssub_res_nbhd_of_mem  (h : v ∈ A) : G.nbhdRes v A ⊂ A :=
--   (ssubset_iff_of_subset (G.sub_res_nbhd_A v A)).mpr ⟨v, h, G.not_mem_res_nbhd v A⟩

-- -- restricted nbhd contained in nbhd
-- theorem sub_res_nbhd_N (v : α) (A : Finset α) : G.nbhdRes v A ⊆ G.neighborFinset v := 
-- by 
--   intro;
--   rw [mem_res_nbhd_iff]; intro h; exact h.2

-- restricted degree additive over partition of A into B ∪ A\B
-- this is daft, it would work for any function defined on A
theorem sum_sdf  (hB : B ⊆ A) (C : Finset α) :
    ∑ v in A, G.degRes v C = ∑ v in B, G.degRes v C + ∑ v in A \ B, G.degRes v C := 
by
  nth_rw 1 [← union_sdiff_of_subset hB]; exact sum_union disjoint_sdiff

-- restricted deg over A = restricted deg over B + restricted deg over A\B
theorem degRes_add_sub (hB : B ⊆ A) :
    G.degRes v A = G.degRes v B + G.degRes v (A \ B) :=
by
  simp_rw [degRes, nbhdRes]; nth_rw 1 [← union_sdiff_of_subset hB]
  rw [inter_distrib_right B (A \ B) _]
  exact card_disjoint_union (sdiff_inter_disj A B _)

-- sum version of previous lemma
theorem degRes_add_sum {A B C : Finset α} (hB : B ⊆ A) :
    ∑ v in C, G.degRes v A = ∑ v in C, G.degRes v B + ∑ v in C, G.degRes v (A \ B) := by
  rw [← sum_add_distrib]; exact sum_congr rfl fun _ _ => G.degRes_add_sub hB

-- if A and B are disjoint then for any vertex v the degRes add
theorem degRes_add' (h : Disjoint A B) :
    G.degRes v (A ∪ B) = G.degRes v A + G.degRes v B :=
by
  rw [degRes, nbhdRes,inter_distrib_right]
  exact card_disjoint_union (disj_of_inter_disj _ _ h)

-- sum version of previous lemma
theorem degRes_add_sum' (h : Disjoint A B) :
    ∑ v in C, G.degRes v (A ∪ B) = ∑ v in C, G.degRes v A + ∑ v in C, G.degRes v B := 
by
  rw [← sum_add_distrib]; exact sum_congr rfl fun _ _ => G.degRes_add' h

-- counting edges exiting B via ite helper, really just counting edges in e(B,A\B)
theorem bip_count_help (A B : Finset α)  :
    ∑ v in B, G.degRes v (A \ B) = ∑ v in B, ∑ w in A \ B, ite (G.Adj v w) 1 0 :=
by
  simp only [degRes_ones]; congr; ext x;
  simp only [sum_const, Algebra.id.smul_eq_mul, mul_one, sum_boole, cast_id]
  congr; ext; rw [mem_res_nbhd_iff, mem_filter, mem_neighborFinset]

-- edges from B to A\B equals edges from A\B to B
theorem bip_count (hB : B ⊆ A) :
    ∑ v in B, G.degRes v (A \ B) = ∑ v in A \ B, G.degRes v B :=
by
  rw [G.bip_count_help]
  have := _root_.sdiff_sdiff_eq_self hB
  nth_rw 4 [←this ]
  rw [G.bip_count_help, this, sum_comm]
  congr; ext y; congr; ext x
  split_ifs with h1 h2 h3; 
  · rfl
  · rw [adj_comm] at h1
    exact h2 h1
  · rw [adj_comm] at h1
    exact h1 h3
  · rfl

-- same but between any pair of disjoint sets rather tha B⊆A and A\B
theorem bip_count_help' :
    ∑ v in B, G.degRes v A = ∑ v in B, ∑ w in A, ite (G.Adj v w) 1 0 :=
by
  simp_rw [degRes_ones]; congr; ext x;
  rw [nbhdRes_filter,sum_filter]

-- edges from A to B (disjoint) equals edges from B to A
theorem bip_count'  :
    ∑ v in B, G.degRes v A = ∑ v in A, G.degRes v B :=
by
  rw [G.bip_count_help' ]; rw [G.bip_count_help']; rw [sum_comm]; congr
  ext y; congr; ext x
  split_ifs with h1 h2 h3; 
  · rfl
  · rw [adj_comm] at h1
    exact h2 h1
  · rw [adj_comm] at h1
    exact h1 h3
  · rfl


-- sum of res_res_deg ≤ sum of res_deg
theorem sum_res_le (hB : B ⊆ A)  :
    ∑ v in C, G.degRes v B ≤ ∑ v in C, G.degRes v A :=
  by
  apply sum_le_sum _
  intro i _
  rw [degRes, degRes]; apply card_le_of_subset _
  intro x hx; rw [mem_res_nbhd_iff] at *
  exact ⟨hB hx.1, hx.2⟩

end NbhdRes



end SimpleGraph

