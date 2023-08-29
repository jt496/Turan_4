import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Core
import Mathlib.Algebra.BigOperators.Basic
import Turan4.NbhdRes

open Finset Nat

open scoped BigOperators

namespace SimpleGraph

section CliqueFreeSets


variable {α : Type _} {G : SimpleGraph α} [Fintype α]  [DecidableEq α] [DecidableRel G.Adj]

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (B «expr ⊆ » A) -/
-- restricted nbhd is the part of nbhd in A
-- we will need the concept of a clique-free set of vertices in a graph rather than just clique-free graphs
-- A is a t-clique-free set of vertices in G

lemma pair_subset {A : Finset α} (hv: v ∈ A) (hw: w ∈ A) : {v,w} ⊆ A:=
by 
  intro x ; rw [mem_insert,mem_singleton];
  intro h;
  cases h with
  | inl h => exact h ▸ hv
  | inr h => exact h ▸ hw

lemma adj_is2Clique  (h: G.Adj a b) : G.IsNClique 2 {a, b} := 
by
  rw [isNClique_iff, coe_insert, coe_singleton, isClique_iff, Set.pairwise_pair_of_symmetric G.symm]
  exact ⟨fun _ => h, card_eq_two.2 ⟨a,b,G.ne_of_adj h,rfl⟩⟩

def CliqueFreeSet (A : Finset α) (s : ℕ) : Prop :=
  ∀ (B: Finset α), B ⊆ A → ¬G.IsNClique s B

--clique-free if too small
theorem clique_free_card_lt (h : A.card < s) : G.CliqueFreeSet A s :=
by
  rw [CliqueFreeSet]; intro B hB; rw [isNClique_iff]; 
  push_neg; intro
  exact _root_.ne_of_lt (lt_of_le_of_lt (card_le_of_subset hB) h)

--clique-free of empty (unless s=0)
theorem clique_free_empty (h : 0 < s) : G.CliqueFreeSet ∅ s := 
by 
  rw [← Finset.card_empty] at h ; exact G.clique_free_card_lt h

-- if G has no s-clique then nor does any subset
theorem cliqueFree_graph_imp_set  (h : G.CliqueFree s) (U: Finset α): G.CliqueFreeSet U s :=
by
  revert h; contrapose
  rw [CliqueFreeSet]; push_neg; intro h; rw [CliqueFree]; push_neg
  obtain ⟨B, _, h2⟩ := h; exact ⟨B, h2⟩

-- base case for Erdos/Furedi proof:
-- if A has no 2-clique then restricted degrees are all zero 
-- i.e. A is an independent set
theorem two_clique_free (hA : G.CliqueFreeSet A 2) : ∀ v ∈ A, G.degRes v A = 0 :=
by
  intro v hv; rw [degRes, card_eq_zero]
  contrapose hA
  obtain ⟨w, hw⟩ := exists_mem_nempty G hA
  rw [CliqueFreeSet]; push_neg
  exact ⟨{v, w}, pair_subset hv hw.1, adj_is2Clique hw.2⟩; 

-- sum of degRes over an independent set (2-clique-free set) is 0
-- e (G.ind A)=0
theorem two_clique_free_sum (hA : G.CliqueFreeSet A 2) :
    ∑ v in A, G.degRes v A = 0 :=
  sum_eq_zero (G.two_clique_free hA)


--- If we add a vertex to a subset of its nbhd that is a clique we get a new (bigger) clique
lemma isClique_insert (hv: v ∈ A) (hB : B ⊆ G.nbhdRes v A) (h: IsClique G B):  IsClique G (insert v B) :=
by
  intro x hx y hy hne
  cases hx with
  | inl hx => 
    cases hy with
    | inl hy => rw [hx,hy] at hne; contradiction
    | inr hy => 
      rw [hx]; 
      apply G.subset_res_nbhd hB hy
  | inr hx => 
    cases hy with
    | inl hy => 
      rw [hy, G.adj_comm]
      apply G.subset_res_nbhd hB hx
    | inr hy => exact h hx hy hne

--- If we add a vertex to a subset of its nbhd that is a t-clique we get a (t+1)-clique
lemma isSuccClique (hv: v ∈ A) (hB : B ⊆ G.nbhdRes v A) (h: IsNClique G t B): IsNClique G (t+1) (insert v B):=
by
  constructor
  · rw [coe_insert]
    exact isClique_insert hv hB h.1
  · rw [card_insert_of_not_mem,add_left_inj,h.2]
    apply not_mem_mono hB (G.not_mem_res_nbhd v A)   

-- if A set is (t+2)-clique-free then any member vertex 
-- has restricted nbhd that is (t+1)-clique-free 
-- (just prove for any simple_graph α if  G is (t+2)-clique free then so is any nbhd of a vertex in G
-- then can apply it to G.ind A etc...
theorem t_clique_free (hA : G.CliqueFreeSet A (t + 2)) (hv : v ∈ A) :
    G.CliqueFreeSet (G.nbhdRes v A) (t + 1) :=
by
  rw [CliqueFreeSet] at *
  intro B hB; contrapose! hA
  refine ⟨insert v B,?_, isSuccClique hv hB hA⟩;
  exact insert_subset hv (subset_trans hB (G.sub_res_nbhd_A v A))
  
 
end CliqueFreeSets

end SimpleGraph

