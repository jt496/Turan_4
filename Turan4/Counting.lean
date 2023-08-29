import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Core
import Mathlib.Algebra.BigOperators.Basic
import Turan4.Fedges
import Turan4.NbhdRes
import Turan4.CliqueFreeSets
import Turan4.MiscFinset
import Turan4.Multipartite
import Turan4.Turanpartition
import Turan4.Induced

open Finset Nat Turanpartition

open scoped BigOperators

namespace SimpleGraph

variable {α : Type _} {G : SimpleGraph α} [Fintype α]  [DecidableEq α]
  [DecidableRel G.Adj]

---for any (t+2)-clique free set there is a partition into B, a (t+1)-clique free set and A\B 
-- such that e(A)+e(A\B) ≤ e(B) + |B|(|A|-|B|)
theorem furedi_help :
    ∀ A : Finset α,
      G.CliqueFreeSet A (t + 2) →
        ∃ B : Finset α,
          B ⊆ A ∧
            G.CliqueFreeSet B (t + 1) ∧
              ∑ v in A, G.degRes v A + ∑ v in A \ B, G.degRes v (A \ B) ≤
                ∑ v in B, G.degRes v B + 2 * B.card * (A \ B).card :=
by
  cases Nat.eq_zero_or_pos t with
  | inl ht =>  -- t = 0 need to check that ∅ is not a 1-clique. 
    intro A hA; rw [ht,zero_add] at *; 
    refine ⟨∅, ⟨empty_subset A, G.clique_free_empty zero_lt_one, ?_⟩⟩
    rw [sdiff_empty, card_empty, mul_zero, zero_mul, sum_empty, zero_add, G.two_clique_free_sum hA, zero_add]
  | inr ht => -- 0 < t
    intro A hA; 
    by_cases hnem : A.Nonempty;
    · obtain ⟨x, hxA, hxM⟩ := G.exists_max_res_deg_vertex hnem
      -- get a vert x of max res deg in A
      set hBA := G.sub_res_nbhd_A x A
      set B := G.nbhdRes x A with hB
      -- Let B be the res nbhd of the vertex x of max deg_A
      refine' ⟨B, ⟨hBA, G.t_clique_free hA hxA, _⟩⟩
      rw [G.degRes_add_sum hBA, G.sum_sdf hBA B, add_assoc]
      rw [G.sum_sdf hBA (A \ B), G.bip_count hBA, ← G.degRes_add_sum hBA]
      simp_rw [← hB]; rw [add_assoc]; --ring_nf
      apply add_le_add_left --(∑ v in G.nbhdRes x A, G.degRes v (G.nbhdRes x A))
      rw [add_comm]; simp_rw [add_assoc,←hB]; rw [add_comm (∑ x in A \ B, degRes G x (A \ B))]
      rw [← G.degRes_add_sum hBA]; ring_nf; --rw [← mul_assoc]
      apply mul_le_mul' _ _
      · apply (G.maxDegRes_sum_le (sdiff_subset A B)).trans _
        rw [hxM, degRes]
      · rfl  
    · rw [not_nonempty_iff_eq_empty] at hnem 
      refine ⟨∅, ⟨empty_subset A, G.clique_free_empty (succ_pos _), ?_⟩⟩
      rw [sdiff_empty, card_empty, mul_zero, zero_mul, hnem, sum_empty]


-- Putting together the deg counts of G induced on a larger partition (M with C inserted).
-- Counting degrees sums over the parts of the larger partition is what you expect
-- ie e(G[M_0])+ .. +e(G[M_t])+e(G[C]) = e(G[M'_0])+...+e(G[M'_{t+1}])

theorem internal_count (h : Disjoint M.A C) :
    ∑ i in range (M.t + 1), ∑ v in M.P i, G.degRes v (M.P i) + ∑ v in C, G.degRes v C =
      ∑ i in range ((Turanpartition.minsert M h).t + 1), 
        ∑ v in (Turanpartition.minsert M h).P i, G.degRes v ((Turanpartition.minsert M h).P i) :=
by
  simp_rw [insert_t,sum_range_succ _ (M.t+1), insert_P, ite_not]
  apply (add_left_inj _).mpr; 
  apply sum_congr rfl; intro k hk; 
  have kne := Nat.ne_of_lt (mem_range.1 hk)
  apply sum_congr
  · split_ifs with h; 
    · contradiction; 
    · rfl;
  · intro v _; split_ifs with h; 
    · contradiction; 
    · rfl

-- Furedi's stability theorem: (t+2)-clique-free set A implies there is a (t+1)-partition of A
-- such that edges in A + edges in parts (counted a second time) ≤ edges in the complete
-- (t+1)-partite graph on same partition
-- implies Turan once we have know how to maximize edges of a complete multi-partite graph
theorem furedi :
    ∀ {A : Finset α},
      G.CliqueFreeSet A (t + 2) →
        ∃ M : MultiPart α,
          M.A = A ∧
            M.t = t ∧
              ∑ v in A, G.degRes v A + ∑ i in range (M.t + 1), ∑ v in M.P i, G.degRes v (M.P i) ≤
                ∑ v in A, (mp M).degRes v A :=
by
  induction t with
  | zero => 
    --rw [zero_add]
    intro A ha; use defaultM A 0; refine' ⟨rfl, rfl, _⟩; rw [G.two_clique_free_sum ha]
    rw [zero_add]; unfold defaultM; dsimp; 
    simp only [zero_add, range_one, sum_singleton, ite_true]; 
    apply sum_le_sum
    intro x hx; rw [G.two_clique_free ha x hx];dsimp; exact _root_.zero_le _
  --- t.succ case
  | succ t  ht => 
    intro A ha; obtain ⟨B, hBa, hBc, hBs⟩ := G.furedi_help A ha
    have hAsd := union_sdiff_of_subset hBa
    obtain ⟨M, Ma, Mt, Ms⟩ := ht hBc
    have dAB : Disjoint M.A (A \ B) := by rw [Ma]; exact disjoint_sdiff
    set H : SimpleGraph α := mp (minsert M dAB)
    use minsert M dAB; 
    refine ⟨?_, ?_, ?_⟩; 
    · rw [insert_AB, Ma]; exact union_sdiff_of_subset hBa
    · rw [insert_t, Mt];
    · --- so we now have the new partition and "just" need to check the degree sum bound..
      have mpc := mp_count M dAB; 
      rw [insert_AB, Ma, hAsd] at mpc 
      -- need to sort out the sum over parts in the larger graph
      rw [← mpc, ← G.internal_count dAB]; 
      linarith

end SimpleGraph

