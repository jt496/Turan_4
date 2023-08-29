import Turan4.Counting

open Finset Nat Turanpartition
local notation "‖" x "‖" => Fintype.card x
local notation "|" x "|" => Finset.card x
open scoped BigOperators

namespace SimpleGraph


variable {α : Type _} {G: SimpleGraph α} [Fintype α][DecidableEq α] [DecidableRel G.Adj] 
/-
# Furedi stability result (no counting):

If G is K_{t+2}-free with vertex set α then there is a (t+1)-partition M of α
 such that the e(G)+ ∑ i< t+1, e(G[M_i]) ≤ e(complete_multipartite M)

# Turan's theorem 

 Together with an upper bound on the number of edges in any complete multipartite graph 
 Furedi's result easily implies Turan with equality iff G is a complete multipartite graph on a 
 turan partition (ie. a Turan graph)

  def turan_numb : ℕ → ℕ → ℕ:=
  begin
    intros t n,
    set a:= n/(t+1),--- size of a small part
    set b:= n%(t+1),-- number of large parts
    exact (a^2)*nat.choose(t+1-b)(2)+a*(a+1)*b*(t+1-b)+((a+1)^2)*nat.choose(b)(2)
  end
  
#eval turan_numb 1 11  -- = 5*6 = 30        K_3-free bipartite
#eval turan_numb 2 12  -- = 3*(4*4) = 48    K_4-free tri-partite
#eval turan_numb 5 23  -- = 5*(4*3) +(5 choose 2)*(4*4) = 60+160 = 220 --  K_7-free 6-partite 


# Furedi with counting: 
If G is K_{t+2}-free and is close to extremal in size then G is close to (t+1)-partite. 

-/
theorem furedi_stability :
    G.CliqueFree (t + 2) →
      ∃ M : MultiPart α,
        M.t = t ∧
          M.A = univ ∧
            G.edgeFinset.card + ∑ i in range (t + 1), (G.ind (M.P i)).edgeFinset.card ≤
              (mp M).edgeFinset.card :=
by
  intro h; obtain ⟨M, hA, ht, hs⟩ := furedi (cliqueFree_graph_imp_set h univ)
  refine' ⟨M, ht, hA, _⟩; 
  apply (mul_le_mul_left (by norm_num : 0 < 2)).mp; rw [mul_add, mul_sum];
  simp only [degRes_univ] at hs 
  rw [← G.sum_degrees_eq_twice_card_edges, ← (mp M).sum_degrees_eq_twice_card_edges]
  apply le_trans _ hs; apply add_le_add_left; apply le_of_eq; apply sum_congr; rw [ht]
  intro i _; rw [← ind_edge_count]

-- So we have e(G)+edges internal to the partiton ≤ edges of complete (t+1)-partite M
theorem furedi_stability' :
    G.CliqueFree (t + 2) →
      ∃ M : MultiPart α,
        M.t = t ∧
          M.A = univ ∧ G.edgeFinset.card + (G.disJoin M).edgeFinset.card ≤ (mp M).edgeFinset.card :=
  by
  intro h; obtain ⟨M, ht, hu, hle⟩ := furedi_stability h; rw [← ht] at hle ;
  rw [← G.disJoin_edge_sum hu] at hle 
  exact ⟨M, ht, hu, hle⟩

--Now deduce Turan's theorem without worring about case of equality yet
theorem turan : G.CliqueFree (t + 2) → G.edgeFinset.card ≤ turanNumb t (Fintype.card α) :=
by
  intro h; obtain ⟨M, ht, hA, hc⟩ := furedi_stability h
  have := turan_max_edges M hA; rw [ht] at this 
  apply (le_of_add_le_left hc).trans this

-- Uniqueness? 
---There are three places where G can fail to achieve equality in Furedi's stability theorem
-- 1) there are "internal" edges, ie edges inside a part of the (t+1)-partition  (counted in the LHS)
-- 2) the partition can fail to be balanced (and hence #edgesof mp M < turan_numb)
-- 3) the multipartite induced graph G ⊓ (mp M) may not be complete 
-- Clearly for equality in Furedi-Turan hybrid ie LHS of Furedi with RHS of Turan
-- need M is a balanced partition and G is multipartite (ie no internal edges)
-- can then prove in this case G ≤ (mp M) = T and hence G = T for equality.   
--Now deduce case of equality in Turan's theorem

theorem turan_equality :
    G.CliqueFree (t + 2) ∧ G.edgeFinset.card = turanNumb t (Fintype.card α) ↔
      ∃ M : MultiPart α, M.t = t ∧ M.A = univ ∧ TuranPartition M ∧ G = mp M :=
by
  constructor;
  · intro h; obtain ⟨M, ht, hu, hle⟩ := furedi_stability' h.1; rw [h.2] at hle 
    refine ⟨M, ht, hu, ?_⟩; 
    have tm := turan_max_edges M hu
    rw [ht] at tm 
    have inz : (G.disJoin M).edgeFinset.card = 0 
    · apply eq_zero_of_le_zero
      by_contra h; push_neg at h;
      apply lt_irrefl (turanNumb t (Fintype.card α))
      apply lt_of_lt_of_le (lt_add_of_pos_right _ h) (hle.trans tm)
    rw [inz,add_zero] at hle
    rw [card_eq_zero] at inz 
    have inem : G.disJoin M = ⊥ := empty_iff_edge_empty.mpr inz
    have dec := G.self_eq_disJoin_ext_mp hu; rw [inem] at dec ;
    rw [bot_sup_eq, left_eq_inf] at dec 
    have ieq : (mp M).edgeFinset.card = turanNumb t (Fintype.card α):= le_antisymm tm hle 
    rw [← ht] at ieq 
    refine ⟨turan_eq_imp M hu ieq, ?_⟩; rw [← h.2] at tm 
    exact edge_eq_sub_imp_eq dec tm
  · intro h; obtain ⟨M, ht, hu, iM, hG⟩ := h
    have hc := mp_cliqueFree M ht hu
    have ieq := turan_imm_imp_eq M hu ht iM; rw [← hG] at hc 
    refine ⟨hc, ?_⟩
    rw [← ieq];
    exact eq_imp_edges_card_eq hG

-- The usual version of Furedi's stability theorem says:
-- if G is (K_t+2)-free and has (turan numb - s) edges
-- then we can make G (t+1)-partite by deleting at most s edges
theorem furedi_stability_count :
    G.CliqueFree (t + 2) →
      G.edgeFinset.card = turanNumb t (Fintype.card α) - s →
        ∃ M : MultiPart α, M.t = t ∧ M.A = univ ∧ G.IsFar (mp M) s :=
by
  intro h1 h2;
  obtain ⟨M, ht, hA, hle⟩ := furedi_stability' h1
  refine ⟨M, ht, hA, ?_⟩; rw [h2] at hle 
  have tm := turan_max_edges M hA; rw [ht] at tm 
  by_cases hs : s ≤ turanNumb t (Fintype.card α);
  · have ic : (G.disJoin M).edgeFinset.card ≤ s
    · by_contra hc; push_neg at hc
      change succ _ ≤ _ at hc 
      obtain ⟨a,ha⟩:=exists_add_of_le hc
      rw [ha,← add_assoc,succ_eq_add_one,←  add_assoc] at hle
      rw [tsub_add_cancel_of_le hs,succ_add] at hle
      apply lt_irrefl (edgeFinset (mp M)).card
      apply lt_of_le_of_lt tm
      apply lt_of_le_of_lt (Nat.le_add_right _ a) <| lt_of_succ_le hle
    refine ⟨(G.disJoin M).edgeFinset, ?_, ic⟩
    rw [G.delFedges_is_sdiff (G.disJoin M)];
    · rw [G.sdiff_with_int hA]
      · intro v w hvw; exact hvw.2         
  · have : G.edgeFinset.card ≤ s 
    · push_neg at hs; rw [h2]
      apply (lt_of_le_of_lt tsub_le_self hs).le
    exact G.isFar_trivial (mp M) s this

end SimpleGraph

