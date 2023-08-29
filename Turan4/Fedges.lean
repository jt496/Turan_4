import Mathlib.Data.Nat.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.Core
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Turan4.MiscFinset
import Turan4.CliqueFreeSets

open Finset Nat
namespace SimpleGraph

-- extremal graph theory studies finite graphs and we do a lot of counting so I naively thought I should 
-- prove some lemmas about (sub)graphs and edgeFinsets..
-- main new def below "G.is_far H s" if by deleting at most s edges from G we obtain a subgraph of H
section Fedges

variable {α : Type _} [Fintype α]  [DecidableEq α] {G H : SimpleGraph α}
  [DecidableRel G.Adj] [DecidableRel H.Adj]

-- G is a subgraph of H iff G.edgeFinset is subset of H.edgeFinset
theorem subgraph_edge_subset : G ≤ H ↔ G.edgeFinset ⊆ H.edgeFinset :=
by
  exact Iff.symm edgeFinset_subset_edgeFinset

-- graphs (on same vertex set) are equal iff edgeFinsets are equal
theorem eq_iff_edges_eq : G = H ↔ G.edgeFinset = H.edgeFinset :=
  edgeFinset_inj.symm

-- if G=H (finite) graph they have the same number of edges..
theorem eq_imp_edges_card_eq : G = H → G.edgeFinset.card = H.edgeFinset.card :=
by
  intro h
  rw [eq_iff_edges_eq.mp h]

-- a subgraph of the same size or larger is the same graph (... everything is finite)
theorem edge_eq_sub_imp_eq (hs : G ≤ H) (hc : H.edgeFinset.card ≤ G.edgeFinset.card) : G = H :=
  eq_iff_edges_eq.mpr (Finset.eq_of_subset_of_card_le (subgraph_edge_subset.mp hs) hc)

-- -- the empty graph has no edges
-- theorem empty_has_no_edges : (⊥ : SimpleGraph α).edgeFinset = ∅ := edgeFinset_bot

-- a graph is the empty graph iff it has no edges
theorem empty_iff_edge_empty : G = ⊥ ↔ G.edgeFinset = ∅ :=
by
  rw [← edgeFinset_inj,edgeFinset_bot]

-- if G is not the empty graph there exist a pair of distinct adjacent vertices
theorem edge_of_not_empty : G ≠ ⊥ → ∃ v : α, ∃ w : α, v ≠ w ∧ G.Adj v w :=
by
  contrapose; intro h; push_neg at h ; push_neg; ext x x_1; rw [bot_adj]; specialize h x x_1
  by_cases h' : x = x_1; simp only [h,h', G.irrefl]; have := h h'; tauto

-- if G is 2-clique free then it is empty
theorem two_cliqueFree_imp_empty : G.CliqueFree 2 → G = ⊥ :=
by
  intro h; contrapose h;
  obtain ⟨v, w, had⟩ := edge_of_not_empty h
  intro hf; apply hf _ (adj_is2Clique had.2)

-- edge sets are disjoint iff meet is empty graph
theorem disjoint_edges_iff_meet_empty : Disjoint G.edgeFinset H.edgeFinset ↔ G ⊓ H = ⊥ :=
by
  rw [disjoint_iff,← edgeFinset_inj,edgeFinset_inf,inf_eq_inter,edgeFinset_bot,bot_eq_empty];

--if G and H meet in ⊥ then the card of their edge sets adds
theorem card_edges_add_of_meet_empty :
    G ⊓ H = ⊥ → (G ⊔ H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := 
by
  rw [← disjoint_edges_iff_meet_empty,edgeFinset_sup];
  intro h; exact card_disjoint_union h

-- the subgraph formed by deleting edges (from edgeFinset)
def delFedges (G : SimpleGraph α) (S : Finset (Sym2 α)) : SimpleGraph α
    where
  Adj := λ x y => G.Adj x y \ Sym2.ToRel S x y
  symm a b := by simp only [Sym2.toRel_prop, mem_coe, adj_comm, Sym2.eq_swap, imp_self]
  loopless a := 
  by
    intro ha;apply G.loopless a ;exact ha.1

--deleting all the edges in H from G is G\H
theorem delFedges_is_sdiff (G H : SimpleGraph α) [DecidableRel H.Adj] : G.delFedges H.edgeFinset = G \ H :=
by
  ext u v;
  simp only [delFedges, sdiff_adj, Set.coe_toFinset,  Sym2.toRel_prop, mem_edgeSet]
  rfl

-- now introduce a simple version of distance between graphs 
-- G.is_far s H iff there exists a finset S of at most s edges such that G-S is a subgraph of H
def IsFar (G H : SimpleGraph α) (s : ℕ) :=
  ∃ S : Finset (Sym2 α), G.delFedges S ≤ H ∧ S.card ≤ s

theorem isFar_le (G H : SimpleGraph α) (h : s ≤ t) : G.IsFar H s → G.IsFar H t := 
by 
  intro h1; obtain ⟨S, hS1, hS2⟩ := h1;
  exact ⟨S, hS1, hS2.trans h⟩

theorem isFar_trivial (G H : SimpleGraph α) (s : ℕ) [DecidableRel G.Adj] :
    G.edgeFinset.card ≤ s → G.IsFar H s := 
by
  intro h; refine ⟨G.edgeFinset, ?_, h⟩; 
  rw [delFedges_is_sdiff,_root_.sdiff_self];
  exact bot_le

end Fedges

end SimpleGraph

