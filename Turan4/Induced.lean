import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Core
import Mathlib.Algebra.BigOperators.Basic
import Turan4.Turanpartition
import Turan4.Multipartite
import Turan4.NbhdRes
import Turan4.Fedges

open Finset Nat Turanpartition

open scoped BigOperators

namespace SimpleGraph

section Ind

variable {α : Type _} (G : SimpleGraph α) [Fintype α]  [DecidableEq α]
  [DecidableRel G.Adj] 

-- I found dealing with the mathlib "induced" subgraph too painful (probably just too early in my experience of lean)
-- Graph induced by A:finset α, defined to be a simple_graph α (so all vertices outside A have empty neighborhoods)
-- this is equvialent to  "spanning_coe (induce (A:set α) G)" as we prove below.
@[reducible]
def ind (A : Finset α) : SimpleGraph α
    where
  Adj x y := G.Adj x y ∧ x ∈ A ∧ y ∈ A
  symm := by intro x y hxy; rw [adj_comm]; exact ⟨hxy.1,hxy.2.2,hxy.2.1⟩
  loopless := 
  by 
    intro x hx; apply G.loopless x hx.1

theorem ind_univ : G.ind univ = G := by ext; simp only [mem_univ, and_true_iff]

-- why is this so messy to prove? (presumably it isn't..)
-- theorem ind_eq_coe_induced (A : Finset α) : spanningCoe (induce (A : Set α) G) = G.ind A :=
-- by
--   ext;
--   simp only [map_adj, SimpleGraph.comap, Function.Embedding.coe_subtype, SetCoe.exists, mem_coe,
--     Subtype.coe_mk, exists_prop]
--   constructor; 
--   · intro ⟨a, h1, b, h2, h3, h4, h5⟩; rw [← h4, ← h5]; exact ⟨h3, h1, h2⟩
--   · intro ⟨h, h1, h2⟩; exact ⟨_, h1, _, h2, h, rfl, rfl⟩

-- induced subgraphs on disjoint sets meet in the empty graph
theorem empty_of_disjoint_ind (h : Disjoint A B) : G.ind A ⊓ G.ind B = ⊥ :=
  by
  ext u v;
  constructor;
  · intro ⟨⟨_, h1, _⟩, ⟨_, h2, _⟩⟩
    apply not_disjoint_iff.2 ⟨_, h1, h2⟩ h
  · intro hf;exfalso; apply (bot_adj  _ _ ).1 hf;

theorem empty_of_ind_comp (A : Finset α) : G.ind A ⊓ G.ind (Aᶜ) = ⊥ :=
  have : Disjoint A (Aᶜ) := disjoint_compl_right
  G.empty_of_disjoint_ind this

-- -- different parts of a multi_part induce graphs that meet in the empty graph
-- theorem empty_of_diff_parts {M : MultiPart α} (hi : i ∈ range (M.t + 1))
--     (hj : j ∈ range (M.t + 1)) (hne : i ≠ j) : G.ind (M.P i) ⊓ G.ind (M.P j) = ⊥ :=
--   G.empty_of_disjoint_ind (M.disj i hi j hj hne)

-- would like to just define the biUnion of the induced graphs directly but can't figure out how to do this.

def edgesInside (M : MultiPart α) : Finset (Sym2 α) :=
  (range (M.t + 1)).biUnion fun i => (G.ind (M.P i)).edgeFinset

def inner (M : MultiPart α) : SimpleGraph α:= ⨆ i ∈ range (M.t+1), (G.ind (M.P i))

 
-- --so counting edges inside M is same as summing of edges in induced parts (since parts are disjoint..)
-- theorem edge_mp_count :
--     (G.edgesInside M).card = ∑ i in range (M.t + 1), (G.ind (M.P i)).edgeFinset.card := 
-- by
--   apply card_biUnion; 
--   intro i hi j hj hne; rw [disjoint_edges_iff_meet_empty];
--   exact G.empty_of_diff_parts hi hj hne

-- if v w are adjacent in induced graph then they are adjacent in G
theorem ind_adj_imp : (G.ind A).Adj v w → G.Adj v w := fun h => h.1

-- if v w are adjacent in induced graph on A then they are both in A
theorem ind_adj_imp' : (G.ind A).Adj v w → v ∈ A ∧ w ∈ A := fun h => h.2

--nbhd of v ∈ A in the graph induced by A is exactly the nbhd of v restricted to A
theorem ind_nbhd_mem  : v ∈ A → (G.ind A).neighborFinset v = G.nbhdRes v A :=
by
  intro hv; unfold neighborFinset nbhdRes; ext x 
  simp_rw [Set.mem_toFinset, mem_neighborSet, and_self_iff]
  constructor; 
  · intro ha; rw [mem_inter,mem_neighborFinset]; exact ⟨ha.2.2, ha.1⟩
  · rw [mem_inter, mem_neighborFinset]; intro h; exact ⟨h.2,hv,h.1⟩

-- induced degree of  v ∈ A is deg res to A
theorem ind_deg_mem : v ∈ A → (G.ind A).degree v = G.degRes v A := 
by
  unfold degree degRes; 
  intro hv; congr; 
  exact G.ind_nbhd_mem hv

-- if v∉A then v has no neighbors in the induced graph G.ind A
theorem ind_nbhd_nmem : v ∉ A → (G.ind A).neighborFinset v = ∅ :=
by
  contrapose; push_neg; 
  intro h; obtain ⟨w, hw⟩ := Nonempty.bex (nonempty_of_ne_empty h)
  rw [mem_neighborFinset] at hw ; exact hw.2.1

-- if v∉ A then (G.ind A).degree v is zero
theorem ind_deg_nmem  : v ∉ A → (G.ind A).degree v = 0 := fun h =>
  card_eq_zero.mpr (G.ind_nbhd_nmem h)

-- so degrees of v in the induced graph are degRes v A or 0 depending on whether or not v ∈ A
theorem ind_deg : (G.ind A).degree v = ite (v ∈ A) (G.degRes v A) 0 :=
by
  unfold degree
  split_ifs with h; 
  · unfold degRes; congr; exact G.ind_nbhd_mem h
  · rw [G.ind_nbhd_nmem h]; apply card_eq_zero.mpr rfl

-- finite support of G
def fsupport : Finset α :=
  (univ :Finset α).filter fun v => 0 < G.degree v

-- member of support iff degree >0
theorem mem_fsupport (v : α) : v ∈ G.fsupport ↔ 0 < G.degree v := 
by 
  unfold fsupport;
  rw [mem_filter]; simp only [mem_univ, true_and_iff]

theorem deg_fsupport (v : α) : G.degree v = ite (v ∈ G.fsupport) (G.degree v) 0 := 
by 
  split_ifs with h;
  rfl; rw [mem_fsupport] at h ; exact Nat.eq_zero_of_nonpos _ h;

-- a vertex is in the fsupport of (G.ind A) only if it is in A
theorem mem_ind_fsupport  : v ∈ (G.ind A).fsupport → v ∈ A := 
by
  rw [(G.ind A).mem_fsupport v]; contrapose; push_neg; intro hv; rw [G.ind_deg_nmem hv]

-- so when calculating any sum of degrees over a set can restrict to fsupport
theorem deg_sum_fsupport:
    ∑ v in A, G.degree v = ∑ v in A.filter fun v => v ∈ G.fsupport, G.degree v := 
by
  rw [sum_filter]; apply sum_congr rfl; intro x _; exact G.deg_fsupport x

-- so degree sum over α in the induced subgraph is same as sum of degRes over A
-- both count 2*e(G[A])
theorem ind_deg_sum  : ∑ v, (G.ind A).degree v = ∑ v in A, G.degRes v A :=
by
  simp_rw [ind_deg]; rw [sum_ite,sum_const_zero,add_zero]; 
  congr ; ext a; 
  simp_rw [mem_filter,mem_univ,true_and]

--induced subgraph is a subgraph
theorem ind_sub (A : Finset α) : G.ind A ≤ G := fun _ _ => G.ind_adj_imp

-- internal edges induced by parts of a partition M
-- I should have defined this as G \(⋃ (G.ind M.P i)) if I 
-- could have made it work.. defining the biUnion operator for simple_graphs
-- was a step too far..
---bipartite graph induced by a finset A
@[reducible]
def bipart (A : Finset α) : SimpleGraph α
    where
  Adj v w := G.Adj v w ∧ (v ∈ A ∧ w ∉ A ∨ v ∉ A ∧ w ∈ A)
  symm := by intro x y hxy; rw [adj_comm]; tauto
  loopless := by intro x hx;exact G.loopless x hx.1
-- the bipartite graph induced by A (and Aᶜ) is the same as that induced by Aᶜ (and A = Aᶜᶜ)
theorem bipart_comp_eq_self : G.bipart A = G.bipart (Aᶜ) := 
by
  simp_rw [bipart, mem_compl, not_not, mk.injEq]
  ext x y;
  tauto

open Classical

theorem edgecard_of_disjoint {K L : SimpleGraph α}  (hkl : K ⊓ L = ⊥) :
    (K ⊔ L).edgeFinset.card = K.edgeFinset.card + L.edgeFinset.card :=
  by
  rw [edgeFinset_sup]; apply card_disjoint_union
  rw [← edgeFinset_inj, edgeFinset_bot, edgeFinset_inf] at hkl 
  apply disjoint_iff_inter_eq_empty.2 hkl


--induced subgraph on A meets bipartite induced subgraph e(A,Aᶜ) in empty graph
theorem empty_of_ind_bipart (A : Finset α) : (G.ind A ⊔ G.ind (Aᶜ)) ⊓ G.bipart A = ⊥ := 
by 
  ext;
  simp only [inf_adj, sup_adj, bot_adj, mem_compl]; tauto

-- Given A:finset α and G :simple_graph α we can partition G into G[A] G[Aᶜ] and G[A,Aᶜ]
theorem split_induced (A : Finset α) : G = G.ind A ⊔ G.ind (Aᶜ) ⊔ G.bipart A := 
by 
  ext;
  simp only [sup_adj, mem_compl]; tauto

theorem edges_ind_compl (A : Finset α) :
    (G.ind A ⊔ G.ind (Aᶜ)).edgeFinset.card =
      (G.ind A).edgeFinset.card + (G.ind (Aᶜ)).edgeFinset.card :=
  by
  have hd := G.empty_of_ind_comp A
  rw [← edgeFinset_inj, edgeFinset_bot, edgeFinset_inf] at hd 
  rw [edgeFinset_sup]
  apply card_disjoint_union
  apply disjoint_iff_inter_eq_empty.2 hd

--- Edge counting: e(G[A])+e(G[Aᶜ])+e(G[A,Aᶜ])=e(G)
theorem edges_split_induced' (A : Finset α) :
    (G.ind A).edgeFinset.card + (G.ind (Aᶜ)).edgeFinset.card + (G.bipart A).edgeFinset.card =
      (G.ind A ⊔ G.ind (Aᶜ) ⊔ G.bipart A).edgeFinset.card :=
by
  have hd := G.empty_of_ind_bipart A
  rw [← edges_ind_compl]
  rw [← edgeFinset_inj, edgeFinset_bot, edgeFinset_inf] at hd 
  simp_rw [edgeFinset_sup] at *
  symm
  apply card_disjoint_union
  apply disjoint_iff_inter_eq_empty.2 hd

theorem edges_split_induced (A : Finset α) :
    (G.ind A).edgeFinset.card + (G.ind (Aᶜ)).edgeFinset.card + (G.bipart A).edgeFinset.card =
      G.edgeFinset.card :=
by
  rw [edges_split_induced']
  congr 1
  rw [edgeFinset_inj]
  exact (G.split_induced A).symm

-- v w adjacent in the bipartite graph given by A iff adj in bipartite graph given by Aᶜ (since they are the same graph..)
theorem bipart_comp_adj_iff : (G.bipart A).Adj v w ↔ (G.bipart (Aᶜ)).Adj v w := 
by 
  constructor
  · intro ⟨h1,h2⟩;  refine ⟨h1,?_⟩
    cases h2 with
    | inl h => 
      right; rwa [not_mem_compl,mem_compl] 
    | inr h => 
      left; rwa [mem_compl,not_mem_compl] 
  · intro ⟨h1,h2⟩;  refine ⟨h1,?_⟩
    cases h2 with
    | inl h => 
      right; rwa [mem_compl,not_mem_compl] at h
    | inr h => 
      left; rwa [not_mem_compl,mem_compl] at h
   
  

-- nbhd of v ∈ A in the bipartite graph is the nbhd of v in G restricted to Aᶜ
theorem nbhd_bipart_mem (h : v ∈ A) :
    (G.bipart A).neighborFinset v = G.nbhdRes v (Aᶜ) := 
by 
  ext a;
  rw [mem_res_nbhd_iff, mem_neighborFinset, mem_neighborFinset,bipart,mem_compl];
  dsimp;
  constructor
  · intro ⟨ha,hb⟩
    cases hb with
    | inl hb => exact ⟨hb.2,ha⟩
    | inr hb => exfalso; exact hb.1 h          
  · intro ⟨ha,hb⟩
    refine ⟨hb,?_⟩
    left; exact ⟨h,ha⟩

-- hence degree is degRes v to Aᶜ
theorem deg_bipart_mem (h : v ∈ A) :
    (G.bipart A).degree v = G.degRes v (Aᶜ) :=
by
  unfold degree degRes
  rwa [nbhd_bipart_mem]

-- nbhd of v ∉ A in the bipartite graph is the nbhd of v in G restricted to A
theorem nbhd_bipart_not_mem (h : v ∉ A) :
    (G.bipart A).neighborFinset v = G.nbhdRes v A := 
by 
  ext a;
  rw [mem_res_nbhd_iff, mem_neighborFinset,mem_neighborFinset]; 
  constructor
  · intro ⟨ha,hb⟩
    cases hb with
    | inl hb => exfalso; exact h hb.1  
    | inr hb => exact ⟨hb.2,ha⟩
  · intro ⟨ha,hb⟩
    refine ⟨hb,?_⟩
    right; exact ⟨h,ha⟩

-- if v∉ A then in the bipartite graph deg v is the degRes to A
theorem deg_bipart_not_mem (h : v ∉ A) :
    (G.bipart A).degree v = G.degRes v A := 
by 
  unfold degree degRes; rwa [nbhd_bipart_not_mem]

-- degree of v ∈ A is degree in induced + degree in bipartite (ie count neighbour in A and Aᶜ)
theorem deg_eq_ind_add_bipart : ∀ v ∈ A, G.degree v = (G.ind A).degree v + (G.bipart A).degree v :=
by
  intro v hv; rw [G.deg_bipart_mem hv,G.ind_deg_mem hv, ← G.degRes_univ]
  exact G.degRes_add_sub (subset_univ A)

--ite to count edges from A to Aᶜ
theorem bipart_sum_ite :
    ∑ v in A, (G.bipart A).degree v = ∑ v in A, ∑ w in Aᶜ, ite (G.Adj v w) 1 0 :=
by
  apply sum_congr rfl; 
  intro x hx; 
  rw [G.deg_bipart_mem hx, degRes_ones, nbhdRes_filter, sum_filter];

-- sum of degrees over each part are equal in any induced bipartite graph
theorem bipart_sum_eq :
    ∑ v in A, (G.bipart A).degree v = ∑ v in Aᶜ, (G.bipart A).degree v :=
by
  rw [G.bipart_sum_ite, sum_comm]; 
  apply sum_congr rfl; intro x hx;
  rw [sum_ite,sum_const_zero,add_zero,degree,card_eq_sum_ones]
  apply sum_congr _ (fun _ _ => rfl)
  ext a
  rw [mem_neighborFinset,mem_filter,adj_comm];
  rw [compl_eq_univ_sdiff, mem_sdiff] at hx; 
  tauto

-- hence sum of degrees over one part counts edges once
theorem sum_deg_bipart_eq_edge_card  :
    ∑ v in A, (G.bipart A).degree v = (G.bipart A).edgeFinset.card :=
by
  apply (mul_right_inj' zero_lt_two.ne.symm).mp; rw [← sum_degrees_eq_twice_card_edges]
  rw [two_mul]; nth_rw 1 [G.bipart_sum_eq]
  rw [compl_eq_univ_sdiff]; symm
  have : Disjoint (univ \ A) A := sdiff_disjoint
  rw [← sum_union this, sdiff_union_of_subset (subset_univ A)]

--- in the induced graph only need to sum over A to count all edges twice
theorem sum_degrees_ind_eq_twice_card_edges :
    ∑ v in A, (G.ind A).degree v = 2 * (G.ind A).edgeFinset.card :=
by
  rw [← sum_degrees_eq_twice_card_edges, ind_deg_sum]; 
  apply sum_congr rfl
  intro _ hx; exact G.ind_deg_mem hx

-- sum of degrees in A = twice number of edges in A + number of edges from A to Aᶜ
theorem sum_deg_ind_bipart :
    ∑ v in A, G.degree v = 2 * (G.ind A).edgeFinset.card + (G.bipart A).edgeFinset.card :=
by
  rw [← sum_degrees_ind_eq_twice_card_edges, ← sum_deg_bipart_eq_edge_card,← sum_add_distrib]
  apply sum_congr rfl; 
  intro x hx; rw [G.deg_eq_ind_add_bipart x hx]

-- any nbhd is contained in the fsupport
theorem nbhd_sub_fsupport (v : α) : G.neighborFinset v ⊆ G.fsupport :=
by
  intro x; rw [mem_neighborFinset, mem_fsupport, degree, card_pos]
  rw [adj_comm, ← mem_neighborFinset]; 
  intro hx; exact ⟨v,hx⟩

-- should have been one line (on finsets not graphs) but couldn't find it: A ⊆ B → Aᶜ ∩ B = B\A
theorem comp_nbhd_int_supp_eq_sdiff (v : α) :
    (G.neighborFinset v)ᶜ ∩ G.fsupport = G.fsupport \ G.neighborFinset v := 
by
  rw [sdiff_eq, inter_comm]; rfl

-- Bound on max degree gives bound on edges of G in the following form:
--(Note this almost gives Mantel's theorem since in a K_3-free graph nbhds are independent)
theorem sum_deg_ind_max_nbhd (hm : G.degree v = G.maxDegree)
    (hA : A = (G.neighborFinset v)ᶜ) :
    2 * (G.ind A).edgeFinset.card + (G.bipart A).edgeFinset.card ≤
      ((G.fsupport).card - G.maxDegree) * G.maxDegree :=
by
  rw [← G.sum_deg_ind_bipart, G.deg_sum_fsupport, ← hm, degree]
  rw [sum_filter, sum_ite, sum_const, smul_zero, add_zero, ← card_sdiff (G.nbhd_sub_fsupport v)]
  nth_rw 1 [card_eq_sum_ones]; rw [sum_mul, one_mul]
  rw [hA]; rw [filter_mem_eq_inter, G.comp_nbhd_int_supp_eq_sdiff v]
  apply sum_le_sum; rw [← degree, hm]; intro x _; exact G.degree_le_maxDegree x

-- The essential bound for Furedi's result: 
-- e(G) + e(G[Γ(v)ᶜ]) ≤ (G.fsupport.card - Δ(G))*Δ(G) + e(G[Γ(v)])
theorem edge_bound_max_deg (hm : G.degree v = G.maxDegree)
    (hA : A = (G.neighborFinset v)ᶜ) :
    G.edgeFinset.card + (G.ind A).edgeFinset.card ≤
      ((G.fsupport).card - G.maxDegree) * G.maxDegree + (G.ind (Aᶜ)).edgeFinset.card :=
by 
  rw [add_comm, ← G.edges_split_induced A, add_assoc,add_comm ((G.ind (Aᶜ)).edgeFinset.card)];
  simp_rw [←add_assoc,←two_mul]; 
  apply add_le_add_right (G.sum_deg_ind_max_nbhd hm hA); 


-- any "actual" clique consists of vertices in the support
theorem clique_sub_fsupport (ht : 2 ≤ t) (h : G.IsNClique t S) :
    S ⊆ G.fsupport := by
  intro a ha; rw [isNClique_iff] at h ; have : 1 < S.card := (h.2 ▸ ht)
  obtain ⟨b, hb, hne⟩ := exists_ne_of_one_lt_card this a
  rw [← mem_coe] at *; have hadj := h.1 hb ha hne; rw [mem_coe]; rw [← mem_neighborFinset] at hadj 
  exact (G.nbhd_sub_fsupport b) hadj

-- any t+2 clique of an induced graph is a subset of the induced set
theorem clique_ind_sub_ind (h : 2 ≤ t) : (G.ind A).IsNClique t S → S ⊆ A := 
by
  intro h1 a ha; 
  exact G.mem_ind_fsupport <| (G.ind A).clique_sub_fsupport h h1 ha

-- if S a t-clique in a nbhd Γ(v) then inserting v gives a (t+1)-clique
theorem clique_insert_nbhr (hc : G.IsNClique t S)
    (hd : S ⊆ G.neighborFinset v) : G.IsNClique (t + 1) (insert v S) :=
by
  rw [isNClique_iff] at *; rw [← hc.2];
  have vnin : v ∉ S := by apply Set.not_mem_subset hd (G.not_mem_nbhd v)
  rw [isClique_iff] at *; refine' ⟨_, card_insert_of_not_mem vnin⟩; rw [coe_insert]
  refine Set.Pairwise.insert hc.1 ?_; 
  intro b hb _;
  rw [G.adj_comm b v, and_self_iff, ← mem_neighborFinset]; exact hd hb

-- Now the other key lemma for Furedi's result:
-- If G is K_{t+3}-free then any nbhd induces a K_{t+2}-free graph
-- (Could replace t by t-1 below, since G K_2 free → nbhds all empty → graphs induced by nbhds empty → they are K_1 -free )
-- theorem cliqueFree_nbhd_ind :
--     G.CliqueFree (t + 3) → (G.ind (G.neighborFinset v)).CliqueFree (t + 2) :=
--   by
--   contrapose; unfold CliqueFree; push_neg; rintro ⟨S, hs⟩; use insert v S
--   have :=
--     G.clique_insert_nbhr ⟨IsClique.mono (G.ind_sub (G.neighborFinset v)) hs.1, hs.2⟩
--       (G.clique_ind_sub_ind (Nat.le_add_left _ _) hs)
--   rwa [(by rfl : 3 = 2 + 1), ← add_assoc]

@[reducible]
def biUnion (M : MultiPart α) : SimpleGraph α
    where
  Adj v w := ∃ i ∈ range (M.t + 1), (G.ind (M.P i)).Adj v w
  symm := 
  by
    intro x y ⟨i,hxy⟩
    exact ⟨i,hxy.1,hxy.2.symm⟩
  loopless := 
  by 
    intro x ⟨i,hx⟩
    exfalso; apply ne_of_adj
    exact hx.2; rfl

@[reducible]
def disJoin (M : MultiPart α) : SimpleGraph α
    where
  Adj v w := G.Adj v w ∧ ∃ i ∈ range (M.t + 1), v ∈ M.P i ∧ w ∈ M.P i
  symm := 
  by
    intro x y ⟨hxy,i,hi⟩
    refine ⟨hxy.symm,i,hi.1,hi.2.2,hi.2.1⟩ 
  loopless :=
  by
    intro x ⟨hx,_⟩
    exfalso; apply ne_of_adj
    exact hx; rfl

-- the two versions of "union of induced disjoint parts" are the same
theorem biUnion_eq_disJoin_sum (M : MultiPart α) : G.biUnion M = G.disJoin M :=
  by
  ext; simp_rw [mem_range, exists_prop]; 
  constructor
  · intro ⟨i, hi, ad, hx, hy⟩; exact ⟨ad, i, hi, hx, hy⟩;
  · intro ⟨ad, i, hi, hx, hy⟩; exact ⟨i, hi, ad, hx, hy⟩

-- -- edges inside M are the same as the edgeFinset of biUnion M
-- theorem edgesInside_eq (M : MultiPart α) : (G.biUnion M).edgeFinset = G.edgesInside M :=
-- by
--   unfold edgesInside; ext a; simp only [mem_edgeFinset, mem_biUnion, mem_range, exists_prop]
--   unfold biUnion; 
-- --  simp only [mem_range,exists_prop] 
--   constructor
--   · intro h1
--     dsimp at h1

--     rw [mem_edgeSet] at h1
--     sorry
--   · sorry
-- --  on_goal 1 => cases a; dsimp at *; simp only [mem_range, exists_prop] at *; rfl; rfl

-- this is a subgraph of G
theorem disJoin_sub (M : MultiPart α) : G.disJoin M ≤ G := fun _ _ h => h.1

-- G with the internal edges removed is G ⊓ (mp M)
theorem sdiff_with_int (h : M.A = univ) : G \ G.disJoin M = G ⊓ mp M :=
by
  ext (x y); dsimp
  have hx : x ∈ M.A := by rw [h]; exact mem_univ x
  have hy : y ∈ M.A := by rw [h]; exact mem_univ y
  obtain ⟨i, hi, hx1⟩ := inv_part hx
  obtain ⟨j, hj, hy1⟩ := inv_part hy
  constructor;
  · intro ⟨hadj, h2⟩; refine ⟨hadj, ?_⟩; push_neg at h2; push_neg at h2 
    specialize h2 hadj i hi hx1
    apply mp_imp_adj hi hj hx1 hy1 
    intro ne; rw [ne] at h2 ; exact h2 hy1
  · intro ⟨hadj, h2⟩; refine ⟨hadj, ?_⟩; push_neg;push_neg; 
    intro _ i hi hx hy
    exact not_nbhr_same_part hi hx h2 hy

-- G is the join of the edges induced by the parts and those in the complete 
-- multipartite graph M on α
theorem self_eq_disJoin_ext_mp (h : M.A = univ) : G = G.disJoin M ⊔ G ⊓ mp M := 
by
  rw [← G.sdiff_with_int h, sup_sdiff_self_right, right_eq_sup]; 
  exact G.disJoin_sub M

-- Given M and v,w vertices with v ∈ M.P i and w ∈ M.A then v,w are adjacent in 
-- the "internal induced subgraph"  iff they are adjacent in the graph induced on M.P i
theorem disJoin_edge_help:
    i ∈ range (M.t + 1) → v ∈ M.P i → w ∈ M.A → ((G.disJoin M).Adj v w ↔ (G.ind (M.P i)).Adj v w) :=
by
  intro hi hv hw; obtain ⟨j, hj, hw⟩ := inv_part hw; dsimp
  by_cases i = j;
  · constructor; · intro h1; rw [← h] at hw ; exact ⟨h1.1, hv, hw⟩
    · intro h1;  exact ⟨h1.1, i, hi, h1.2⟩
  · constructor;
    · intro h1; 
      exfalso; obtain ⟨k, hkr, hk⟩:= h1.2
      have ieqk := uniq_part hi hkr hv hk.1; 
      have jeqk := uniq_part hj hkr hw hk.2
      rw [← jeqk] at ieqk ; exact h ieqk
    · intro h1; exfalso; exact uniq_part' hi hj h h1.2.2 hw

--same as above but for degrees and assuming M covers all of α
theorem disJoin_edge_help' (h : M.A = univ) :
    i ∈ range (M.t + 1) → v ∈ M.P i → (G.disJoin M).degree v = (G.ind (M.P i)).degree v :=
by
  intro hi hv; unfold degree; 
  apply congr_arg _; ext a
  have := mem_univ a; rw [← h] at this ; 
  have := G.disJoin_edge_help hi hv this
  rwa [mem_neighborFinset, mem_neighborFinset]

-- so sum of degrees in internal subgraph is sum over induced subgraphs on parts of sum of degrees
theorem disJoin_deg_sum (h : M.A = univ) :
    ∑ v, (G.disJoin M).degree v = ∑ i in range (M.t + 1), ∑ v, (G.ind (M.P i)).degree v :=
by
  rw [← h]; nth_rw 1 [biUnion_parts M]
  rw [sum_biUnion (pair_disjoint M)]
  apply sum_congr rfl 
  intro i hi; rw [sdiff_part hi,sum_union sdiff_disjoint]
  have : ∑ x in M.A \ M.P i, (G.ind (M.P i)).degree x = 0 := 
  by 
    apply sum_eq_zero; intro x hx;
    rw [mem_sdiff] at hx ; exact G.ind_deg_nmem hx.2
  rw [this,zero_add]; 
  apply sum_congr rfl 
  intro x hx; apply (G.disJoin_edge_help' h) hi hx;
  

-- number of edges in the subgraph induced inside all parts is the sum of those induced in each part
theorem disJoin_edge_sum (h : M.A = univ) :
    (G.disJoin M).edgeFinset.card = ∑ i in range (M.t + 1), (G.ind (M.P i)).edgeFinset.card :=
by
  apply (mul_right_inj' zero_lt_two.ne.symm).mp; 
  simp_rw [mul_sum,← sum_degrees_eq_twice_card_edges]; 
  exact G.disJoin_deg_sum h

--counting edges in induced parts is (almost) the same as summing restricted degrees...
theorem ind_edge_count : ∑ v in A, G.degRes v A = 2 * (G.ind A).edgeFinset.card := by
  rw [← sum_degrees_eq_twice_card_edges, G.ind_deg_sum]
end Ind

end SimpleGraph

