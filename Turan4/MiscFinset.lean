import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Core

open Finset

-- just some lemmas that I couldn't quite find in finset.basic
variable {α : Type _} [DecidableEq α]

--probably easier ways of doing this...
--if A and B are disjoint then seo are A ∩ C and B ∩ D for any C,D
theorem disj_of_inter_disj (C D : Finset α) (h : Disjoint A B) :
    Disjoint (A ∩ C) (B ∩ D) :=
  Disjoint.mono (le_iff_subset.mpr (inter_subset_left A C)) (inter_subset_left B D) h

--if A and B are disjoint then seo are C ∩ A and D ∩ B for any C,D
theorem disj_of_disj_inter (C D : Finset α)  (h : Disjoint A B) :
    Disjoint (C ∩ A) (D ∩ B) :=
  Disjoint.mono (le_iff_subset.mpr (inter_subset_right C A)) (inter_subset_right D B) h

-- in particular (B ∩ C) and (A\B ∩ C) are disjoint
theorem sdiff_inter_disj (A B C : Finset α) : Disjoint (B ∩ C) (A \ B ∩ C) :=
  disj_of_inter_disj C C disjoint_sdiff


