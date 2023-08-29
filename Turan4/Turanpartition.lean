import Mathlib.Data.Finset.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring

open Finset Nat

open scoped BigOperators

--------------------------------------------------------------------------
--- Define turan numbers. 
--- 
--- Since the Turan problem asks for the maximum number of edges in a K_t-free graph of order n
--  We don't care about t = 0 or t = 1  
--  so we define turan_numb t n to be what most people would call turan (t+1) n
--  eg turan 0 n is the max size (number of edges) in a K_2 free graph
--  Turan's theorem says that this is the number of edges in a balanced complete (t+1)-partite graph
-- 
-- Main definitions below: ...
namespace Turanpartition

--classical Turan numbers
def turanNumb : ℕ → ℕ → ℕ := 
λ t n =>  
    (n / (t + 1)) ^ 2 * Nat.choose (t + 1 - (n % (t + 1))) 2 + 
    (n / (t + 1)) * ((n / (t + 1)) + 1) * (n % (t + 1)) * (t + 1 - (n % (t + 1))) + 
    ((n / (t + 1)) + 1) ^ 2 * Nat.choose (n % (t + 1)) 2
--  let a := n / (t + 1)
  --- size of a small part
 -- let b := n % (t + 1)
  -- number of large parts


@[simp]
lemma tN : 
turanNumb t n = (n / (t + 1)) ^ 2 * Nat.choose (t + 1 - (n % (t + 1))) 2 + (n / (t + 1)) * ((n / (t + 1)) + 1) * (n % (t + 1)) * (t + 1 - (n % (t + 1))) + ((n / (t + 1)) + 1) ^ 2 * Nat.choose (n % (t + 1)) 2:=rfl


--complement is often easier to deal with and we also multiply by 2 to convert edges to degree sum
-- so 2*(turan_numb t n) = n^2 - (turan_numb'  t n)
def turanNumb' : ℕ → ℕ → ℕ := 
λ t n =>
  (t + 1 - ( n % (t + 1))) * (n / (t + 1)) ^ 2 + (n % (t + 1)) * ((n / (t + 1)) + 1) ^ 2
  


lemma tN' : turanNumb' t n = (t + 1 - ( n % (t + 1))) * (n / (t + 1)) ^ 2 + (n % (t + 1)) * ((n / (t + 1)) + 1) ^ 2:=rfl


-- choose two simplification
theorem two (a : ℕ) : 2 * Nat.choose a 2 = a * (a - 1) :=
by
  induction a with
  | zero => rfl
  | succ n ih => 
    cases n with
    | zero => rfl
    | succ n =>
      rw [Nat.choose,Nat.choose_one_right,mul_add,ih]
      rw [succ_sub_succ_eq_sub,tsub_zero,mul_comm _ n,← add_mul];
      congr; rw [add_comm]


-- square simp
theorem square (b c : ℕ) : (b + c) ^ 2 = b ^ 2 + 2 * b * c + c ^ 2 := 
by 
  rw [pow_two,add_mul, mul_add,mul_add,pow_two,pow_two,mul_comm c,two_mul,add_mul,add_assoc,add_assoc,add_assoc]



-- this is a mess but it works
theorem tn_turanNumb' (t n : ℕ) : turanNumb' t n + 2 * turanNumb t n = n^2 :=
by 
  rw [tN,tN']
  have t1 : t + 1 - 1 = t := tsub_eq_of_eq_add rfl
  have n1 := div_add_mod n (t + 1)
  have n2 := mod_lt n (succ_pos t); 
  rw [succ_eq_add_one] at n2 
  have n3 : t + 1 - n % (t + 1) + n % (t + 1) = t + 1 := tsub_add_cancel_of_le (le_of_lt n2)
  set a := n / (t + 1); 
  set b := n % (t + 1) with hb
  cases Nat.eq_zero_or_pos n with
  | inl hn =>
    rw [hn] at hb n1 ⊢
    rw [Nat.zero_mod] at hb
    rw [hb] at n3 n1 ⊢
    simp_rw [tsub_zero,hn,Nat.choose_zero_succ,Nat.zero_div,zero_mul,mul_zero,add_zero,zero_pow' ,zero_mul,mul_zero]      
  | inr hn =>
    cases Nat.eq_zero_or_pos b with
    | inl hb' => 
      rw [hb', tsub_zero,mul_add,mul_add,zero_mul,←mul_assoc 2,mul_comm 2 (a^2),
          mul_assoc,two,t1,mul_zero, zero_mul,mul_zero,add_zero,add_zero,Nat.choose_zero_succ,mul_zero,mul_zero,add_zero]; 
      rw [hb',add_zero] at n1
      rw [←n1,mul_pow,mul_comm (a^2),←add_mul]
      nth_rw 1 [←mul_one (t+1)]; rw [←mul_add,add_comm 1,←pow_two]
    |inr hb' =>
      rw [← n3, add_mul] at n1 ; nth_rw 3 [← mul_one b] at n1 ; rw [add_assoc, ← mul_add b] at n1 
      rw [← n1]; rw [mul_add, mul_add, ← mul_assoc 2, ← mul_assoc 2 ((a + 1) ^ 2)]
      nth_rw 1 [mul_comm 2 _]; 
      rw [mul_assoc, two,mul_comm 2 ((a+1)^2),mul_assoc ((a+1)^2) 2,two, square ((t + 1 - b) * a) (b * (a + 1)),
        mul_comm _ (a ^ 2)]
      set c := t + 1 - b; 
      have hc2 : c - 1 + 1 = c := tsub_add_cancel_of_le (tsub_pos_of_lt n2)
      have hb2 : b - 1 + 1 = b := tsub_add_cancel_of_le hb'
      rw [add_comm (a^2*c),add_assoc,←add_assoc (a^2*c),←add_assoc (a^2*c),← mul_add (a^2)]
      nth_rw 1 [←mul_one c,←mul_add c,add_comm _ (c-1),hc2]
      rw [add_comm (b*(a+1)^2),add_assoc,mul_comm b ((a+1)^2),←mul_add ((a+1)^2)]
      nth_rw 4 [←mul_one b]; 
      rw[←mul_add b,hb2,-- ring will work from here... since there is no subtraction
        mul_comm c a,mul_pow,←pow_two c,add_assoc,add_assoc,
        add_right_inj,mul_pow,mul_add,pow_two,mul_add,mul_one,add_mul,mul_one,pow_two,mul_add,add_mul,
        add_mul,add_mul,add_mul,one_mul,mul_one,add_mul,one_mul,mul_add,mul_add,mul_add,mul_add,mul_add,mul_one,
        ← add_assoc,← add_assoc,← add_assoc,← add_assoc,←add_assoc,add_left_inj,mul_comm a (b*b),add_left_inj,
        ←add_assoc,add_left_inj,mul_comm (b*b), add_left_inj,mul_assoc 2 _ b,mul_assoc a c b,mul_comm c b,
        ←mul_assoc a,add_left_inj,mul_assoc 2,mul_assoc,mul_assoc,mul_assoc,mul_comm b a,mul_comm c,mul_assoc]

--sum of degrees in a turan graph
theorem tn_turanNumb'_2 (t n : ℕ) : 2 * turanNumb t n = n ^ 2 - turanNumb' t n := 
by
  rw [← tn_turanNumb' t n]; 
  exact (add_tsub_cancel_left _ _).symm

-- start with some helper functions that don't need partitions to be defined.
-- here P : ℕ → ℕ plays the role of sizes of parts in a (t+1)-partition 
-- sum of part sizes i.e number of vertices
def psum (t : ℕ) (P : ℕ → ℕ) : ℕ :=
  ∑ i in range (t + 1), P i

-- sum of squares of part sizes (basically 2*edges in complement of corresponding complete multipartite graph)
def sumSq (t : ℕ) (P : ℕ → ℕ) : ℕ :=
  ∑ i in range (t + 1), P i ^ 2

-- inevitable mod (t+1) calculation related to sizes of parts in balanced partition
theorem mod_tplus1  (hc : c ≤ t) (hd : d ≤ t)
    (ht : (t + 1) * a + c = (t + 1) * b + d) : a = b ∧ c = d :=
by
  have mc : c % (t + 1) = c := mod_eq_of_lt (succ_le_succ hc ) 
  have md : d % (t + 1) = d := mod_eq_of_lt (succ_le_succ hd)
  rw [add_comm, add_comm _ d] at ht 
  have hmtl : (c + (t + 1) * a) % (t + 1) = c % (t + 1) := add_mul_mod_self_left c (t + 1) a
  have hmtr : (d + (t + 1) * b) % (t + 1) = d % (t + 1) := add_mul_mod_self_left d (t + 1) b
  rw [mc,ht] at hmtl ; rw [md,hmtl] at hmtr 
  refine' ⟨_, hmtr⟩; rw [hmtr] at ht 
  rw [add_right_inj, mul_eq_mul_left_iff] at ht
  cases ht with
  | inl h => exact h
  | inr h => contradiction

---can this be used to simplify the previous lemma ?
theorem mod_tplus1'  : (t + 1) * (n / (t + 1)) + n % (t + 1) = n :=
  div_add_mod n (t + 1)

-- now lots of  results about balanced partitions
-- these are partitions whose parts differ by at most 1
-- a balanced (t+1) partition is one with almost equal parts
def Balanced (t : ℕ) (P : ℕ → ℕ) : Prop :=
  ∀ i ∈ range (t + 1), ∀ j ∈ range (t + 1), P i ≤ P j + 1

-- smallest part is well-defined
def minP (t : ℕ) (P : ℕ → ℕ) : ℕ :=
  have nem : ((range (t + 1)).image fun i => P i).Nonempty :=
    (Nonempty.image_iff _).mpr nonempty_range_succ
  min' ((range (t + 1)).image fun i => P i) nem

-- indices of small parts
def smallParts (h : Balanced t P) : Finset ℕ :=
  (range (t + 1)).filter fun i => P i = minP t P

-- .. and large parts
def largeParts (h : Balanced t P) : Finset ℕ :=
  (range (t + 1)).filter fun i => P i = minP t P + 1

-- there is a smallest part
theorem small_nonempty (h : Balanced t P) : (smallParts h).Nonempty :=
  by
  rw [smallParts];
  have nem : ((range (t + 1)).image fun i => P i).Nonempty :=
    (Nonempty.image_iff _).mpr nonempty_range_succ
  set a : ℕ := min' ((range (t + 1)).image fun i => P i) nem with ha
  have ain := min'_mem ((range (t + 1)).image fun i => P i) nem
  rw [← ha, mem_image] at ain 
  obtain ⟨k, hk1, hk2⟩ := ain; use k; rw [mem_filter]
  refine' ⟨hk1, _⟩; rw [ha] at hk2 ; exact hk2

-- in a balanced partition all parts are small or large
theorem con_sum (h : Balanced t P) :
    ∀ i ∈ range (t + 1), P i = minP t P ∨ P i = minP t P + 1 :=
  by
  unfold Balanced at h 
  have nem : ((range (t + 1)).image fun i => P i).Nonempty :=
    (Nonempty.image_iff _).mpr nonempty_range_succ
  set a : ℕ := min' ((range (t + 1)).image fun i => P i) nem with ha
  set b : ℕ := max' ((range (t + 1)).image fun i => P i) nem with hb
  intro i hi
  have ale : a ≤ P i := min'_le ((range (t + 1)).image fun i => P i) (P i) (mem_image_of_mem P hi)
  have leb : P i ≤ b := le_max' ((range (t + 1)).image fun i => P i) (P i) (mem_image_of_mem P hi)
  have ain := min'_mem ((range (t + 1)).image fun i => P i) nem; rw [← ha] at ain 
  have bin := max'_mem ((range (t + 1)).image fun i => P i) nem; rw [← hb] at bin 
  have blea : b ≤ a + 1 := by
    rw [mem_image] at *
    obtain ⟨k, hk, hak⟩ := ain; obtain ⟨l, hl, hbl⟩ := bin
    rw [← hak, ← hbl]; exact h l hl k hk
  have ple := le_trans leb blea
  by_contra h; push_neg at h ; 
  have h1 := lt_of_le_of_ne ale h.1.symm
  have h2 := lt_of_le_of_ne ple h.2; 
  apply lt_irrefl (a+1); exact lt_of_le_of_lt h1 h2

-- large parts are those that aren't small
theorem large_parts' (h : Balanced t P) :
    largeParts h = (range (t + 1)).filter fun i => ¬P i = minP t P :=
by
  have := con_sum h; 
  unfold largeParts; 
  ext a; rw [mem_filter, mem_filter]; 
  constructor
  · intro h'; refine' ⟨h'.1, _⟩; intro h2; rw [h2] at h' ; exact succ_ne_self (minP t P) h'.2.symm
  · intro h'; refine' ⟨h'.1, _⟩; 
    specialize this a h'.1; 
    cases this with
    | inl h => 
      exfalso; exact h'.2 h
    | inr h => exact h

-- parts cannot be both small and large
theorem parts_disjoint (h : Balanced t P) :
    Disjoint (smallParts h) (largeParts h) :=
  by
  convert disjoint_filter_filter_neg (range (t + 1)) (range (t + 1)) fun i => P i = minP t P
  exact large_parts' h

-- all parts are either small or large
theorem parts_union (h : Balanced t P) :
    range (t + 1) = smallParts h ∪ largeParts h :=
  by
  have := con_sum h
  ext a; unfold smallParts; unfold largeParts; rw [mem_union]; 
  constructor
  · intro ha
    rw [mem_filter, mem_filter]; specialize this a ha; 
    cases this with
    | inl h => 
      left; exact ⟨ha,h⟩
    | inr h => 
      right; exact ⟨ha, h⟩
  · rw [mem_filter, mem_filter]; 
    intro hr; 
    cases hr with
    | inl h => exact h.1
    | inr h => exact h.1

-- so the number of small parts + large parts = t+1
theorem parts_card_add (h : Balanced t P) :
    (smallParts h).card + (largeParts h).card = t + 1 := by
  rw [← card_range (t + 1), parts_union h, card_disjoint_union (parts_disjoint h)]

-- not all parts are large since there is at least one small part
theorem largeParts_card (h : Balanced t P) : (largeParts h).card ≤ t :=
by
  have := Nat.add_le_add (card_pos.mpr (small_nonempty h)) (le_refl (card (largeParts h))) 
  rw [parts_card_add h,add_comm] at this
  apply  le_of_add_le_add_right this
  

-- number of small parts is (t+1) - number of large
theorem smallParts_card (h : Balanced t P) :
    (smallParts h).card = t + 1 - (largeParts h).card := 
by 
  rw [← parts_card_add h,add_tsub_cancel_right]

-- any sum of a function over a balanced partition is easy to compute
theorem bal_sum_f (h : Balanced t P) (f : ℕ → ℕ) :
    ∑ i in range (t + 1), f (P i) =
      (smallParts h).card * f (minP t P) + (largeParts h).card * f (minP t P + 1) :=
  by
  rw [parts_union h, sum_union (parts_disjoint h)]; congr
  · rw [card_eq_sum_ones, sum_mul, one_mul]; apply sum_congr; rfl; rw [smallParts]; intro x;
    rw [mem_filter]; intro hx; rw [hx.2]
  · rw [card_eq_sum_ones, sum_mul, one_mul]; apply sum_congr; rfl; rw [largeParts]; intro x;
    rw [mem_filter]; intro hx; rw [hx.2]

-- simple equation for sum of parts
theorem bal_sum (h : Balanced t P) :
    psum t P = (smallParts h).card * minP t P + (largeParts h).card * (minP t P + 1) :=
  bal_sum_f h fun i => i

-- alternative version of previous lemma
theorem bal_sum' (h : Balanced t P) :
    psum t P = (t + 1) * minP t P + (largeParts h).card := by
  rw [bal_sum h, mul_add, mul_one, ← add_assoc, ← add_mul, parts_card_add h]

--now thinking about balanced (t+1)-partitions whose parts sum to n
-- a balanced partition that sums to n
def Bal (t n : ℕ) (P : ℕ → ℕ) : Prop :=
  Balanced t P ∧ psum t P = n

-- given a balanced partition of n into (t+1)-parts the small part is n/(t+1) and there are n%(t+1) large parts
theorem bal_sum_n  (hb : Bal t n P) :
    minP t P = n / (t + 1) ∧ (largeParts hb.1).card = n % (t + 1) :=
  by
  unfold Bal at hb ; cases' hb with hb1 hb2
  rw [bal_sum' hb1, ← div_add_mod n (t + 1)] at hb2 ;
  exact mod_tplus1 (largeParts_card hb1) (le_of_lt_succ (mod_lt n (succ_pos t))) hb2

-- sum of a function f over parts of a balanced partition  of n into (t+1) parts is:
theorem bal_sum_n_f  (hb : Bal t n P) (f : ℕ → ℕ) :
    ∑ i in range (t + 1), f (P i) =
      (t + 1 - n % (t + 1)) * f (n / (t + 1)) + n % (t + 1) * f (n / (t + 1) + 1) :=
  by
  unfold Bal at hb 
  obtain hf := bal_sum_f hb.1; obtain ⟨mn, ln⟩ := bal_sum_n hb
  specialize hf f; rwa [mn, smallParts_card, ln] at hf 

-- sum of squares of balanced partition is turan_numb'
theorem bal_turan_help (hb : Bal t n P) : sumSq t P = turanNumb' t n := by
  rw [tN',sumSq,bal_sum_n_f hb fun i => i ^ 2]

--so given two balanced (t+1) partitions summing to n their sum_sq  agree
theorem bal_turan_help' (hp : Bal t n P) (hq : Bal t n Q) :
    sumSq t P = sumSq t Q := by rw [bal_turan_help hp]; rw [bal_turan_help hq]

--hence sum_sq + 2* turan number is n^2
theorem bal_turan_bd (hp : Bal t n P) :
    sumSq t P + 2 * turanNumb t n = n ^ 2 := by rw [bal_turan_help hp]; exact tn_turanNumb' t n

--- introduce the partitions we use to build complete multipartite graphs
-- this is a partition of A:finset α into t+1 parts each of which is a finset α
variable {α : Type _} [Fintype α] [DecidableEq α]

@[ext]
structure MultiPart (α : Type _) [DecidableEq α] [Fintype α] where
  t : ℕ -- the number of parts is t + 1
  P : ℕ → Finset α -- the mapping to parts
  A : Finset α -- the set covered by the parts
  uni : A = (range (t + 1)).biUnion fun i => P i -- the fact that the union of parts is A
  disj : ∀ i ∈ range (t + 1), ∀ j ∈ range (t + 1), i ≠ j → Disjoint (P i) (P j) -- the parts are disjoint



--TO DO rewrite constructors for multi_part using this for "move" and set.pairwise_disjoint.insert for "insert"
theorem disjoint_insert_erase {A : Finset α}  (hd : Disjoint A B) :
    Disjoint (A.erase v) (insert v B) :=
  by
  rw [disjoint_insert_right, mem_erase]
  refine ⟨?_, disjoint_of_subset_left (erase_subset v A) hd⟩
  · push_neg; intro h; contradiction

-- def PartsTA (t : ℕ) (A : Finset α) (M : MultiPart α) : Prop :=
--   M.t = t ∧ M.A = A

-- -- given M with M.t+1 parts and partition sets P we have P' M is the corresponding sizes of parts
-- def nump (M : MultiPart α) : ℕ → ℕ := fun i => (M.P i).card

--sum of squares of part sizes useful for counting edges in complete multitpartite graph on M
def sumSqC (M : MultiPart α) : ℕ :=
  ∑ i in range (M.t + 1), card (M.P i) ^ 2


-- a partition is moveable if the part sizes are unbalanced
def Moveable (M : MultiPart α) : Prop :=
  ¬Balanced M.t (λ i => (M.P i).card)

--- ie. turan_partition means the sizes of parts is such that it is balanced
def TuranPartition (M : MultiPart α) : Prop :=
  ∀ i ∈ range (M.t + 1), ∀ j ∈ range (M.t + 1), (M.P i).card ≤ (M.P j).card + 1

-- no vertex can be moved between parts of a TuranPartition to increase the number of edges in the complete 
-- (t+1)-partite graph defined by M
theorem turanPartition_iff_not_moveable (M : MultiPart α) : TuranPartition M ↔ ¬Moveable M := 
by
  rw [Moveable, not_not] ; rfl

-- if a partition is not a turan_partition then we can find two parts and a vertex to move from one to the other
theorem not_turanPartition_imp {M : MultiPart α} (h : ¬TuranPartition M) :
    ∃ i ∈ range (M.t + 1),
      ∃ j ∈ range (M.t + 1), ∃ v ∈ M.P i, j ≠ i ∧ (M.P j).card + 1 < (M.P i).card :=
by
  rw [turanPartition_iff_not_moveable,  Moveable, Balanced] at h ;
  push_neg at h 
  obtain ⟨i, hi, j, hj, hc⟩ := h;
  refine ⟨i,hi,j,hj,?_⟩ 
  obtain ⟨v,hv⟩:= card_pos.1 <| pos_of_gt hc
  have cne :=((lt_succ_self _).trans hc).ne.symm 
  refine ⟨v, hv, λ eq => ?_, hc⟩; 
  rw [eq] at cne; contradiction

---there is a partition
instance (α : Type _) [DecidableEq α] [Fintype α]  [DecidableEq α] :
    Inhabited (MultiPart α)
    where default :=
    { t := 0
      P := fun _ => ∅
      A := ∅
      uni := rfl
      disj := fun _ _ _ _ _ => disjoint_empty_left ∅ }

-- given any B:finset α and s : ℕ there is an partition of B into s+1 parts 1 x B and s x ∅
def defaultM (B : Finset α) (s : ℕ) : MultiPart α
    where
  t := s
  P := by intro i; exact ite (i = 0) B ∅
  A := B
  uni := by
    ext a; rw [mem_biUnion]
    constructor; 
    · intro ha; exact ⟨0,mem_range.2 <|zero_lt_succ s, ha⟩
    · intro ⟨c,_,hc2⟩; 
      split_ifs at hc2; 
      · exact hc2
      · exfalso; apply not_mem_empty _ hc2
  disj := 
  by
    intro i _ j _ ne; 
    split_ifs with h h_1; 
    · exfalso; rw [h,h_1] at ne ; contradiction
    · exact disjoint_empty_right _ 
    · exact disjoint_empty_left _
    · exact disjoint_empty_left _

--TODO : this should use set.pairwise_disjoint.insert to be much simpler
-- we want to build a complete (t+1)-partite graph one part at a time
-- given a current partition into t+1 parts we can insert a new
-- disjoint set to the partition, increasing the number of parts by 1.
--- (We will need this to build the complete multipartite graph used for Furedi's stabilty result)
def minsert (M : MultiPart α)  (h : Disjoint M.A B) : MultiPart α
    where
  t := M.t + 1
  P := by intro i; exact ite (i ≠ M.t + 1) (M.P i) B
  A := B ∪ M.A
  uni := 
  by 
    rw [range_succ,biUnion_insert, M.uni]; 
    split_ifs with h 
    · contradiction
    · ext a; simp_rw [mem_union, mem_biUnion]
      constructor
      · intro h
        cases h with
        | inl hb => left; exact hb
        | inr hP =>
          right
          obtain ⟨a1, H, H2⟩ := hP; 
          refine ⟨a1, H, ?_⟩; 
          split_ifs with h_2;
          · exact H2;
          · push_neg at h_2 ; exfalso; rw [h_2] at H; exact not_mem_range_self H
      · intro h;
        cases h with
        | inl hb => left; exact hb
        | inr hP =>
          right
          obtain ⟨a1, H, H2⟩ := hP 
          split_ifs at H2 with h_2 
          · exact ⟨a1, H, H2⟩
          · push_neg at h_2 ; exfalso; rw [h_2] at H ; exact not_mem_range_self H
  disj := by
    intro i hi j hj iltj; rw [M.uni, disjoint_biUnion_left] at h  
    split_ifs with h_1 h_2 h_3
    · refine M.disj i ?_ j ?_ iltj
      · exact mem_range.mpr (lt_of_le_of_ne (mem_range_succ_iff.mp hi) h_1)
      · exact mem_range.mpr (lt_of_le_of_ne (mem_range_succ_iff.mp hj) h_2)
    · apply h i (mem_range.mpr (lt_of_le_of_ne (mem_range_succ_iff.mp hi) h_1))
    · rw [disjoint_comm]
      apply h j (mem_range.mpr (lt_of_le_of_ne (mem_range_succ_iff.mp hj) h_3))
    · push_neg at h_1 h_3; rw [h_1, h_3] at iltj ; contradiction

--- after inserting B the vertex set is the union of new and old
theorem insert_AB (M : MultiPart α) (h : Disjoint M.A B) :
    (minsert M h).A = M.A ∪ B :=
  union_comm _ _

-- number of parts has increased by 1 (so now have (t+2) parts rather than (t+1))
theorem insert_t (M : MultiPart α) (h : Disjoint M.A B) : (minsert M h).t = M.t + 1 :=
  rfl

--the parts are the same except the last which is the new set.
theorem insert_P (M : MultiPart α) (h : Disjoint M.A B) :
    ∀ i, (minsert M h).P i = ite (i ≠ M.t + 1) (M.P i) B := fun _ => rfl

--all vertices in the new part are in the last part of the new partition
theorem insert_P' (M : MultiPart α) (h : Disjoint M.A B) :
    ∀ v ∈ B, v ∈ (minsert M h).P (M.t + 1) := 
by 
  intro v hv; rw [insert_P]; split_ifs with h_1;
  · contradiction
  · exact hv

--conversely if v is in the last part of the new partition then it is from the inserted part.
theorem insert_C (M : MultiPart α) (h : Disjoint M.A B):
    v ∈ (minsert M h).P (M.t + 1) → v ∈ B := 
by 
  intro h1; rw [insert_P] at h1 ; 
  split_ifs at h1 with h2;
  · contradiction 
  · exact h1

-- there is always a (s+1)-partition of B for any B:finset α and s:ℕ
theorem exists_mpartition (B : Finset α) (s : ℕ) : ∃ M : MultiPart α, M.A = B ∧ M.t = s :=
  ⟨defaultM B s, rfl, rfl⟩

---M.disj is the same as "pairwise_disjoint" but without any coercion to set for range(t+1)
theorem pair_disjoint (M : MultiPart α) : (range (M.t + 1) : Set ℕ).PairwiseDisjoint M.P :=
  M.disj

-- member of a part implies member of union
theorem mem_part {M : MultiPart α} : i ∈ range (M.t + 1) → v ∈ M.P i → v ∈ M.A := by
  intro hi hv; rw [M.uni]; rw [mem_biUnion]; exact ⟨i, hi, hv⟩

-- every vertex in M.A belongs to a part
theorem inv_part {M : MultiPart α} (hA : v ∈ M.A) : ∃ i ∈ range (M.t + 1), v ∈ M.P i := by
  rw [M.uni, mem_biUnion] at hA ; exact hA

-- M.A is the union of its parts
theorem biUnion_parts (M : MultiPart α) : M.A = Finset.biUnion (range (M.t + 1)) fun i => M.P i :=
by
  ext x; 
  rw [mem_biUnion]; 
  constructor; 
  · intro hA; obtain ⟨i,hi⟩:= (inv_part hA); exact ⟨i,hi⟩
  · intro hA; obtain ⟨i, hi, hi2⟩ := hA; exact mem_part hi hi2

-- so (by disj) card of M.A is the sum of sizes of parts
theorem card_uni (M : MultiPart α) : M.A.card = ∑ i in range (M.t + 1), (M.P i).card := 
by
  rw [biUnion_parts M]; rw [card_biUnion]; intro x hx y hy ne; exact M.disj x hx y hy ne

-- Any turan partition with M.t and M.A is bal M.t |M.A| ((M.P i).card)
theorem turan_bal {M : MultiPart α} (hM : TuranPartition M) : Bal M.t M.A.card (λ i=> (M.P i).card) :=
by
  rw [turanPartition_iff_not_moveable] at hM ; unfold Moveable at hM 
  rw [not_not] at hM ; rw [card_uni]; exact ⟨hM, rfl⟩

-- if v belongs to P i and P j then i = j.
theorem uniq_part {M : MultiPart α} :
    i ∈ range (M.t + 1) → j ∈ range (M.t + 1) → v ∈ M.P i → v ∈ M.P j → i = j :=
by
  intro hi hj hiv hjv; by_contra h; 
  apply not_disjoint_iff.2 ⟨v, hiv, hjv⟩ (M.disj i hi j hj h)

-- if v belongs to P i and i ≠ j and is in range then v ∉ P j
theorem uniq_part' {M : MultiPart α} :
    i ∈ range (M.t + 1) → j ∈ range (M.t + 1) → i ≠ j → v ∈ M.P i → v ∉ M.P j := 
by
  intro hi hj hiv ne; contrapose hiv; push_neg at hiv ; 
  rw [not_ne_iff]; exact uniq_part hi hj ne hiv

-- every part is contained in A
theorem sub_part {M : MultiPart α} (hi : i ∈ range (M.t + 1)) : M.P i ⊆ M.A := 
by
  rw [M.uni]; intro x hx; rw [mem_biUnion]; exact ⟨i, hi, hx⟩

-- if there are two different parts then the sum of their sizes is at most the size of the whole
-- could make a version for any number of parts ≥ 2 but don't need it,
theorem two_parts {M : MultiPart α} (hi : i ∈ range (M.t + 1)) (hj : j ∈ range (M.t + 1))
    (hne : i ≠ j) : (M.P i).card + (M.P j).card ≤ M.A.card :=
by
  rw [card_uni,← sum_erase_add (range (M.t + 1)) _ hj]; 
  apply Nat.add_le_add_right
  rw [← sum_erase_add ((range (M.t + 1)).erase j) _ (mem_erase_of_ne_of_mem hne hi)]
  apply Nat.le_add_left

--A is the union of each part and the sdiff
theorem sdiff_part {M : MultiPart α} (hi : i ∈ range (M.t + 1)) :
    M.A = M.A \ M.P i ∪ M.P i := 
by
  have := sub_part hi
  rwa [sdiff_union_self_eq_union, left_eq_union_iff_subset]

-- each part is disjoint from its sdiff with the whole
theorem disjoint_part {M : MultiPart α}: Disjoint (M.A \ M.P i) (M.P i) :=
  sdiff_disjoint

-- size of uni = sum of rest and part
theorem card_part_uni {M : MultiPart α} (hi : i ∈ range (M.t + 1)) :
    M.A.card = (M.A \ M.P i).card + (M.P i).card :=
by
  nth_rw 1 [sdiff_part hi]
  apply card_disjoint_union sdiff_disjoint

--  We can create a new partition by moving v ∈ M.P i from P i to P j.
-- We only want to do this if this increases the number of edges in the complete multipartite graph.
--  Any non-Turan partition contains a vertex that can be moved to increase 
--  the number of edges in corresponding graph
-- TODO: figure out why "(M.P j).insert v" caused an error (so used (M.P j)∪ {v} instead)
--  but it didn't complain about "(M.P i).erase v"
--- Error message :'insert' is not a valid "field" because environment does not contain 
-- 'finset.insert' M.P j which has type finset α
--- This is due to the "insert" defined for multi_part α above that clashes, and somehow finset.insert doesn't work

def move (M : MultiPart α) (hvi : i ∈ range (M.t + 1) ∧ v ∈ M.P i)
    (hj : j ∈ range (M.t + 1) ∧ j ≠ i) : MultiPart α
    where
  t := M.t
  P := by intro k; exact ite (k ≠ i ∧ k ≠ j) (M.P k) (ite (k = i) ((M.P i).erase v) (insert v (M.P j)))
  A := M.A
  uni := by
    rw [M.uni]; ext a;simp_rw [mem_biUnion,mem_range, Ne.def, exists_prop] at * 
    constructor;
    · intro h  
      by_cases hav : a = v
      · refine ⟨j, hj.1, ?_⟩; rw [← hav] at * 
        split_ifs with h_1 h_2
        · exfalso; exact h_1.2 rfl;
        · exfalso; push_neg at h_1 ; exact hj.2 h_2
        · apply mem_insert_self
      · obtain ⟨k, hk1, hk2⟩ := h
        refine ⟨k, hk1, ?_⟩; 
        split_ifs with h_1 h_2; 
        · exact hk2;
        · apply mem_erase.2 ; rw [h_2] at hk2 ; exact ⟨hav, hk2⟩
        · push_neg at h_1 ; rw [h_1 h_2] at hk2 ; exact mem_insert_of_mem hk2
    · intro h
      by_cases hav : a = v; 
      · rw [← hav] at hvi ; exact ⟨i, hvi⟩
      · obtain ⟨k, hk1, hk2⟩ := h; 
        split_ifs at hk2 ; 
        · exact ⟨k, hk1, hk2⟩;
        · exact ⟨i, hvi.1, (erase_subset v (M.P i)) hk2⟩
        · refine ⟨j, hj.1, ?_⟩; rw [mem_insert] at hk2 ; 
          cases hk2 with
          | inl hk2 =>  contradiction 
          | inr hk2 => exact hk2
  disj := by
    intro a ha b hb ne; 
    split_ifs with h h_1 h_2 h_3 h_4 h_5 h_6 h_7
    · exact M.disj a ha b hb ne
    · apply disjoint_of_subset_right _ (M.disj a ha i hvi.1 h.1); exact erase_subset _ _
    · rw [disjoint_insert_right];
      refine ⟨?_,M.disj a ha j hj.1 h.2⟩
      intro hv; exact h.1 (uniq_part ha hvi.1 hv hvi.2)
    · apply disjoint_of_subset_left _ (M.disj i hvi.1 b hb h_4.1.symm);
      exact erase_subset _ _
    · exfalso; push_neg at h ; push_neg at h_4 ; rw [h_3, h_5] at ne ; contradiction
    · apply disjoint_insert_right.2
      constructor
      · apply not_mem_erase v
      · apply disjoint_of_subset_left _ (M.disj i hvi.1 j hj.1 hj.2.symm);
        apply erase_subset 
    · rw [disjoint_insert_left]
      refine ⟨?_,M.disj j hj.1 b hb h_6.2.symm⟩;
      intro hb2; have := uniq_part hb hvi.1 hb2 hvi.2; exact h_6.1 this
    · simp_rw [disjoint_insert_left, disjoint_singleton_left, mem_erase]
      constructor
      · push_neg; intro hc; contradiction
      · apply disjoint_of_subset_right _ (M.disj j hj.1 i hvi.1 hj.2);
        apply erase_subset v (MultiPart.P M i) 
    · exfalso; push_neg at h ; push_neg at h_6 ; 
      rw [h h_3, h_6 h_7] at ne ; contradiction

-- new whole is same as old
theorem move_a {M : MultiPart α}  (hvi : i ∈ range (M.t + 1) ∧ v ∈ M.P i)
    (hj : j ∈ range (M.t + 1) ∧ j ≠ i) : (move M hvi hj).A = M.A :=rfl

-- the moved partition still has t+1 parts
theorem move_t {M : MultiPart α} (hvi : i ∈ range (M.t + 1) ∧ v ∈ M.P i)
    (hj : j ∈ range (M.t + 1) ∧ j ≠ i) : (move M hvi hj).t = M.t :=rfl

-- the moved parts are the same except for P i and P j which have lost/gained v
theorem move_p {M : MultiPart α}  (hvi : i ∈ range (M.t + 1) ∧ v ∈ M.P i)
    (hj : j ∈ range (M.t + 1) ∧ j ≠ i) :
    k ∈ range (M.t + 1) →
      (move M hvi hj).P k =
        ite (k ≠ i ∧ k ≠ j) (M.P k) (ite (k = i) ((M.P i).erase v) (insert v (M.P j))) :=
  by intro _; rfl

-- the sizes of parts changed by moving v
theorem move_Pcard {M : MultiPart α}  (hvi : i ∈ range (M.t + 1) ∧ v ∈ M.P i)
    (hj : j ∈ range (M.t + 1) ∧ j ≠ i) :
    k ∈ range (M.t + 1) →
      ((move M hvi hj).P k).card =
        ite (k ≠ i ∧ k ≠ j) (M.P k).card (ite (k = i) ((M.P i).card - 1) ((M.P j).card + 1)) :=
by
  intro hk; rw [move_p hvi hj hk]; 
  split_ifs with h h_1
  · rfl
  · exact card_erase_of_mem hvi.2
  · apply card_insert_of_not_mem (uniq_part' hvi.1 hj.1 hj.2.symm hvi.2)

--- the complement of the part with v has gained v
theorem sdiff_erase {A  : Finset α} (hB : B ⊆ A) (hv : v ∈ B) :
    A \ B.erase v = A \ B ∪ {v} := by
  ext a; constructor;
  · intro h; rw [mem_union, mem_sdiff] at *; rw [mem_erase] at h 
    push_neg at h ; 
    by_cases h' : a = v;
    · right; exact mem_singleton.mpr h'
    · left; exact ⟨h.1, h.2 h'⟩
  · intro h; rw [mem_sdiff]; rw [mem_erase]; rw [mem_union, mem_sdiff] at h ; push_neg
    cases h with
    | inl h =>  exact ⟨h.1, fun _ => h.2⟩;
    | inr h => 
      by_contra h'; push_neg at h' 
      have ha := hB hv
      have := mem_singleton.mp h; rw [← this] at ha 
      exact (h' ha).1 this

--..hence its size  has increased
theorem card_sdiff_erase {A : Finset α} (hB : B ⊆ A) (hv : v ∈ B) :
    (A \ B.erase v).card = (A \ B).card + 1 :=
by
  have hv2 : v ∉ A \ B := by rw [mem_sdiff]; push_neg; intro _; exact hv
  rw [sdiff_erase hB hv]; exact card_disjoint_union (disjoint_singleton_right.mpr hv2)

--  complement of part without v has lost v
theorem sdiff_insert  {A : Finset α} :
    A \ (insert v B) = (A \ B).erase v := by
  ext; constructor;
  · intro h
    rw [mem_erase]; rw [mem_sdiff] at *; rw [mem_insert] at h ; push_neg at h ;
    exact ⟨h.2.1, h.1, h.2.2⟩
  · intro h; rw [mem_erase] at h ; rw [mem_sdiff]; rw [mem_insert]; push_neg;
    rw [mem_sdiff] at h ; exact ⟨h.2.1, h.1, h.2.2⟩

--- .. hence its size has decreased
theorem card_sdiff_insert {A : Finset α}  (hvB : v ∉ B) (hvA : v ∈ A) :
    (A \ (insert v B)).card = (A \ B).card - 1 :=
by
  rw [sdiff_insert]; exact card_erase_of_mem (mem_sdiff.mpr ⟨hvA, hvB⟩)

-- how have the sizes of the complements of parts changed by moving v
-- for parts other than i and j nothing has changed, for i and j we have calculated the changes above
theorem move_Pcard_sdiff {M : MultiPart α}
    (hvi : i ∈ range (M.t + 1) ∧ v ∈ M.P i) (hj : j ∈ range (M.t + 1) ∧ j ≠ i) :
    k ∈ range (M.t + 1) →
      ((move M hvi hj).A \ (move M hvi hj).P k).card =
        ite (k ≠ i ∧ k ≠ j) (M.A \ M.P k).card
          (ite (k = i) ((M.A \ M.P i).card + 1) ((M.A \ M.P j).card - 1)) :=
by
  intro hk; rw [move_p hvi hj hk]; rw [move_a hvi hj]; 
  split_ifs; 
  · rfl
  · exact card_sdiff_erase (sub_part hvi.1) hvi.2
  · apply card_sdiff_insert 
      (uniq_part' hvi.1 hj.1 hj.2.symm hvi.2)
        (mem_part hvi.1 hvi.2)

-- key increment inequality we need to show moving a vertex in a moveable partition is increases deg sum
theorem move_change  (hb : b + 1 < a) (hn : a + b ≤ n) :
    a * (n - a) + b * (n - b) < (a - 1) * (n - a + 1) + (b + 1) * (n - b - 1) :=
  by
  rw [mul_add,add_mul,mul_one,one_mul]
  have ha := tsub_add_cancel_of_le ((le_tsub_of_add_le_left hb.le).trans tsub_le_self : 1 ≤ a)
  have h2 : a ≤ n - b := le_tsub_of_add_le_right hn
  have hnb := tsub_add_cancel_of_le (le_trans ((le_tsub_of_add_le_left hb.le).trans tsub_le_self : 1 ≤ a) h2)
  nth_rw 1 [← ha,← hnb];
  rw [add_mul, mul_add, one_mul, mul_one, add_assoc, add_assoc]
  apply Nat.add_lt_add_left
  rw [add_comm, ← add_assoc, add_comm (a - 1), add_assoc, add_assoc]
  apply Nat.add_lt_add_left
  have ab : b < a - 1 := lt_tsub_of_add_lt_right hb
  have nba : n - a < n - b - 1
  · have nba' : n - a < n - (b + 1)
    · rw [tsub_lt_tsub_iff_left_of_le <| h2.trans tsub_le_self ]
      exact tsub_pos_iff_lt.1 <|tsub_pos_of_lt hb
    rwa [tsub_add_eq_tsub_tsub] at nba' 
  exact Nat.add_lt_add ab nba

end Turanpartition

