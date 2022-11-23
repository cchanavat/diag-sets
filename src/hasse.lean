import combinatorics.quiver.basic
import combinatorics.quiver.path
import order.category.FinPartialOrder
import order.cover

import finite

namespace hasse

universe u

-- 1.1.2 (Hasse diagram)
instance hasse (P : FinPartialOrder) : quiver P := { hom := λ y x, x ⋖ y }

open quiver

variable {P : FinPartialOrder}

instance subsingleton_hom_set (x y : P) : subsingleton (x ⟶ y) :=
begin
  apply subsingleton.intro, intros e e',
  refl
end

def hom_of_cov {x y : P} (hcov : y ⋖ x) : x ⟶ y := hcov
def path_of_cov {x y : P} (hcov : y ⋖ x) : path x y := hom.to_path (hom_of_cov hcov)
def cov_of_hom {x y : P} (f : x ⟶ y) : y ⋖ x := f

lemma le_of_path {x y : P} (p : path y x) : x ≤ y :=
begin
  induction p with w z p h h1,
  { refl },
  { apply le_of_lt, 
    apply has_lt.lt.trans_le (covby.lt (cov_of_hom h)) h1  }
end

lemma lt_of_path {x y : P} (hneq : x ≠ y) (p : path y x) : x < y :=
begin 
  rw lt_iff_le_and_ne,
  exact and.intro (le_of_path p) hneq
end

lemma covby_of_length_one  {x y : P} (p : path y x) (hl : p.length = 1) : x ⋖ y :=
begin
  cases p with w _ p q,
  { rw path.length_nil at hl, linarith },
  { rw [path.length_cons, add_left_eq_self] at hl,  
    rw path.eq_of_length_zero p hl,
    exact cov_of_hom q }
end

-- Two lemmas, if we have two elements one smaller than the other,
-- we can consider an element in between that either cover the smaller
-- or is covered by the larger
lemma exists_right_cov_of_lt {x x' : P} (hle : x < x') : ∃ y, x ⋖ y ∧ y ≤ x' :=
begin
  rw ←finite.greater_iff_in_greater at hle,
  exact finite.exists_cov_of_greater hle 
end

lemma exists_left_cov_of_lt {x x' : P} (hle : x < x') : ∃ y, x ≤ y ∧ y ⋖ x' :=
begin
  rw ←finite.smaller_iff_in_smaller at hle,
  exact finite.exists_cov_of_smaller hle 
end

lemma nil_of_path_to_self {x : P} (p : quiver.path x x) : p = path.nil :=
begin 
  cases p with y hp q e,
  { refl },
  { have lt := covby.lt e,
    rw lt_iff_le_not_le at lt,
    exfalso, exact lt.right (le_of_path q) }
end

-- Auxiliary results to prove that if x < y, then we have a path from y to x
namespace path_of_lt
variables {x y : P} 

noncomputable
def next (xn : P) (hpath : ∀ z : P, path z x → ¬z = y) (hlt : xn < y) (p : path xn x) : 
  { x // xn ⋖ x ∧ x < y } :=
begin
  let k := classical.indefinite_description _ (exists_right_cov_of_lt hlt),
  use k.val,
  apply and.intro k.prop.left,
  by_cases heq : k.val = y,
  { exfalso,
    have hcov : xn ⋖ y := 
    begin
      rw ←heq, exact k.prop.left
    end,
    apply hpath _ (path.comp (path_of_cov hcov) p), 
    refl },
    { rw lt_iff_le_and_ne,
      exact and.intro k.prop.right heq }
end

-- A cool use of Σ-types
noncomputable
def path_seq (hpath : ∀ z : P, path z x → ¬z = y) (hlt : x < y) : 
  ℕ → Σ (w : P), { p : path w x // w < y }  
| 0       := ⟨x, ⟨path.nil, hlt⟩⟩
| (n + 1) := let v := (next (path_seq n).1 hpath (path_seq n).2.prop (path_seq n).2.val) in
             ⟨v.val, ⟨path.comp (path_of_cov v.prop.left) (path_seq n).2.val, v.prop.right⟩⟩

-- Now we forget some of the structure of the previous sequence 
noncomputable
def path_seq_forget (hpath : ∀ z : P, path z x → ¬z = y) (hlt : x < y) : 
  ℕ → P := λ n, (path_seq hpath hlt n).1

-- Tis sequence is increasing
lemma path_seq_forget_cov_increasing (hpath : ∀ z : P, path z x → ¬z = y) (hlt : x < y) :
  ∀ n, path_seq_forget hpath hlt n ⋖ path_seq_forget hpath hlt (n + 1) :=
begin
  intro n,
  unfold path_seq_forget path_seq, simp,
  exact (next _ hpath (path_seq hpath hlt n).2.prop (path_seq hpath hlt n).2.val).prop.left
end

lemma path_seq_forget_increasing (hpath : ∀ z : P, path z x → ¬z = y) (hlt : x < y) :
  ∀ n, path_seq_forget hpath hlt n < path_seq_forget hpath hlt (n + 1) :=
begin
  intro n,
  apply covby.lt,
  apply path_seq_forget_cov_increasing
end

def path_of_lt {x y : P} (hlt : x < y) : ∃ (z : P) (p : path z x), z = y :=
begin
  by_contra' h,
  apply finite.no_infinite_increasing_seq (path_of_lt.path_seq_forget h hlt),
  apply path_of_lt.path_seq_forget_increasing
end

end path_of_lt

-- This is the result,
-- Highly nonconstructible
noncomputable
def path_of_lt {x y : P} (hlt : x < y) : path y x :=
begin
  have p := classical.indefinite_description _ (path_of_lt.path_of_lt hlt),
  simp at p,
  have q := classical.indefinite_description _ p.prop,
  rw ←q.prop,
  exact q.val
end


lemma eq_of_double_covby {x y z : P} (h1 : x ⋖ y) (h2 : x ⋖ z) (hle : y ≤ z) : y = z :=
eq_of_le_of_not_lt hle (h2.right h1.left)

lemma eq_of_length_zero_int {x y : P} (p : path x y) (hzero : int.of_nat p.length = 0) : x = y :=
begin
  apply path.eq_of_length_zero p,
  rw int.coe_nat_inj hzero,
end

end hasse