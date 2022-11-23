import data.finset.basic
import order.cover
import order.category.FinPartialOrder
import tactic.linarith

noncomputable theory
local attribute [instance] classical.prop_decidable

/--
  This file provide some useful lemmas about the finiteness property of P
  In particular
  `no_infinite_increasing_seq` and `no_infinite_decreasing_seq` prove that there are 
  no infinite increasing/decreasing sequences in P
  and `no_forall_exists_lt` and `no_forall_exists_gt` prove that there are no statement of
  the form ∀ x ∈ U, ∃ y ∈ U, x < (or >) y, with `U : finset P` 
-/

variables (P : FinPartialOrder) -- [decidable_eq P] [@decidable_rel P (<)]


-- Some useful lemma about finiteness
namespace finite

variable {P}

abbreviation points : finset P := fintype.elems P

def greater_or_eq (x : P) : finset P := finset.filter (λ y : P, x ≤ y) points
def greater (x : P) : finset P := finset.filter (λ y : P, x < y) points

lemma greater_iff_in_greater (x y : P) : y ∈ greater x ↔ x < y := 
begin
  erw finset.mem_filter, simp [fintype.complete]
end  

-- We prove that there could not be any strictly increasing sequence
lemma monotonic_of_increasing {s : ℕ → P} (hinc : ∀ n, s n < s (n + 1)) :
  ∀ i j, i < j → s i < s j :=
begin
  intros i j, revert i,
  induction j with j hj,
  simp,
  intros i hi,
  by_cases i = j,
  rw h, apply hinc,
  have i_lt_j : i < j := array.push_back_idx hi h,
  specialize hj i i_lt_j,
  apply lt_trans hj,
  apply hinc
end

lemma injective_of_increasing {s : ℕ → P} (hinc : ∀ n, s n < s (n + 1)) : function.injective s :=
begin
  intros x y h,
  wlog h : x ≤ y,
  rw le_iff_lt_or_eq at h,
  cases h,
  { exfalso, 
    have lt := monotonic_of_increasing hinc x y h,
    simp at lt, 
    exact ne_of_lt lt h_1 },
  { exact h }
end

lemma no_infinite_increasing_seq (s : ℕ → P) : ¬ (∀ n, s n < s (n + 1)) :=
begin
  intro hinc,
  have i : function.injective s := injective_of_increasing hinc,
  have inf_P : infinite P := infinite.of_injective s i,
  rw ←not_finite_iff_infinite at inf_P,
  exact inf_P (finite.of_fintype P)
end

lemma injective_of_neq_preds {s : ℕ → P} (hinc : ∀ n m, n < m → s n ≠ s m) : function.injective s :=
begin
  intros n m,
  wlog h : n ≤ m,
  rw le_iff_lt_or_eq at h,
  cases h,
  { intro hs, exfalso, exact hinc _ _ h hs },
  { rw h, intro, refl }
end

-- No sequence in P where s_m is different from s_n, n < m  
lemma no_forall_neq_preds (s : ℕ → P) : ¬ (∀ n m, n < m → s n ≠ s m) :=
begin
  intros hneq,
  have i : function.injective s := injective_of_neq_preds hneq,
  have inf_P : infinite P := infinite.of_injective s i,
  rw ←not_finite_iff_infinite at inf_P,
  exact inf_P (finite.of_fintype P)
end

variables {U : finset P} {x0 : P} (hx0 : x0 ∈ U) 

def seq_A_E' (h : ∀ x ∈ U, { y : P // y ∈ U ∧ x < y }) : ℕ → { x : P // x ∈ U } 
| 0       := ⟨x0, hx0⟩
| (n + 1) := ⟨(h (seq_A_E' n).val (seq_A_E' n).prop).val, 
              (h (seq_A_E' n).val (seq_A_E' n).prop).prop.left⟩ 

def seq_A_E (h : ∀ x ∈ U, { y : P // y ∈ U ∧ x < y }) : ℕ → P := λ n, (seq_A_E' hx0 h n).val
def seq_A_E_in (h : ∀ x ∈ U, { y : P // y ∈ U ∧ x < y }) (n : ℕ)  : 
  (seq_A_E hx0 h n) ∈ U := (seq_A_E' hx0 h n).prop

lemma seq_A_E_increasing (h : ∀ x ∈ U, { y : P // y ∈ U ∧ x < y }) : 
  ∀ n, seq_A_E hx0 h n < seq_A_E hx0 h n.succ :=
begin
  intro n,
  have g := (h (seq_A_E hx0 h n) (seq_A_E_in hx0 h n)).prop.right,
  convert g
end

lemma no_infinite_decreasing_seq (h : ∀ x ∈ U, { y : P // y ∈ U ∧ x < y }) (s : ℕ → P) : 
  ¬ (∀ n, s (n + 1) < s n) :=
begin
  intro h,
  apply @no_infinite_increasing_seq (FinPartialOrder.dual.obj P) s h,
end

-- Therefore, there cannot be true statement of the form (∀ x : U, { y : U // x < y })
-- which is a quite useful argument(?)
lemma no_forall_exists_lt (h : ∀ x ∈ U, { y : P // y ∈ U ∧ x < y }) : false :=
no_infinite_increasing_seq (seq_A_E hx0 h) (seq_A_E_increasing _ _)

lemma no_forall_exists_gt (hx0 : x0 ∈ U) (h : ∀ x ∈ U, { y : P // y ∈ U ∧ y < x }) : false :=
@no_infinite_increasing_seq (FinPartialOrder.dual.obj P) _ (seq_A_E_increasing hx0 h)


-- with the axiom of choice
lemma no_forall_exists_lt' (h : ∀ x ∈ U, ∃ y ∈ U, x < y) : false :=
no_forall_exists_lt hx0
begin
  intros x hx,
  have k := classical.indefinite_description _ (h x hx),
  simp at k,
  exact k  
end

lemma no_forall_exists_gt' (h : ∀ x ∈ U, ∃ y ∈ U, y < x) : false :=
no_forall_exists_gt hx0
begin
  intros x hx,
  have k := classical.indefinite_description _ (h x hx),
  simp at k,
  exact k  
end

-- A variation with ≠ in place of < (should have done that first...)
def seq_A_E_neq' (h : ∀ x ∈ U, { y : P // y ∈ U ∧ x ≠ y }) : ℕ → { x : P // x ∈ U } 
| 0       := ⟨x0, hx0⟩
| (n + 1) := ⟨(h (seq_A_E_neq' n).val (seq_A_E_neq' n).prop).val, 
              (h (seq_A_E_neq' n).val (seq_A_E_neq' n).prop).prop.left⟩ 

def seq_A_E_neq (h : ∀ x ∈ U, { y : P // y ∈ U ∧ x ≠ y }) : ℕ → P := λ n, (seq_A_E_neq' hx0 h n).val
def seq_A_E_neq_in (h : ∀ x ∈ U, { y : P // y ∈ U ∧ x ≠ y }) (n : ℕ)  : 
  (seq_A_E_neq hx0 h n) ∈ U := (seq_A_E_neq' hx0 h n).prop

lemma seq_A_E_neq_succ (h : ∀ x ∈ U, { y : P // y ∈ U ∧ x ≠ y }) : 
  ∀ n, seq_A_E_neq hx0 h n ≠ seq_A_E_neq hx0 h n.succ :=
begin
  intro n,
  have g := (h (seq_A_E_neq hx0 h n) (seq_A_E_neq_in hx0 h n)).prop.right,
  convert g
end

lemma lt_iff_le_and_neq (x y : P) : x < y ↔ x ≤ y ∧ ¬x = y :=
begin
  rw lt_iff_le_not_le,
  split; intro h; apply and.intro h.left; intro hneg,
  { have h' : y ≤ x := by rw hneg, 
    exact h.right h' },
  { exact h.right (le_antisymm h.left hneg) }
end

def Ioc (x x' : P) := finset.filter (λ y, x < y ∧ y ≤ x') points
lemma right_mem_Ioc (x x' : P) : x' ∈ Ioc x x' ↔ x < x' := 
begin
  unfold Ioc,
  simp [fintype.complete]
end

lemma Ioc_lt_left {x x' y : P} (hin : y ∈ Ioc x x') : x < y := 
begin
  erw finset.mem_filter at hin,
  simp [fintype.complete] at hin,
  exact hin.left
end

lemma Ioc_le_right {x x' y : P} (hin : y ∈ Ioc x x') : y ≤ x' := 
begin
  erw finset.mem_filter at hin,
  simp [fintype.complete] at hin,
  exact hin.right
end

lemma Ioc_in_lt_lt {x x' y w : P} (hin : y ∈ Ioc x x') (hw : x < w ∧ w < y) : w ∈ Ioc x x':=
begin
  erw finset.mem_filter at *,
  simp [fintype.complete] at *,
  apply and.intro hw.left,
  exact le_of_lt (lt_of_lt_of_le hw.right hin.right)
end

-- If x < x', then the sets of greater elements has a min ≤ x'
lemma exists_min_greater {x x' : P} (hx' : x' ∈ greater x) : 
  ∃ y ∈ Ioc x x', ∀ z ∈ Ioc x x', z ≤ y → z = y :=
begin
  by_contra' h,
  have h' : ∀ (y ∈ Ioc x x'), ∃ (z ∈ Ioc x x'), z < y :=
  begin
    intros y hyin,
    cases h y hyin with w h',
    use w, 
    rw lt_iff_le_and_neq w y,
    exact h'
  end,
  have hIoc : x' ∈ Ioc x x' := 
  begin
    rw right_mem_Ioc,
    rw greater_iff_in_greater at hx',
    exact hx'
  end,
  apply no_forall_exists_gt' hIoc h'
end

lemma exists_cov_of_greater {x x' : P} (hx' : x' ∈ greater x) : ∃ y, x ⋖ y ∧ y ≤ x' := 
begin
  cases exists_min_greater hx',
  cases h with w_in h,
  use w,
  rw greater_iff_in_greater at *,
  split, split,
  { exact Ioc_lt_left w_in },
  { intros v hv hw, 
    specialize h v,
    specialize h (Ioc_in_lt_lt w_in (and.intro hv hw)) (le_of_lt hw),
    rw h at hw,
    apply lt_irrefl w,
    exact hw },
  { exact Ioc_le_right w_in }
end

def smaller (x : P) : finset P := finset.filter (λ y : P, x > y) points

lemma smaller_iff_in_smaller (x y : P) : y ∈ smaller x ↔ y < x := 
begin
  erw finset.mem_filter, simp [fintype.complete]
end  

lemma exists_cov_of_smaller {x x' : P} (hx' : x ∈ smaller x') : ∃ y, x ≤ y ∧ y ⋖ x' := 
begin
  cases @exists_cov_of_greater (FinPartialOrder.dual.obj P) x' x hx' with y hy, 
  use y,
  rw ←to_dual_covby_to_dual_iff, 
  apply and.intro hy.right hy.left,
end

-- useful as we will deal with dim x - 1
lemma eq_pred_eq_succ (n m : ℤ) : m = n - 1 ↔ m + 1 = n :=
begin
  split; intro h; linarith,
end

end finite