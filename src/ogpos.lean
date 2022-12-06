import order.interval
import order.locally_finite
import order.succ_pred.basic
import data.set.basic
import data.nat.interval
import data.nat.lattice
import data.int.interval
import init.data.bool.lemmas

import finite
import hasse

local attribute [instance] classical.prop_decidable

open quiver hasse set

/- 1.1. Some basic definitions of order theory -/

-- 1.1.1 (Covering relation) ⋖ is already implemented in Lean, with tons of useful lemmas

-- We require that our ogpos has a decidable equality and <

universe u

namespace ogpos

variables {P : FinPartialOrder}

abbreviation points : finset P := fintype.elems P
abbreviation points_set : set P := fintype.elems P

lemma incl_of_set (U : set P) : U ⊆ points_set := 
begin
  intros x _,
  simp [fintype.complete]
end

instance (U : set P) : finite U :=
finite.of_injective (set.inclusion (incl_of_set U)) (set.inclusion_injective _)

-- 1.1.3 (Closure of a subset)
def cl (U : set P) : set P := { x | ∃ y ∈ U, x ≤ y }

lemma subset_cl (U : set P) : U ⊆ cl U := 
begin
  intros x hx,
  use x,
  apply and.intro hx, refl
end

lemma mem_cl_of_below {U : set P} {x : P} (hx : x ∈ cl U) :
  ∀ y : P, y ≤ x → y ∈ cl U :=
begin
  intros y hle,
  cases hx with w hw,
  cases hw with hw hlew,
  use w,
  apply and.intro hw,
  apply le_trans hle hlew
end

-- 1.1.4 (Closed subset)
class is_closed (U : set P) : Prop :=
(is_eq_cl : cl U = U)

lemma closed_eq_closure (U : set P) [is_closed U] : cl U = U := is_closed.is_eq_cl
 
lemma empty_eq_cl_empty : cl ∅ = (∅ : set P)  :=
begin
  ext, unfold cl, simp
end

lemma mem_is_cl_of_lt {U : set P} [is_closed U] {x y : P} (hy : y ∈ U) (hle : x < y) : x ∈ U :=
begin
  rw ←closed_eq_closure U at *,
  apply mem_cl_of_below hy x (le_of_lt hle) 
end

lemma mem_is_cl_of_le {U : set P} [is_closed U] {x y : P} (hy : y ∈ U) (hle : x ≤ y) : x ∈ U :=
begin
  rw ←closed_eq_closure U at *,
  apply mem_cl_of_below hy x hle
end

instance empty_closed : is_closed (∅ : set P) := 
{ is_eq_cl := empty_eq_cl_empty} 

lemma closure_nonempty {U : set P} (hnempty : U.nonempty) : (cl U).nonempty :=
nonempty.mono (subset_cl U) hnempty

-- Lemma 1.1.5 - part 1
lemma closure_monotonic {U V : set P} (hsub : U ⊆ V) : cl U ⊆ cl V :=
λ x ⟨u, ⟨hu, hle⟩⟩, ⟨u, ⟨hsub hu, hle⟩⟩

-- Lemma 1.1.5 - part 2
lemma closure_sub {U V: set P} [is_closed V] (hsub : U ⊆ V) : cl U ⊆ V :=
begin
  rw ←closed_eq_closure V,
  exact closure_monotonic hsub,
end

lemma closure_indempotent (U : set P) : cl (cl U) = cl U :=
begin
  apply subset_antisymm,
  { intros x hx,
    cases hx with w hw,
    cases hw with hw hlew,
    apply mem_cl_of_below hw _ hlew },
    { exact subset_cl _ }
end

instance closure_is_closed (U : set P) : is_closed (cl U) := 
{is_eq_cl := closure_indempotent _ }

lemma mem_cl_singleton_iff_below (x y : P) : y ∈ cl ({x} : set P) ↔ y ≤ x :=
begin
  split; intro h,
  { cases h with w hw,
    cases hw with hw hle,
    rw mem_singleton_iff at hw,
    rw hw at hle, exact hle },
  { use x, 
    refine and.intro _ h, 
    exact mem_singleton x }
end

-- Lemma 1.1.6
lemma closure_Union_eq_Union_closure (ι : Sort*) (s : ι → set P) : cl (⋃ i, s i) = ⋃ i, cl (s i) :=
begin
  ext, split,
  { rintro ⟨y, ⟨hin, hle⟩⟩,
    rw mem_Union at *, 
    cases hin with i hin,
    use i, use y,
    exact and.intro hin hle },
  { rw mem_Union, 
    rintro ⟨i, ⟨y, ⟨hin, hle⟩⟩⟩,
    use y, refine and.intro _ hle,
    rw mem_Union,
    exact ⟨i, hin⟩ }
end 

lemma closure_Union_eq_Union_closure₂ (ι : Sort*) (κ : ι → Sort*) (s : Π i, κ i → set P) : 
  cl (⋃ i j, s i j) = ⋃ i j, cl (s i j) := by simp_rw closure_Union_eq_Union_closure

-- It is basically easier to redo the proof that to use the previous one
lemma closure_union_eq_union_closure (U V : set P) : cl (U ∪ V) = cl U ∪ cl V :=
begin
  ext, split,
  { rintro ⟨y, ⟨hin, hle⟩⟩,
    cases hin,
    left, use y,
    exact and.intro hin hle, 
    right, use y,
    exact and.intro hin hle },
  { intros hx,
    cases hx; cases hx with y hy; cases hy with hy hle; use y;
    refine and.intro _ hle, 
    { left, exact hy },
    { right, exact hy } }
end

lemma is_closed_eq_union_closure_singleton (U : set P) [is_closed U] : (⋃ x ∈ U, cl {x}) = U :=
begin
  apply subset_antisymm; intros x hx,
  { rw mem_Union at hx,  
    cases hx with w hw,
    rw mem_Union at hw,
    cases hw with hw hcl,
    rw mem_cl_singleton_iff_below at hcl,
    apply mem_is_cl_of_le hw hcl },
  { rw mem_Union, use x, 
    rw mem_Union, use hx,
    rw mem_cl_singleton_iff_below }
end

variable (U : set P)

-- 1.1.7 (Maximal element)
def maximal (x : P) : Prop := (x ∈ U) ∧ ∀ {u}, u ∈ U → ¬(x ⋖ u)

lemma eq_of_maximal_of_le [is_closed U] {x y : P} (hy : y ∈ U) (hle : x ≤ y) (hmax : maximal U x) : x = y :=
begin
  rw le_iff_lt_or_eq at hle,
  cases hle,
  { cases exists_right_cov_of_lt hle with w hw,
    exfalso,
    apply hmax.right (mem_is_cl_of_le hy hw.right) hw.left },
  { assumption }
end

def Max : set P := { x | maximal U x }

def Max_subset : Max U ⊆ U := 
begin
  intros x hx,
  exact hx.left
end

-- lemma Max_inter (U V : set P) : Max (U ∩ V) = Max U ∩ Max V :=
-- begin
--   apply subset_antisymm; intros x hx,
--   { split, 
--     { apply and.intro hx.left.left, intros u hu hcov, cases hx, },

--   } 
-- end
-- In this namespace, some auxialiary lemmas to prove Lemma 1.1.8
namespace maximal

lemma MaxU_sub_U : Max U ⊆ U := λ _ h, h.left

variable [is_closed U]

lemma MaxU_sub_cl_U : cl (Max U) ⊆ U := closure_sub (MaxU_sub_U U)

noncomputable
def next (xn : P) (hxn : xn ∈ U) : { x // x ∈ U ∧ (maximal U x ∧ xn = x ∨ xn ⋖ x)} :=
begin
  by_cases maximal U xn,
  { use xn, 
    apply and.intro hxn, left, 
    apply and.intro h (eq.refl _) },
  { unfold maximal at h, simp at h,
    have w := classical.indefinite_description _ (h hxn),
    -- cases  with w hw,
    use w.val,
    apply and.intro w.prop.left, right,
    exact w.prop.right }
end

noncomputable
def seq {x : P} (hx : x ∈ U) : ℕ → { w // w ∈ U } 
| 0       := ⟨x, hx⟩
| (n + 1) := let k := next U (seq n).val (seq n).prop in ⟨k.val, k.prop.left⟩

lemma seq_increasing {x : P} (hx : x ∈ U) (hmax : ∀ n, ¬maximal U (seq U hx n)) : 
  ∀ n, (seq U hx n).val < (seq U hx (n + 1)).val :=
begin
  intro n,
  unfold seq, simp,
  have prop := (next U (seq U hx n).val (seq U hx n).prop).prop.right,
  cases prop,
  { exfalso, apply hmax (n + 1), unfold seq, simp, exact prop.left },
  { apply covby.lt prop },
end

lemma seq_increasing_or_eq {x : P} (hx : x ∈ U) : ∀ n, (seq U hx n).val ≤ (seq U hx (n + 1)).val :=
begin
  intro n,
  unfold seq, simp,
  cases (next U (seq U hx n).val (seq U hx n).prop).prop.right,
  { exact le_of_eq h.right },
  { exact covby.le h }
end

lemma x_le_seq {x : P} (hx : x ∈ U) : ∀ n, x ≤ (seq U hx n).val :=
begin
  intro n, induction n with n hn,
  { refl },
  { apply le_trans hn, 
    apply seq_increasing_or_eq }
end

lemma U_sub_cl_MaxU : U ⊆ cl (Max U) := 
begin
  intros x hx, 
  have hn : ∃ n, maximal U (seq U hx n) := 
  begin
    by_contra' h,
    exact finite.no_infinite_increasing_seq _ (seq_increasing U hx h)
  end,
  cases hn with n hn,
  use seq U hx n,
  apply and.intro hn,
  apply x_le_seq,
end

end maximal

--Lemma 1.1.8
lemma U_eq_cl_MaxU [is_closed U] : U = cl (Max U) :=
subset_antisymm (maximal.U_sub_cl_MaxU U) (maximal.MaxU_sub_cl_U U)


-- we define the sets of normal elements, the one that are at the bottom of the Hasse diagram
def is_normal (x : P) : Prop := ∀ y : P, is_empty (x ⟶ y)  

lemma not_covby_of_normal {x : P} (norm : is_normal x) : ∀ y : P, ¬ y ⋖ x :=
λ y h, (norm y).false h

-- It is equivalent to say that there is no element below x
lemma normal_iff_no_lt (x : P) : is_normal x ↔ ∀ y : P, ¬ y < x :=
begin
  split; intros h y,
  { intro hlt, 
    cases exists_left_cov_of_lt hlt with w hw,
    exact not_covby_of_normal h _ (hom_of_cov hw.right) },
  { apply is_empty.mk,
    intro f, 
    exact h y (covby.lt (cov_of_hom f)) }
end

lemma all_paths_length_0_of_normal {x : P} (norm : is_normal x) (y : P) (p : path x y) : 
  p.length = 0 :=
begin
  cases p with w hp q p,
  { refl },
  { exfalso,
    by_cases h : w = x,
    {rw h at p, exact (norm _).false p }, 
    { cases exists_left_cov_of_lt (has_lt.lt.trans_le (covby.lt p) (le_of_path q)) with z hz,
      rw normal_iff_no_lt at norm,
      apply norm z,
      exact (covby.lt hz.right) } }
end

-- A path is maximal iff its codomain is normal
def is_maximal {x y : P} (p : path x y) : Prop := is_normal y

structure maximal_path (x : P) :=
(cod : P)
(normal_cod : is_normal cod)
(path : path x cod)

lemma is_maximal_concat {x y z : P} (le : x ⟶ y) (p : path y z) (p_max : is_maximal p) : 
  is_maximal (path.comp (hom.to_path le) p) := p_max

def maximal_path_of_le {x y : P} (le : y ⟶ x) (p : maximal_path x) : maximal_path y :=
{ cod := p.cod,
  normal_cod := p.normal_cod,
  path := path.comp (hom.to_path le) p.path }

def maximal_path_concat {x y : P} (p : path y x) (q : maximal_path x) : maximal_path y :=
{ cod := q.cod,
  normal_cod := q.normal_cod,
  path := path.comp p q.path }

def maximal_path_concat.path {x y : P} (p : path y x) (q : maximal_path x) : 
  (maximal_path_concat p q).path = path.comp p q.path := rfl

-- An element is graded if all maximal path have same length
-- To avoid proving there exists a maximal path, we provide one in the strucutre
-- In pratice, it should not be a problem, as when we prove that all paths have the same length,
-- We will most likely exhibit one 
structure is_graded (x : P) := 
(dim : ℕ)
(max_path : maximal_path x)
(same_length : ∀ p : maximal_path x, dim = path.length p.path)

lemma dim_max_path (x : P) (grad_x : is_graded x) : 
  grad_x.dim = path.length grad_x.max_path.path := grad_x.same_length grad_x.max_path

variable (P)

-- 1.1.9 (Graded poset)
class graded :=
(all_graded : ∀ x : P, is_graded x) 

variables {P} [graded P]

def same_length (x : P) (p q : maximal_path x) : p.path.length = q.path.length :=
begin
  rw [←is_graded.same_length, ←is_graded.same_length],
  exact graded.all_graded x
end

def max_path (x : P) :=  @is_graded.max_path _ _ (graded.all_graded x)

lemma path_length_le_max_path_length {x y : P} (p : path x y) : 
  p.length ≤ (max_path x).path.length :=
begin
  rw [←same_length x (maximal_path_concat p (max_path y)), maximal_path_concat.path],
  rw [path.length_comp, le_add_iff_nonneg_right],
  apply zero_le (max_path y).path.length
end

-- 1.1.10 (Dimension of an element)
def dim (x : P) : ℤ := (max_path x).path.length

lemma dim_pos (x : P) : 0 ≤ dim x := nat.cast_nonneg _

def length_dim {x : P} (p : maximal_path x) : dim x = p.path.length :=
begin
  erw int.coe_nat_inj',
  apply same_length
end

-- The only elements of dim 0 are the normal one 
lemma dim_zero_iff_normal (x : P) : dim x = ↑0 ↔ is_normal x :=
begin
  unfold dim,
  split; intro h,
  { intros y, refine ⟨_⟩, intro e,
    have n := maximal_path.normal_cod (max_path x), 
    rw ←eq_of_length_zero_int _ h at n, 
    convert (n y).false e },
  { by_contra' hm,
    apply hm,
    rw int.coe_nat_inj',
    apply all_paths_length_0_of_normal h }
end

--Lemma 1.1.12
lemma dim_monotonic {x y : P} (hle : x ≤ y) : dim x ≤ dim y :=
begin
  cases lt_or_eq_of_le hle,
  { have p := path_of_lt h, 
    unfold dim,
    have hh : (maximal_path_concat p (max_path x)).path.length = (max_path y).path.length := 
      same_length y _ _,
    rw ←hh, erw path.length_comp, simp },
  { rw h }
end

lemma dim_plus_one_of_covby {x y : P} (hcov : x ⋖ y) : dim x + ↑1 = dim y :=
begin
  unfold dim,
  have hh : (maximal_path_concat (hom.to_path (hom_of_cov hcov)) (max_path x)).path.length = (max_path y).path.length := 
    same_length y _ _,
  erw ←hh,
  rw maximal_path_concat.path,
  unfold hom.to_path,
  rw [path.length_comp, path.length_cons, path.length_nil, zero_add, add_comm, int.coe_nat_add], 
end

lemma dim_st_monotonic {x y : P} (hlt : x < y) : dim x < dim y :=
begin
  cases exists_left_cov_of_lt hlt,
  apply has_le.le.trans_lt (dim_monotonic h.left),
  rw ←dim_plus_one_of_covby h.right,
  simp only [coe_is_one_hom.coe_one, lt_add_iff_pos_right, zero_lt_one],
end

lemma covby_of_dim_plus_one_of_le {x y : P} (hle : y ≤ x) (hdim : dim y + 1 = dim x) : y ⋖ x :=
begin
  have hlt : y < x := 
  begin
     rw lt_iff_le_and_ne,
     apply and.intro hle, intro h,
     rw h at hdim,
     linarith,
  end,
  apply covby_of_length_one (path_of_lt hlt),
  rw [length_dim (maximal_path_concat (path_of_lt hlt) (max_path y)), 
      length_dim (max_path y), maximal_path_concat.path, path.length_comp, int.coe_nat_add] at hdim,
  linarith
end

lemma eq_of_le_of_eq_dim {x y : P} (hle : x ≤ y) (hdim : dim x = dim y) : x = y :=
begin
  rw le_iff_lt_or_eq at hle,
  cases hle,
  { exfalso, 
    have hdim' := dim_st_monotonic hle,
    rw hdim at hdim',
    apply lt_irrefl (dim y),
    exact hdim' },
  { assumption }
end

lemma dim_minus_one_pos_of_cov {x y : P} (hcov : x ⋖ y) : 0 ≤ dim y - 1 :=
begin
  rw [←dim_plus_one_of_covby hcov, coe_is_one_hom.coe_one, add_tsub_cancel_right],
  apply dim_pos x
end

variables (U) 

-- 1.1.13 (Grading of a subset)
def grading (n : ℤ) : set P := { x ∈ U | dim x = n }

@[simp] lemma mem_grading_dim (x : P) (hx : x ∈ U) : x ∈ grading U (dim x) :=
begin
  unfold grading, simp [hx],
end

lemma grading_monotonic {U V : set P} (h : U ⊆ V) (n : ℤ) : grading U n ⊆ grading V n :=
λ x hx, and.intro (h hx.left) hx.right

lemma grading_empty_of_dim_le_zero (n : ℤ) (hle : ¬ (0 ≤ n)) : grading U n = ∅ :=
begin
  rw eq_empty_iff_forall_not_mem, 
  intros x hx,
  apply hle,
  rw ←hx.right,
  apply dim_pos
end

lemma eq_Union_grading : U = ⋃ n, grading U n :=
begin
  apply subset_antisymm; intros x hx; simp at *,
  { use dim x, simp [hx]},
  { cases hx with _ h, erw mem_set_of_eq at h,
    exact h.left }
end

-- Various auxiliary results about dimension of a subset
namespace dim

def dim' (x : P) : ℕ := (dim x).to_nat

lemma dim_eq_dim' (x : P) : dim x = dim' x := rfl

-- This won't be the final dim_set
-- We only use it to prove it's bounded
def dim_set : set ℕ := { n | ∃ x ∈ U, n = dim' x }

@[simp] lemma dim_set_of_is_empty (hempty : U = ∅) : dim_set U = ∅ :=
begin
  rw ←subset_empty_iff,
  intros x hx,
  cases hx with _ hx, cases hx with hx, 
  rw hempty at hx,
  rw mem_empty_iff_false at hx,
  exfalso, exact hx
end

@[simp] lemma dim_set_empty : dim_set (∅ : set P) = ∅ :=
begin
  apply dim_set_of_is_empty, refl,
end

noncomputable
def pick {n : ℕ} (hn : n ∈ dim_set U) : {x : P // x ∈ U ∧ n = dim' x} :=
begin
  convert (classical.indefinite_description _ hn), 
  simp,
end

noncomputable
def undounded_pick_greater (h : ∀ (N : ℕ), ∃ (n : ℕ), n ∈ dim_set U ∧ N < n) (n : ℕ) : 
  {x : P // n < dim' x } :=
begin
  have k := classical.indefinite_description _ (h n),
  have pt := pick U k.prop.left,
  refine ⟨pt.val, _⟩,
  erw ←pt.prop.right,
  exact k.prop.right,
end

variables {U} (x0 : P) (hx0 : x0 ∈ U)

noncomputable
def next (h : ∀ (N : ℕ), ∃ (n : ℕ), n ∈ dim_set U ∧ N < n) (xn : P) := undounded_pick_greater U h (dim' xn)

noncomputable
def dim_seq (h : ∀ (N : ℕ), ∃ (n : ℕ), n ∈ dim_set U ∧ N < n) : ℕ → P 
| 0       := x0
| (n + 1) := next h (dim_seq n)

lemma dim_seq_lt_succ (h : ∀ (N : ℕ), ∃ (n : ℕ), n ∈ dim_set U ∧ N < n) :
  ∀ n, dim' (dim_seq x0 h n) < dim' (dim_seq x0 h (n + 1)) :=
begin
  intro n,
  unfold dim_seq next,
  exact (undounded_pick_greater U h (dim' (dim_seq x0 h n))).prop,
end

lemma dim_seq_lt_pred (h : ∀ (N : ℕ), ∃ (n : ℕ), n ∈ dim_set U ∧ N < n) :
  ∀ n m, n < m → dim' (dim_seq x0 h n) < dim' (dim_seq x0 h m) :=
begin
  intros n m,
  induction m with m hm,
  { intro hinf, exfalso, exact not_lt_bot hinf },
  intro hlt,
  rw nat.lt_succ_iff_lt_or_eq at hlt,
  cases hlt,
    { specialize hm hlt, 
      apply has_lt.lt.trans hm,
      apply dim_seq_lt_succ },
    {rw hlt, apply dim_seq_lt_succ }
end

lemma dim_congr_contra (x y : P) : dim' x < dim' y → x ≠ y :=
begin
  by_contra' h,
  have k := h.left,
  rw h.right at k,
  apply lt_irrefl _ k,
end

lemma dim_seq_neq_preds (h : ∀ (N : ℕ), ∃ (n : ℕ), n ∈ dim_set U ∧ N < n) :
  ∀ n m, n < m → dim_seq x0 h n ≠ dim_seq x0 h m :=
begin
  intros n m hlt,
  apply dim_congr_contra,
  apply dim_seq_lt_pred,
  exact hlt
end

-- As long as we can provide a point in P, the dimension of every point is bounded
lemma bounded_dim_set' (x : P) (U : set P) : ∃ N, ∀ n ∈ dim_set U, n ≤ N :=
begin
  by_contra' h,
  apply finite.no_forall_neq_preds (dim_seq x h),
  apply dim_seq_neq_preds,
end

-- And if P is empty, we can as well show it is bounded (trivially)
lemma bounded_dim_set (U : set P) : ∃ N, ∀ n ∈ dim_set U, n ≤ N :=
begin
  by_cases h : is_empty P,
  { use 0, intros n hn, exfalso, 
    exact h.false (pick U hn).val }, 
  { simp at h,
    apply bounded_dim_set' (classical.choice h) }
end

-- Do I really need to do this?
noncomputable
def dim_set_injective (U : set P) : 
  Σ (N : ℕ), { f : dim_set U → fin N // function.injective f } :=
begin
  have N := classical.indefinite_description _ (bounded_dim_set U),
  use N.val + 1,
  refine ⟨(λ n : dim_set U, {val := n, property := _ }), _ ⟩,
  apply nat.lt_succ_of_le,
  apply N.prop, simp,
  intros m n heq, simp at heq, ext, exact heq,
end

-- A number such that Dim U is less than it
noncomputable
def upper_bound (U : set P) : { N // ∀ n ∈ dim_set U, n ≤ N } := 
classical.indefinite_description _ (bounded_dim_set U)  

lemma dim_mem_dim_set (U : set P) : ∀ x ∈ U, dim' x ∈ dim_set U :=
begin
  intros x hx,
  use x,
  exact and.intro hx (eq.refl _)
end

-- The two useful constructions from this namespace

-- The upper bound
noncomputable
def M (U : set P) : ℤ := (dim.upper_bound U).val

-- The fact that it's an upper bound, with the correct def of dim 
lemma M_prop {U : set P} : ∀ x ∈ U, dim x ≤ (M U : ℤ) :=
begin
  intros x hx,
  have k := (upper_bound U).prop (dim' x) (dim_mem_dim_set U x hx),
  rw dim_eq_dim',
  apply int.coe_nat_le_coe_nat_of_le k,
end

end dim

noncomputable
def dim_set : finset ℤ := 
finset.filter (λ n, ∃ x ∈ U, n = dim x) (finset.Icc 0 (dim.M U))

lemma dim_set_complete : ∀ x ∈ U, dim x ∈ dim_set U :=
begin
  intros x hx,
  erw finset.mem_filter,
  split,
  { rw finset.mem_Icc, apply and.intro (dim_pos x) (dim.M_prop _ hx) },
  { use x, use hx }
end

lemma mem_dim_set_bound : ∀ n ∈ dim_set U, n ∈ (finset.Icc 0 (dim.M U)) := 
begin
  intros n hn, erw finset.mem_filter at hn,
  exact hn.left
end

lemma dim_set_monotonic {U V : set P} (hsub : U ⊆ V) : dim_set U ⊆ dim_set V :=
begin
  intros n hn,
  erw finset.mem_filter at *,
  cases hn.right,
  cases h with hw heq,
  have hin : n ∈ dim_set V :=
  begin
    rw heq,
    apply dim_set_complete _ w (hsub hw)
  end,
  apply and.intro (mem_dim_set_bound V n hin),
  use w, exact and.intro (hsub hw) heq
end

lemma dim_set_nonempty_of_nonempty {U : set P} (hnempty : U.nonempty) : 
  (dim_set U).nonempty :=
begin
  cases hnempty with w hw,
  use dim w,
  apply dim_set_complete U w hw,
end

@[simp] lemma dim_set_empty : dim_set (∅ : set P) = ∅ :=
begin
  unfold dim_set, simp,
end

@[simp] lemma dim_set_of_is_empty (hempty : U = ∅) : dim_set U = ∅ :=
begin
  unfold dim_set, ext, simp,
  intros _ hle x hx,
  rw [hempty, set.mem_empty_iff_false] at hx,
  exfalso,
  exact hx
end

-- 1.1.14 (Dimension of a subset)
noncomputable
def Dim : ℤ := 
dite (U.nonempty) (λ h, finset.max' (dim_set U) (dim_set_nonempty_of_nonempty h)) (λ h, -1)

lemma Dim_ge_minus_one : -1 ≤ Dim U :=
begin
  unfold Dim,
  by_cases h : U.nonempty,
  { rw dif_pos h, 
    cases h with x hx,
    apply le_trans _ (finset.le_max' _ (dim x) (dim_set_complete _ _ hx)),
    apply le_trans _ (dim_pos x),
    linarith },
  { rw dif_neg h }
end

lemma Dim_empty : Dim (∅ : set P) = -1 := by { unfold Dim, simp }

lemma Dim_empty' {U : set P} (h : ¬U.nonempty) : Dim U = -1 :=
begin
  rw [set.nonempty_def, not_exists, ←eq_empty_iff_forall_not_mem] at h,
  rw h,
  exact Dim_empty
end

lemma Dim_monotonic {U V : set P} (hsub : U ⊆ V) : Dim U ≤ Dim V :=
begin
  unfold Dim,
  by_cases hU : U.nonempty,
  { rw [dif_pos hU, dif_pos (nonempty.mono hsub hU)],
    apply finset.max'_subset,
    apply dim_set_monotonic hsub },
  { rw dif_neg hU,
    apply Dim_ge_minus_one }
end

lemma Dim_le {U : set P} (x : P) (hx : x ∈ U) : dim x ≤ Dim U := 
begin
  by_cases h : U.nonempty,
  { unfold Dim, erw dif_pos h, apply finset.le_max',
    apply dim_set_complete U x hx },
  { exfalso, 
    apply h,
    apply nonempty_of_mem hx }
end

lemma Dim_pos {U : set P} (h : U.nonempty) : 0 ≤ Dim U := 
begin
  unfold Dim,
  rw dif_pos h,
  cases h with x hx,
  apply le_trans (dim_pos x),
  apply finset.le_max',
  apply dim_set_complete U x hx
end

lemma Dim_to_nat_eq_Dim {U : set P} (h : U.nonempty) : Dim U = (Dim U).to_nat :=
begin
  rw int.to_nat_of_nonneg (Dim_pos h),
end 
lemma Dim_nonempty {U : set P} (h : 0 ≤ Dim U) : U.nonempty :=
begin
  by_contra he,
  unfold Dim at h,
  erw dif_neg he at h,
  linarith
end

lemma empty_of_Dim_neg (U : set P) (hDim : Dim U < 0) : U = ∅ :=
begin
  apply eq_empty_of_forall_not_mem,
  intros x hx,
  have hpos := Dim_pos (nonempty_of_mem hx),
  linarith
end

-- To work directly in ℤ with non empty sets
noncomputable
def Dim' {U : set P} (hnempty : U.nonempty) : ℤ := 
finset.max' (dim_set U) (dim_set_nonempty_of_nonempty hnempty)

lemma Dim_eq_Dim' {U : set P} (hnempty : U.nonempty) : Dim U = Dim' hnempty :=
begin
  unfold Dim,
  erw dif_pos hnempty, refl,
end

lemma nth_grading_empty_of_Dim_lt_n (n : ℤ) (hlt : Dim U < n) : grading U n = ∅ :=
begin
  by_contra,
  rw [←ne.def, ne_empty_iff_nonempty] at h,
  cases h with x hx,
  rw [←hx.right, ←not_le] at hlt,
  apply hlt,
  by_cases hU : U.nonempty,
  { rw Dim_eq_Dim' hU, 
    apply finset.le_max',
    apply dim_set_complete,
    apply hx.left },
  { exfalso,
    apply hU,
    apply nonempty_of_mem hx.left }
end


lemma eq_Union_grading_bounded : (⋃ k : {k // k ≤ Dim U}, grading U k) = U :=
begin
  apply subset_antisymm; intros x hx, 
  { rw mem_Union at hx,
    cases hx with k hk,
    exact hk.left },
  { by_cases h : U.nonempty,
    { rw mem_Union,
      use dim x, 
      rw Dim_eq_Dim' h,
      apply finset.le_max',
      apply dim_set_complete U x hx,
      apply mem_grading_dim U x hx },
    { exfalso, 
      apply h,
      apply nonempty_of_mem hx } }
end

lemma eq_Union_grading_bounded' (n : ℤ) (hle : Dim U ≤ n) : (⋃ k : {k // k ≤ n}, grading U k) = U :=
begin
  nth_rewrite_rhs 0 ←eq_Union_grading_bounded U,
  
  apply subset_antisymm; intros x hx; rw mem_Union at *; cases hx with k hk,
  { use k,
    { by_contra' hc, rw nth_grading_empty_of_Dim_lt_n U _ hc at hk,
      apply not_mem_empty _ hk },
    { exact hk } },
  { use k,
    apply le_trans k.prop hle,
    exact hk }
end

-- 1.1.15
lemma Dim_cl_singleton (x : P) : 
  Dim (cl ({x} : set P)) = dim x :=
begin
  rw Dim_eq_Dim' ((closure_nonempty (set.singleton_nonempty x))),
  unfold Dim', 
  apply le_antisymm,
  { simp, intros y hy,
    erw finset.mem_filter at hy, simp at hy,
    cases hy.right with w hw,
    rw hw.right,
    apply dim_monotonic,
    rw ←mem_cl_singleton_iff_below,
    exact hw.left },
  { apply finset.le_max', 
    apply dim_set_complete,
    apply subset_cl,
    exact mem_singleton x }
end

lemma dim_le_Dim (U : set P) : ∀ x ∈ U, dim x ≤ Dim U :=
begin
by_cases h : U = ∅,
  { rw [h, Dim_empty], intros x hx,
    exfalso, apply not_mem_empty x hx },
  { intros x hx, 
    rw [←ne.def, ne_empty_iff_nonempty] at h,
    rw Dim_eq_Dim' h,
    apply finset.le_max',
    apply dim_set_complete,
    apply hx }
end

lemma Dim_le_iff_forall_dim_le {U : set P} (he : U.nonempty) (n : ℤ) : Dim U ≤ n ↔ ∀ x ∈ U, dim x ≤ n :=
begin
  split; intro h,
  { intros x hx,
    apply le_trans _ h,
    rw Dim_eq_Dim' he,
    apply finset.le_max',
    apply dim_set_complete U x hx },
  { rw Dim_eq_Dim' he,
    apply finset.max'_le,
    intros k hk,
    erw finset.mem_filter at hk,
    cases hk.right with w hw, cases hw with hw hw',
    rw hw',
    exact h w hw }
end
-- 1.1.16 (Codimension of an element)
noncomputable
def coDim {U : set P} {x : P} (hx : x ∈ U) : ℤ := 
  Dim U - dim x

lemma coDim_positive {U : set P} {x : P} (hx : x ∈ U) : 0 ≤ coDim hx :=
begin
  unfold coDim,
  rw [sub_nonneg],
  apply dim_le_Dim,
  exact hx,
end

-- 1.1.17 (Pure subset).
def pure (U : set P) := 
  ∀ x ∈ Max U, dim x = Dim' (set.nonempty_of_mem (Max_subset U H))

/- 1.2. Orientation and boundaries -/

-- We use bool in place of + / - so that all operations (eg ¬) are already implemented 
-- Convention : tt <-> + and ff <-> -

def orientation (P : FinPartialOrder) : Type* := Π {x y : P} (e : x ⟶ y), bool 

end ogpos

open ogpos

structure ogpos :=
(P : FinPartialOrder)
[P_graded : graded P]
(ε : orientation P)

instance : has_coe_to_sort ogpos Type* := ⟨λ X, X.P⟩

@[simp] lemma coe_to_FinPartialOrder (P : ogpos) : ↥P.P = ↥P := rfl

instance (P : ogpos) : graded P.P := P.P_graded

lemma eq_edges_orientation {P : ogpos} {x y : P} (e e' : x ⟶ y) : 
  P.ε e = P.ε e' := by  rw subsingleton.elim e e'

@[simp] lemma neg_eq_orientation {P : ogpos} {x y : P} {e : x ⟶ y} {α : bool} : ¬ P.ε e = α ↔ P.ε e = !α :=
begin
  nth_rewrite 0 ←bnot_bnot α,
  rw bool.not_eq_bnot,
end
-- Remark 1.2.4. TODO


-- -- We can view any subset as a FinPartialOrder
-- instance subset_to_FinPartial_order : has_coe (set ↥P) FinPartialOrder.{u} :=
-- { coe := λ U, 
--   { to_PartialOrder := PartialOrder.of U, 
--     is_fintype := begin simp, apply fintype.of_finite U, end
--   } }

-- def ι (U : set P) : U → (P : FinPartialOrder.{u}) := λ x, x

-- instance embedding (U : set P) : has_coe U (P : FinPartialOrder.{u}) := {coe := ι P U}

-- def orientation_restriction (P : FinPartialOrder.{u}) (ε : orientation.{u} P) (U : set P) : 
--   orientation.{u} U := λ x y f, @ε (ι P U x) _ f

-- instance ogpos_closed (Q : ogpos.{u}) (U : set Q) [is_closed U] : ogpos.{u} :=
-- { P := U,
--   ε := λ x y f, @ogpos.ε Q x y f }

-- 1.2.5 (Faces and cofaces)

namespace faces

variable {P : ogpos}

--1.2.5 (Faces and cofaces)
-- Would it have been better to do:
-- Σ y, { e : x ⟶ y // P.ε e = α } 
-- (but it's the same has we are working classicaly)

def Δ (α : bool) (x : P) := { y | ∃ e : y ⋖ x, P.ε e = α }

def coΔ (α : bool) (x : P) := { y | ∃ e : x ⋖ y, P.ε e = α }

lemma cov_of_Δ {α : bool} {x y : P} (hy : y ∈ Δ α x) : y ⋖ x :=
exists.elim hy (λ h _, h)

lemma cov_of_coΔ {α : bool} {x y : P} (hy : y ∈ coΔ α x) : x ⋖ y :=
exists.elim hy (λ h _, h)

-- 1.2.6 (Input and output boundaries)
-- We allow n < 0 in the general case, and set it to ∅ in that case, for convenience
def sΔ' (α : bool) (n : ℤ) (U : set P) : set P := 
{x ∈ grading U n | coΔ (!α) x ∩ U = ∅}

def sΔ (α : bool) (n : ℤ) (U : set P) : set P := 
dite (0 ≤ n) (λ (h : 0 ≤ n), sΔ' α n U) (λ _, ∅)

lemma sΔ_eq_sΔ' {α : bool} {n : ℤ} {U : set P} (hn : 0 ≤ n) : sΔ α n U = sΔ' α n U :=
begin
  unfold sΔ,
  rw dif_pos hn,
end

lemma sΔ_subset {α : bool} {n : ℤ} {U : set P} : sΔ α n U ⊆ U :=
begin
  by_cases h : 0 ≤ n,
  { rw sΔ_eq_sΔ' h, intros x hx, 
    exact hx.left.left },
  { unfold sΔ, rw dif_neg h, apply empty_subset }
end

lemma mem_sΔ_iff_mem_sΔ' {α : bool} {n : ℤ} {U : set P} (hn : 0 ≤ n) (x : P) :
  x ∈ sΔ α n U ↔ x ∈ sΔ' α n U := by rw sΔ_eq_sΔ' hn

def δ' (α : bool) (n : ℤ) (U : set P) : set P := 
cl (sΔ α n U) ∪ ⋃ (k : { k // k < n}), cl (grading (Max U) k)

def δ (α : bool) (n : ℤ) (U : set P) : set P :=
dite (0 ≤ n) (λ (h : 0 ≤ n), δ' α n U) (λ _, ∅)

def sδ (α : bool) (n : ℤ) (x : P) := δ α n (cl ({x} : set P))

lemma sδ_def {α : bool} {n : ℤ} {x : P} : sδ α n x = δ α n (cl ({x} : set P)) := rfl

lemma δ_eq_δ' {α : bool} {n : ℤ} {U : set P} (hn : 0 ≤ n) : δ α n U = δ' α n U :=
begin
  unfold δ,
  rw dif_pos hn,
end

instance is_closed_δ' {α : bool} {n : ℤ} {U : set P} : is_closed (δ' α n U) :=
{ is_eq_cl := 
  begin
    unfold δ',
    rw [←closure_Union_eq_Union_closure, closure_union_eq_union_closure, 
        closure_indempotent, closure_indempotent],
  end
}

lemma mem_δ_iff_mem_δ' {α : bool} {n : ℤ} {U : set P} (hn : 0 ≤ n) (x : P) : 
  x ∈ δ α n U ↔ x ∈ δ' α n U := by rw δ_eq_δ' hn

-- Remark 1.2.8.
lemma Δ_eq_sΔ_cl_singleton (α : bool) (x : P) : Δ α x = sΔ α (dim x - 1) (cl {x}) :=
begin
  by_cases (1 ≤ dim x); unfold sΔ; simp [h],
  { unfold Δ sΔ', ext y, simp, split; intro h1,
    { cases h1 with h1 e,
      erw mem_set_of, split,
      { rw mem_cl_singleton_iff_below,
        apply and.intro (covby.le h1),
        simp,
        rw finite.eq_pred_eq_succ,
        apply dim_plus_one_of_covby h1},
      { ext w, 
        rw [mem_inter_iff, mem_empty_iff_false, iff_false, mem_cl_singleton_iff_below], 
        erw mem_set_of,
        intro h3,
        cases h3.left with h4 e',  
        have hwx : w = x := eq_of_double_covby h4 h1 h3.right,
        have Ph14 : P.ε h1 = P.ε h4 := 
        begin
          rw hwx at h4,
          convert eq_edges_orientation (hom_of_cov h1) (hom_of_cov h4),
        end,
        rw [e, e'] at Ph14,
        cases α; rw bnot at Ph14; injection Ph14 } },
    { erw [mem_sep_iff, finite.eq_pred_eq_succ, mem_cl_singleton_iff_below] at h1,
      let e := covby_of_dim_plus_one_of_le h1.left.left h1.left.right,
      use e, 
      by_contra' h,
      rw neg_eq_orientation at h,
      apply not_mem_empty x, 
      rw [←h1.right, mem_inter_iff],
      exact and.intro ⟨e, h⟩ (subset_cl _ (mem_singleton x)) } },
  { by_cases h1 : (dim x = ↑0),
    { rw dim_zero_iff_normal x at h1, unfold Δ, ext w,
      rw [mem_empty_iff_false, iff_false], intro hx, rw mem_set_of_eq at hx,
      cases hx with e hx,
      apply not_covby_of_normal h1 w e },
    { exfalso, apply h1, rw not_le at h, have : ↑0 ≤ dim x := dim_pos x, linarith } }
end

variables (U : set P)

--Lemma 1.2.9
lemma dim_δ_n_le_n (α : bool) (n : ℕ) : Dim (δ α n U) ≤ n :=
begin
  by_cases h : (δ α n U).nonempty,
  { rw Dim_le_iff_forall_dim_le h,
    intros x hx,
    rw δ_eq_δ' (nat.cast_nonneg n) at hx,
    cases hx,
    { cases hx with y hy,
      cases hy with hy hle,
      rw sΔ_eq_sΔ' (nat.cast_nonneg n) at hy,
      have k := hy.left.right,
      rw ←hy.left.right,
      exact dim_monotonic hle },
    { cases hx with V hV, cases hV with hV hVin,
      cases hV with k hk, simp only at hk,
      rw ←hk at hVin,
      cases hVin with y hy,
      cases hy with hy hle,
      apply le_trans (dim_monotonic hle),
      rw hy.right,
      apply le_of_lt k.prop } },
  { unfold Dim, rw dif_neg h,
    linarith }
end

lemma sΔ_subset_δ [is_closed U] (α : bool) (n : ℤ) :
  sΔ α n U ⊆ grading (δ α n U) n :=
begin
  by_cases h : 0 ≤ n,
  { rw δ_eq_δ' h, 
    intros x hx,
    erw mem_set_of,
    split,
    { apply mem_union_left, rw sΔ_eq_sΔ' h at |- hx,
      apply subset_cl _ hx },
    { simp only, 
      rw sΔ_eq_sΔ' h at hx,
      exact hx.left.right } },
  { unfold sΔ δ, rw [dif_neg h, dif_neg h], exact empty_subset _ } 
end

--Lemma 1.2.10 -- point 1
lemma nth_grading_nth_boundary_eq_sΔ [is_closed U] (α : bool) (n : ℤ) : 
  grading (δ α n U) n = sΔ α n U :=
begin
  refine subset_antisymm _ (sΔ_subset_δ U α n),
  intros x hx,
  by_cases h : 0 ≤ n,
  { cases hx,
    rw sΔ_eq_sΔ' h,
    rw δ_eq_δ' h at hx_left,
    cases hx_left, 
    { cases hx_left with y hy, 
      cases hy with hy hle,
      rw sΔ_eq_sΔ' h at hy,
      have hdim : dim x = dim y :=
      begin
        apply eq.trans hx_right,
        symmetry,
        erw [mem_sep_iff, mem_sep_iff] at hy,
        exact hy.left.right
      end,
      rw eq_of_le_of_eq_dim hle hdim,
      exact hy},
    { rw set.mem_Union at hx_left,
      cases hx_left with k hx,
      cases hx with y hy,
      cases hy with hy hle, 
      exfalso,
      apply not_lt_of_le (dim_monotonic hle),
      rw hx_right,
      rw hy.right,
      exact k.prop } },
  { exfalso,
    rw ←hx.right at h,
    exact h (dim_pos x) }
end

--Lemma 1.2.10 -- point 2
-- tedious proof...
lemma Max_kth_grading_nth_boundary_eq_Max_kth_grading [is_closed U] (α : bool) (n : ℤ) 
  (k : { k // k < n}) : grading (Max (δ α n U)) k = grading (Max U) k :=
begin
  by_cases h : 0 ≤ k.val,
  { apply subset_antisymm;
    have hn : 0 ≤ n := le_of_lt (has_lt.lt.trans_le' k.prop h),
    { rw δ_eq_δ' hn,
      intros x hx,
      cases hx with hx_l hx_dim,
      erw mem_sep_iff,
      refine and.intro _ hx_dim,
      cases hx_l.left with hx hx,
      { cases hx with y hy,
        cases hy with hy hle,
        have hxy : x = y := 
        begin
          refine eq_of_maximal_of_le _ _ hle hx_l,
          left,
          apply subset_cl _ hy,
        end,
        exfalso,
        rw sΔ_eq_sΔ' hn at hy,
        apply lt_irrefl n,
        rw [hxy, hy.left.right] at hx_dim,
        nth_rewrite 0 hx_dim,
        exact k.prop },
      { rw set.mem_Union at hx,
        cases hx with i hi,
        cases hi with y hy,
        cases hy with hy hle,
        have hxy : x = y := 
        begin
          refine eq_of_maximal_of_le _ _ hle hx_l,
          right,
          rw set.mem_Union, use i,
          apply subset_cl _ hy,
        end,
        rw hxy,
        exact hy.left } },
    { intros x hx,
      erw mem_set_of,
      refine and.intro _ hx.right,
      erw mem_set_of,
      erw δ_eq_δ' hn,
      split,
      { right, rw mem_Union, use k,
        apply subset_cl _ hx, },
      { intros u hu hcov,
        cases hu,
        { cases hu with y hy,
          cases hy with hy hle,
          have hmax := hx.left,
          erw mem_set_of at hmax,
          apply hmax.right _ hcov,
          apply mem_is_cl_of_le _ hle, exact _inst_1,
          apply sΔ_subset hy },
        { rw mem_Union at hu,
          cases hu with i hu,
          cases hu with y hy,
          cases hy with hy hle,
          cases hx.left,
          apply right _ hcov,
          apply mem_is_cl_of_le _ hle, exact _inst_1,
          apply Max_subset _ hy.left } } } },
  { erw grading_empty_of_dim_le_zero _ _ h,
    erw grading_empty_of_dim_le_zero _ _ h }
end

lemma maximal_iff_no_coΔ {x : P} : maximal U x ↔ (x ∈ U) ∧ ∀ α : bool, coΔ α x ∩ U = ∅ :=
begin
  split; intro h,
  { apply and.intro h.left,
    intro α,
    rw eq_empty_iff_forall_not_mem,
    intros y hy,
    cases hy.left with e _,
    apply h.right hy.right e },
  { apply and.intro h.left,
    intros u hu hcov,
    cases h with _ h,
    specialize h (P.ε hcov),
    rw eq_empty_iff_forall_not_mem at h,
    specialize h u,
    apply h,
    apply mem_inter _ hu,
    erw mem_set_of,
    use hcov }
end

-- Lemma 1.2.11 -- point 1
lemma nth_grading_Max_eq_inter_sΔ (U : set P) [is_closed U] (n : ℤ) : 
  grading (Max U) n = sΔ tt n U ∩ sΔ ff n U :=
begin
  by_cases h : 0 ≤ n,
  { ext,
    split; intro hx,
    { cases hx,
      erw mem_set_of at hx_left,
      rw maximal_iff_no_coΔ at hx_left,
      rw [mem_inter_iff, sΔ_eq_sΔ' h, sΔ_eq_sΔ' h],
      repeat {erw mem_sep_iff},
      apply and.intro 
        (and.intro ((and.intro hx_left.left hx_right)) (hx_left.right (!tt))) 
        (and.intro ((and.intro hx_left.left hx_right)) (hx_left.right (!ff))) },
    { erw [mem_set_of, mem_set_of],
      rw [sΔ_eq_sΔ' h, sΔ_eq_sΔ' h] at hx,
      rw maximal_iff_no_coΔ, simp only,
      apply and.intro (and.intro hx.left.left.left _) hx.left.left.right,
      intro α, cases α,
      exact hx.left.right,
      exact hx.right.right } },
  { unfold sΔ, rw [  grading_empty_of_dim_le_zero _ n h,dif_neg h, dif_neg h, empty_inter] }
end

-- Lemma 1.2.11 -- point 2 -- (Max U)_n = U_n
lemma Dim_grading_Max_eq_Dim_grading [is_closed U] :
  grading (Max U) (Dim U) = grading U (Dim U) :=
begin
  by_cases h : U.nonempty,
  { apply subset_antisymm; intros x hx; erw mem_sep_iff; apply and.intro _ hx.right,
    { apply Max_subset _ hx.left },
    { erw mem_set_of, 
      apply and.intro hx.left,
      intros u hu hcov,
      apply lt_irrefl (Dim U),
      have hdim := dim_plus_one_of_covby hcov,
      have hdim_u := dim_le_Dim U u hu,
      rw ←hdim at hdim_u,
      rw hx.right at hdim_u,
      erw int.add_one_le_iff at hdim_u,
      exact hdim_u } },
  { rw Dim_empty' h, rw [grading_empty_of_dim_le_zero, grading_empty_of_dim_le_zero]; linarith }
end

-- Lemma 1.2.11 -- point 2 -- (Max U)_n = Δ^α_n U
lemma Dim_grading_Max_eq_sΔ [is_closed U] (α : bool) :
  grading (Max U) (Dim U) = sΔ α (Dim U) U :=
begin
  by_cases h : U.nonempty,
  { apply subset_antisymm,
    { rw nth_grading_Max_eq_inter_sΔ, 
      intros x hx,
      cases α,
      exact hx.right,
      exact hx.left },
    { rw Dim_grading_Max_eq_Dim_grading, 
      intros x hx,
      apply and.intro (sΔ_subset hx),
      rw sΔ_eq_sΔ' (Dim_pos h) at hx,
      exact hx.left.right } },
  { rw [Dim_grading_Max_eq_Dim_grading, Dim_empty'], 
    unfold sΔ, rw [dif_neg, grading_empty_of_dim_le_zero]; linarith,
    exact h }
end

-- Lemma 1.2.12 -- point 1
lemma δ_subset {α : bool} {n : ℤ} {U : set P} [is_closed U] : δ α n U ⊆ U :=
begin
  by_cases h : 0 ≤ n,
  { rw δ_eq_δ' h, 
    erw [union_subset_iff, ←closure_Union_eq_Union_closure],
    split; apply closure_sub,
    { apply sΔ_subset },
    { intros x hx,
      rw mem_Union at hx,
      cases hx with k hk,
      apply Max_subset, 
      exact hk.left } },
  { unfold δ, rw dif_neg h, apply empty_subset }
end

-- Lemma 1.2.12 -- point 2
lemma δ_eq_iff_Dim_le_n (α : bool) (n : ℕ) (U : set P) [is_closed U] : δ α n U = U ↔ Dim U ≤ n :=
begin
  split,
  { contrapose, intros h he,
    rw not_le at h,
    have hdim : Dim (δ α n U) < Dim U := has_le.le.trans_lt (dim_δ_n_le_n U α n) h,
    rw he at hdim,
    exact (lt_irrefl _ hdim) },
  { intros hn,
    apply subset_antisymm,
    apply δ_subset,
    have hU : U = ⋃ k : { k // k ≤ Dim U}, cl (grading (Max U) k) :=
    begin
      conv_lhs
      { rw U_eq_cl_MaxU U,
        rw ←eq_Union_grading_bounded' (Max U) (Dim U) (Dim_monotonic (Max_subset U)),
        rw closure_Union_eq_Union_closure }
    end,
    nth_rewrite 0 hU,
    intros x hx,
    rw δ_eq_δ' (nat.cast_nonneg n), 
    unfold δ', 
    rw le_iff_lt_or_eq at hn,
    cases hn; rw mem_Union at hx; cases hx with k hk,
    { right, rw mem_Union, use k,
      apply has_lt.lt.trans_le' hn k.prop,
      exact hk },
    { by_cases hkDim : ↑k = Dim U,
      { left,
        rw [←hn, ←Dim_grading_Max_eq_sΔ], rw hkDim at hk,
        exact hk },
      { right, rw mem_Union, use k,
        rw ←hn,
        { rw lt_iff_le_and_ne,
          apply and.intro k.prop, rw ne.def,
          exact hkDim },
        { exact hk } } } }
end

-- Intersting variant where we can have n arbitrary int (converse is false I beleive)
lemma δ_eq_of_Dim_le_n (α : bool) (n : ℤ) (U : set P) [is_closed U] (hle : Dim U ≤ n) : 
  δ α n U = U := 
begin
  by_cases h : 0 ≤ n,
  { rw [←int.to_nat_of_nonneg h, δ_eq_iff_Dim_le_n, 
         int.to_nat_of_nonneg h],
    exact hle },
  { unfold δ, erw dif_neg h, symmetry, 
    apply empty_of_Dim_neg,
    rw not_le at h,
    exact has_le.le.trans_lt hle h }
end

-- Auxiliary lemma for next Corollary
lemma Dim_mem_Dim_eq_min_nonempty [is_closed U] (h : U.nonempty) : 
  (Dim U).to_nat ∈ {n : ℕ | ∀ α, δ α n U = U} :=
begin
  rw mem_set_of, 
  intro α,
  rw [δ_eq_iff_Dim_le_n, int.to_nat_of_nonneg (Dim_pos h)] 
end

lemma Dim_eq_min' [is_closed U] (h : U.nonempty) : 
  (Dim U).to_nat = @Inf ℕ _ {n : ℕ | ∀ α, δ α n U = U} :=
begin
  apply linarith.eq_of_not_lt_of_not_gt; intro hlt,
  { apply nat.not_mem_of_lt_Inf hlt,
    apply Dim_mem_Dim_eq_min_nonempty U h },
  { have hmem := Inf_mem (nonempty_of_mem (Dim_mem_Dim_eq_min_nonempty U h)), 
    rw mem_set_of at hmem,
    specialize hmem tt,
    rw δ_eq_iff_Dim_le_n at hmem,
    apply not_le_of_lt hlt,
    rw ←@nat.cast_le ℤ,
    rw int.to_nat_of_nonneg (Dim_pos h),
    exact hmem }
end

-- Corollary 1.2.13
lemma Dim_eq_min [is_closed U] (h : U.nonempty) :
  Dim U = @Inf ℕ _ {n : ℕ | ∀ α, δ α n U = U} :=
begin
  rw [←int.to_nat_of_nonneg (Dim_pos h), int.coe_nat_inj'],
  apply Dim_eq_min' U h
end

-- The next three lemmas can be factored by a LOT

-- Lemma 1.2.14 -- point 1 -- note : the union is not disjoint here 
lemma Max_union (U V : set P) [is_closed U] [is_closed V] : 
  Max (U ∪ V) = (Max U ∩ Max V) ∪ (Max U) \ V ∪ (Max V) \ U :=
begin
  apply subset_antisymm; intros x hx,
  by_cases hU : x ∈ U, 
  { by_cases hV : x ∈ V,
    { left, left, split, 
      { apply and.intro hU, intros u hu hcov, apply hx.right (mem_union_left _ hu) hcov },
      { apply and.intro hV, intros u hu hcov, apply hx.right (mem_union_right _ hu) hcov } },
    { left, right, 
      rw mem_diff, apply and.intro _ hV, 
      apply and.intro hU, intros u hu hcov,
      apply hx.right (mem_union_left _ hu) hcov } },
  { by_cases hV : x ∈ V,
    { right,
      rw mem_diff, apply and.intro _ hU, 
      apply and.intro hV, intros u hu hcov,
      apply hx.right (mem_union_right _ hu) hcov },
    { exfalso, cases hx, rw mem_union at hx_left, 
      cases hx_left,
      exact hU hx_left, 
      exact hV hx_left } },
  cases hx, 
  { cases hx; apply and.intro (mem_union_left _ hx.left.left);
    intros u hu hcov; cases hu,
    { apply hx.left.right hu hcov },
    { apply hx.right.right hu hcov },
    { rw mem_diff at hx,
      apply hx.left.right hu hcov },
    { rw mem_diff at hx,
      apply hx.right,
      apply mem_is_cl_of_lt hu (covby.lt hcov) } },
  { apply and.intro (mem_union_right _ hx.left.left),
    intros u hu hcov, cases hu,
    { rw mem_diff at hx,
      apply hx.right,
      apply mem_is_cl_of_lt hu (covby.lt hcov) },
    { rw mem_diff at hx,
      apply hx.left.right hu hcov } },
end

-- Lemma 1.2.14 -- point 2 -- note : the union is not disjoint here 
lemma sΔ_union (U V : set P) [is_closed U] [is_closed V] (n : ℤ) (α : bool) : 
    sΔ α n (U ∪ V) = (sΔ α n U ∩ sΔ α n V) ∪ (sΔ α n U) \ V ∪ (sΔ α n V) \ U :=
begin
  by_cases hn : 0 ≤ n,
  { rw [sΔ_eq_sΔ' hn, sΔ_eq_sΔ' hn, sΔ_eq_sΔ' hn], 
    apply subset_antisymm; intros x hx,
    by_cases hU : x ∈ U, 
    { by_cases hV : x ∈ V,
      { left, left, split,
        { apply and.intro (and.intro hU hx.left.right), 
          simp only, rw eq_empty_iff_forall_not_mem, intros e he,
          cases hx, rw eq_empty_iff_forall_not_mem at hx_right,
          apply hx_right e, rw inter_distrib_left, left, exact he },
        { apply and.intro (and.intro hV hx.left.right), 
          simp only, rw eq_empty_iff_forall_not_mem, intros e he,
          cases hx, rw eq_empty_iff_forall_not_mem at hx_right,
          apply hx_right e, rw inter_distrib_left, right, exact he } }, 
      { left, right, rw mem_diff, apply and.intro _ hV,
        { apply and.intro (and.intro hU hx.left.right), 
          simp only, rw eq_empty_iff_forall_not_mem, intros e he,
          cases hx, rw eq_empty_iff_forall_not_mem at hx_right,
          apply hx_right e, rw inter_distrib_left, left, exact he } } },
    { by_cases hV : x ∈ V,
      { right, rw mem_diff, apply and.intro _ hU,
        { apply and.intro (and.intro hV hx.left.right), 
          simp only, rw eq_empty_iff_forall_not_mem, intros e he,
          cases hx, rw eq_empty_iff_forall_not_mem at hx_right,
          apply hx_right e, rw inter_distrib_left, right, exact he } },
      { exfalso, cases hx, erw mem_sep_iff at hx_left, 
        cases hx_left.left,
        exact hU h, 
        exact hV h } },
    cases hx,
    { cases hx; apply and.intro (grading_monotonic (subset_union_left _ _) _ hx.left.left);
      simp only; rw inter_distrib_left; rw union_empty_iff, 
      { apply and.intro hx.left.right hx.right.right },
      { rw mem_diff at hx, 
        apply and.intro hx.left.right,
        rw eq_empty_iff_forall_not_mem, 
        intros u hu,
        cases hu, 
        apply hx.right,
        erw mem_set_of at hu_left,
        cases hu_left with hcov _,
        apply mem_is_cl_of_lt hu_right (covby.lt hcov) } },
    { apply and.intro (grading_monotonic (subset_union_right _ _) _ hx.left.left), 
      simp only, rw inter_distrib_left; rw union_empty_iff, 
      rw mem_diff at hx, 
      refine and.intro _ hx.left.right,
      rw eq_empty_iff_forall_not_mem, 
      intros u hu,
      cases hu, 
      apply hx.right,
      erw mem_set_of at hu_left,
      cases hu_left with hcov _,
      apply mem_is_cl_of_lt hu_right (covby.lt hcov) } },
  { unfold sΔ, rw [dif_neg hn, dif_neg hn, dif_neg hn], 
    rw [empty_inter, empty_union, empty_diff, empty_diff, empty_union] }
end

-- Corollary 1.2.15
lemma δ_sub_distrib (U V : set P) [is_closed U] [is_closed V] (n : ℤ) (α : bool) :
  δ α n (U ∪ V) ⊆  δ α n U ∪  δ α n V :=
begin
  by_cases h : 0 ≤ n,
  { rw [δ_eq_δ' h, δ_eq_δ' h, δ_eq_δ' h], 
    intros x hx,
    cases hx,
    { rw [sΔ_union, closure_union_eq_union_closure, closure_union_eq_union_closure] at hx,
      cases hx,
      { cases hx,
        left, left,
        apply closure_monotonic (inter_subset_left _ _) hx,
        left, left,
        refine closure_monotonic _ hx,
        apply diff_subset },
      { right, left, 
        refine closure_monotonic _ hx,
        apply diff_subset } },
    { rw mem_Union at hx, cases hx with k hk,
      cases hk with w hw,
      cases hw with hw hle,
      have hw' := hw,
      cases hw, rw Max_union at hw_left,
      cases hw_left,
      { cases hw_left;
        { left, right, rw mem_Union, use k,
          refine mem_cl_of_below _ _ hle, 
          apply subset_cl _,
          apply and.intro hw_left.left hw_right } },
      { right, right, rw mem_Union, use k,
          refine mem_cl_of_below _ _ hle, 
          apply subset_cl _,
          apply and.intro hw_left.left hw_right } } },
  { unfold δ, erw dif_neg h, apply empty_subset }
end

end faces
 
namespace maps

open faces 

-- 1.3.1
structure map (P Q : ogpos) :=
(app : P → Q)
(comm : ∀ (x : P) (n : ℤ) (α : bool),  app '' (sδ α n x) = sδ α n (app x))

lemma map.comm' {P Q : ogpos} (f : map P Q) : 
  ∀ (x : P) (n : ℤ) (α : bool),  f.app '' (δ α n (cl {x})) = δ α n (cl {f.app x}) := f.comm

instance map_to_fun (P Q : ogpos) : has_coe_to_fun (map P Q) (λ _, P → Q) := ⟨λ m, m.app⟩

variables {P Q : ogpos} (f : map P Q)

lemma cl_map_eq_map_cl (x : P) : cl { f x } = f '' (cl {x}) :=
begin
  let m := max (Dim (cl {f x})) (Dim (cl {x})),
  rw ←@δ_eq_of_Dim_le_n Q tt m (cl {f x}) _ (le_max_left _ _),  
  erw ←f.comm', 
  rw @δ_eq_of_Dim_le_n P tt m (cl {x}) _ (le_max_right _ _), 
  refl, 
end

-- Lemma 1.3.2 -- point 1
instance image_closed (U : set P) [is_closed U] : is_closed (f '' U) :=
{ is_eq_cl := 
  begin
    refine subset_antisymm _ (subset_cl _),
    nth_rewrite 0 ←is_closed_eq_union_closure_singleton U,
    rw [image_Union₂, closure_Union_eq_Union_closure₂],
    intros x hx, rw mem_Union₂ at hx, 
    cases hx with w hw, cases hw with hw hin,
    rw [←cl_map_eq_map_cl, closure_indempotent] at hin,
    rw [←is_closed_eq_union_closure_singleton U, image_Union₂],
    rw mem_Union₂,
    use w,
    rw ←cl_map_eq_map_cl,
    apply and.intro hw hin
  end }

-- Lemma 1.3.2 -- point 2
lemma map_monotonic {x y : P} (hle : x ≤ y) : f x ≤ f y :=
begin
  rw [←mem_cl_singleton_iff_below (f y), cl_map_eq_map_cl, mem_image],
  use x,
  rw mem_cl_singleton_iff_below,
  apply and.intro hle (eq.refl _)
end

lemma mem_image_of_le_image {x : P} {y : Q} (hxy : y ≤ f x) : ∃ x', y = f x' :=
begin
  rw [←mem_cl_singleton_iff_below, cl_map_eq_map_cl, mem_image] at hxy,
  cases hxy with w hw,
  use w, symmetry, exact hw.right
end

-- Lemma 1.3.2 -- point 3
lemma dim_map_le_dim (x : P) : dim (f x) ≤ dim x :=
begin
  have k : (dim x).to_nat ∈ {n : ℕ | ∀ α, δ α n (cl ({f x} : set Q)) = (cl {f x})} :=
  begin
    rw mem_set_of, intro α,
    erw ←f.comm',
    rw [int.to_nat_of_nonneg (dim_pos _),δ_eq_of_Dim_le_n _ _ _(le_of_eq (Dim_cl_singleton x))],
    rw cl_map_eq_map_cl,
    refl
  end,
  have hInf := nat.Inf_le k,
  rw [←int.coe_nat_le, int.to_nat_of_nonneg (dim_pos x)] at hInf,
  convert hInf,
  rw ←Dim_cl_singleton,
  apply Dim_eq_min,
  use f x, rw mem_cl_singleton_iff_below
end

-- 1.3.3 -- inclusion of ogpos
structure ι_map (P Q : ogpos) extends map P Q :=
(inj : function.injective app)

instance ι_map_to_fun (P Q : ogpos) : has_coe_to_fun (ι_map P Q) (λ _, P → Q) := ⟨λ m, m.app⟩

instance ι_image_closed (i : ι_map P Q) (U : set P) [is_closed U] : 
  is_closed (i '' U) := maps.image_closed i.to_map U

variables {i : ι_map P Q} (x : P)



-- Lemma 1.3.4 -- point 1
lemma ι_map_reflects {x y : P} (hle : i x ≤ i y) : x ≤ y :=
begin
  erw [←mem_cl_singleton_iff_below, cl_map_eq_map_cl, mem_image] at hle,
  cases hle with w hw,
  rw [←mem_cl_singleton_iff_below, ←i.inj (hw.right)],
  exact hw.left
end

lemma ι_map_st_reflects {x y : P} (hle : i x < i y) : x < y :=
begin
  rw lt_iff_le_and_ne,
  apply and.intro (ι_map_reflects (le_of_lt hle)),
  intro h, 
  rw h at hle,
  apply lt_irrefl (i y) hle
end

def ι_map.to_o (i : ι_map P Q) : P ↪o Q :=
{ to_fun := i,
  inj' := i.inj,
  map_rel_iff' := λ x y, iff.intro (ι_map_reflects) (λ h, map_monotonic _ h) }

lemma ι_map.cov_inv (i : ι_map P Q) {x y : P} (hcov : i x ⋖ i y) : x ⋖ y :=
covby.of_image i.to_o hcov


lemma ι_map_st_monotonic {x y : P} (hlt : x < y) : i x < i y :=
begin
  rw lt_iff_le_and_ne,
  apply and.intro (map_monotonic _ (le_of_lt hlt)),
  intro heq,
  apply ne_of_lt hlt,
  apply i.inj heq
end

-- Lemma 1.3.4 -- point 3 (cover)
lemma ι_map.cov (i : ι_map P Q) {x y : P} (e : x ⋖ y) : i x ⋖ i y :=
begin
  apply covby_of_eq (ι_map_st_monotonic (covby.lt e)),
  intros z' hx hy,
  cases mem_image_of_le_image i.to_map hy,
  rw h,
  congr,
  apply eq_of_between_cov_right e,
  { rw h at hx, exact ι_map_st_reflects hx },
  { rw h at hy, exact ι_map_reflects hy }
end

-- ι_maps are prefunctors between the Hasses's diagrams
def ι_map.to_prefunctor (i : ι_map P Q) : prefunctor P Q :=
{ obj := λ x, i x,
  map := λ x y hcov, i.cov hcov }

lemma ι_map_path_length (i : ι_map P Q) {x y : P} (p : path x y) : 
  (i.to_prefunctor.map_path p).length = p.length :=
begin
  induction p with z _ p q h,
  { rw [path.length_nil, prefunctor.map_path_nil, path.length_nil] },
  { rw [path.length_cons, prefunctor.map_path_cons, path.length_cons, h] }
end

-- Lemma 1.3.4 -- point 2
lemma ι_map_preserves_dim (i : ι_map P Q) (x : P) : dim (i x) = dim x :=
begin
  apply le_antisymm (dim_map_le_dim i.to_map x), 
  unfold dim,
  rw ←ι_map_path_length i,
  rw int.coe_nat_le_coe_nat_iff,
  apply path_length_le_max_path_length
end

lemma mem_sδ_of_cov {x y : P} (e : x ⋖ y) {α : bool} (hε : P.ε e = α) : x ∈ sδ α (dim y - 1) y :=
begin
  unfold sδ δ,
  erw dif_pos (dim_minus_one_pos_of_cov e),
  left,
  apply subset_cl _,
  rw sΔ_eq_sΔ' (dim_minus_one_pos_of_cov e),
  apply and.intro,
  { erw mem_set_of,
    rw mem_cl_singleton_iff_below,
    apply and.intro e.le,
    rw [←dim_plus_one_of_covby e, coe_is_one_hom.coe_one, add_tsub_cancel_right] },
  { simp only, rw eq_empty_iff_forall_not_mem,
    intros w hw,
    cases hw.left with e' he',
    have hwy : w = y :=
    begin
      cases covby.eq_or_eq e e'.le _,
      { exfalso, rw h at e',
        apply e'.ne', refl },
      { assumption },
      { rw ←mem_cl_singleton_iff_below,
        exact hw.right }
    end,
    rw hwy at e',
    apply bool.bnot_ne_self α,
    rw [←he', ←hε],
    congr, rw hwy }
end 

-- Lemma 1.3.4 -- point 3 (orientation)
lemma ι_map_preserves_orientation (i : ι_map P Q) {x y : P} (e : x ⋖ y) {α : bool} (hε : P.ε e = α) : 
  Q.ε (i.cov e) = α :=
begin
  have hi := mem_image_of_mem i (mem_sδ_of_cov e hε),
  erw i.comm at hi,
  unfold sδ δ at hi,
  erw dif_pos (dim_minus_one_pos_of_cov e) at hi,
  cases hi, 
  { rw ←ι_map_preserves_dim i at hi,
    erw [←Δ_eq_sΔ_cl_singleton, mem_set_of] at hi,
    cases hi with w hw,
    cases hw with hw hle,
    cases hw with e' he',
    rw ←he', congr,
    apply eq_of_between_cov_left (i.cov e) e'.lt hle },
  { exfalso, 
    rw mem_Union at hi,
    cases hi with k hx,
    erw mem_set_of at hx,
    cases hx with w hw,
    cases hw with hw hg,
    erw mem_set_of at hw,
    cases hw,
    clear hw_left hε,
    have hk := k.prop,
    erw ←hw_right at hk,
    rw ←(dim_plus_one_of_covby e) at hk,
    simp at hk,
    apply not_le_of_lt hk,
    rw ←ι_map_preserves_dim i,
    exact dim_monotonic hg }
end

-- Next are (also useful for later?) auxiliary lemmas to prove the isomorphism of corollary 1.3.5
variable (i)

lemma ι_map_mem_cl (U : set P) (x : P) : i x ∈ cl (i '' U) ↔ x ∈ cl U :=
begin
  split; intro hx,
  { cases hx with w hw,
    cases hw with hw hle,
    rw mem_image at hw,
    cases hw with x' hx',
    use x',
    apply and.intro hx'.left, rw ←hx'.right at hle,
    apply ι_map_reflects hle },
  { cases hx with w hw, cases hw with hw hle,
    use i w,
    erw function.injective.mem_set_image i.inj,
    apply and.intro hw (map_monotonic i.to_map hle) }
end

lemma ι_map_mem_sΔ_iff (U : set P) [is_closed U] (α : bool) (n : ℤ) : 
  i x ∈ sΔ α n (i '' U) ↔ x ∈ sΔ α n U  :=
begin
  by_cases h : 0 ≤ n,
  { symmetry,
    rw [sΔ_eq_sΔ' h, sΔ_eq_sΔ' h], 
    split; intro hx,
    { split,
      { split, 
        use x,
        apply and.intro (hx.left.left) (eq.refl _),
        simp only, rw ι_map_preserves_dim,
        exact hx.left.right },
      { simp only,
        rw eq_empty_iff_forall_not_mem, intros y hy,
        cases hy,
        rw mem_image at hy_right,
        cases hy_right with x' hx',
        erw [←hx'.right, mem_set_of] at hy_left,
        cases hy_left with e he,
        have hempty := hx.right,
        erw eq_empty_iff_forall_not_mem at hempty,
        apply hempty x',
        apply and.intro _ hx'.left,
        erw mem_set_of,
        use  i.cov_inv e,
        by_contra, simp at h,
        apply bool.bnot_ne_self α,
        have hcontr := ι_map_preserves_orientation i (i.cov_inv e) h,
        rw he at hcontr,
        exact hcontr } },
      split,
      { erw [mem_set_of, mem_set_of, function.injective.mem_set_image i.inj] at hx,
        apply and.intro hx.left.left,
        simp only, rw ←(ι_map_preserves_dim i x),
        exact hx.left.right },
      { simp only, rw eq_empty_iff_forall_not_mem, intros w hw,
        cases hx,
        erw [mem_sep_iff, mem_set_of] at hw,
        cases hw.left with e he,
        rw eq_empty_iff_forall_not_mem at hx_right,
        apply hx_right (i w),
        refine and.intro _ (mem_image_of_mem _ hw.right),
        use i.cov e,
        apply ι_map_preserves_orientation i e he } },
  { unfold sΔ, 
    rw [dif_neg h, dif_neg h, mem_empty_iff_false, mem_empty_iff_false] }
end

lemma ι_map_max_iff (U : set P) (x : P) : maximal (i '' U) (i x) ↔ maximal U x:=
begin
  split; intro hx; split,
   { rw ←function.injective.mem_set_image i.inj,
    exact hx.left },
  { intros u hu hcov,
    apply hx.right (mem_image_of_mem i hu) (i.cov hcov) },
  { erw function.injective.mem_set_image i.inj,
    exact hx.left },
  { intros u hu hcov,
    cases hu with w hw,
    rw ←hw.right at hcov,
    apply hx.right hw.left (i.cov_inv hcov) },
end

lemma ι_map_Max_iff (U : set P) (x : P) : i x ∈ Max (i '' U) ↔ x ∈ Max U  :=
begin
  erw [mem_set_of, mem_set_of],
  exact ι_map_max_iff i U x
end

lemma ι_map_Max_eq (U : set P) : i '' Max U = Max (i '' U) :=
begin
  apply subset_antisymm; intros x hx,
  { cases hx with w hw,
    rw ←ι_map_Max_iff i at hw, rw ←hw.right,
    exact hw.left },
  { cases hx.left, 
    use w, rw ←ι_map_Max_iff i, rw ←h.right at hx,
    exact and.intro hx h.right }
end

lemma ι_map_cl_sΔ (U : set P) [is_closed U] (α : bool) (n : ℤ) (x : P) : 
 i x ∈ cl (sΔ α n (i '' U)) ↔ x ∈ cl (sΔ α n U) :=
begin
  split; intros hx; cases hx with w hw; cases hw with hw hle,
  { by_cases h : 0 ≤ n,
    { rw sΔ_eq_sΔ' h at hw ⊢,
      cases hw.left, rw mem_image at left,
      cases left with y hy,
      use y,
      rw ←hy.right at hle,
      refine and.intro _(ι_map_reflects hle),
      rw [←hy.right, ι_map_preserves_dim] at right,
      apply and.intro (and.intro hy.left right),
      rw [←hy.right, ←sΔ_eq_sΔ' h, ι_map_mem_sΔ_iff i y, sΔ_eq_sΔ' h] at hw,
      exact hw.right },
    { unfold sΔ at *,
      rw dif_neg h at hw,
      exfalso,
      apply not_mem_empty w hw } },
  { use i w,
    rw ι_map_mem_sΔ_iff i w,
    apply and.intro hw (map_monotonic i.to_map hle) },
end

lemma ι_map_mem_grading (U : set P) (n : ℤ) (x : P) : i x ∈ grading (i '' U) n ↔ x ∈ grading U n :=
begin
  split; intro hx,
  { apply and.intro ((function.injective.mem_set_image i.inj).elim_left hx.left), 
    simp only, rw ←ι_map_preserves_dim i x,
    exact hx.right },
  { apply and.intro (mem_image_of_mem i hx.left), 
    simp only, rw ι_map_preserves_dim,
    exact hx.right}
end

-- Corollary 1.3.5 -- mem version (this only proves )
lemma ι_map.iso_mem (U : set P) [is_closed U] (α : bool) (n : ℤ) (x : P) : 
  i x ∈ δ α n (i '' U) ↔ x ∈ δ α n U :=
begin
  by_cases h : 0 ≤ n,
  { rw [δ_eq_δ' h, δ_eq_δ' h], 
    symmetry,
    split; intro hx; cases hx,
    { left, rw ι_map_cl_sΔ, exact hx },
    { rw mem_Union at hx, cases hx with k hk,
      right, rw mem_Union, use k,
      cases hk with w hw, cases hw with hw hle,
      use i w, refine and.intro _ (map_monotonic i.to_map hle),
      rw [←ι_map_mem_grading i (Max U)] at hw,
      refine and.intro _ hw.right,
      rw ι_map_Max_iff,
      rw ←function.injective.mem_set_image i.inj,
      exact hw.left },
    { left, rw ←ι_map_cl_sΔ i, exact hx },
    { rw mem_Union at hx, cases hx with k hk,
      right, rw mem_Union, use k,
      cases hk with w hw, cases hw with hw hle,
      cases hw.left.left with x' hx',
      use x', rw ←hx'.right at hle hw,
      refine and.intro _ (ι_map_reflects hle), 
      rw [←ι_map_mem_grading i, ι_map_Max_eq],
      exact hw } },
  { unfold δ, rw [dif_neg h, dif_neg h, mem_empty_iff_false, mem_empty_iff_false] }
end

lemma ι_map_δ_sub (U : set P) [is_closed U] (α : bool) (n : ℤ) : i '' δ α n U ⊆ δ α n (i '' U) :=
begin
  intros y hy,
  cases hy with x hx, 
  rw ←i.iso_mem at hx,
  rw ←hx.right,
  exact hx.left
end

lemma ι_map_δ_sub' (U : set P) [is_closed U] (α : bool) (n : ℤ) : δ α n (i '' U) ⊆ i '' δ α n U :=
begin
  by_cases h : 0 ≤ n,
  { rw [δ_eq_δ' h, δ_eq_δ' h], 
    intros y hy,
    cases hy,
    { cases hy with w hw, cases hw with hw hle,
      have hyU : y ∈ i '' U := 
      begin
        apply mem_is_cl_of_le _ hle,
        apply_instance,
        rw sΔ_eq_sΔ' h at hw,
        exact hw.left.left
      end,
      rw mem_image at hyU,
      cases hyU with x' hx',
      use x',
      apply and.intro _ hx'.right,
      rw [←δ_eq_δ' h, ←i.iso_mem, δ_eq_δ' h],
      left,
      use w, rw hx'.right,
      apply and.intro hw hle },
    { rw mem_Union at hy, cases hy with k hk, cases hk with w hw, cases hw with hw hle,
      have hyU : y ∈ i '' U := 
      begin
        apply mem_is_cl_of_le _ hle,
        apply_instance,
        apply Max_subset _ hw.left,
      end,
      rw mem_image at hyU,
      cases hyU with x' hx',
      use x',
      apply and.intro _ hx'.right,
      right, rw mem_Union, use k,
      rw ←ι_map_Max_eq at hw, cases hw.left with z hz,
      use z,
      rw [←hx'.right, ←hz.right] at hle,
      apply and.intro _ (ι_map_reflects hle),
      apply and.intro hz.left, simp only,
      rw ←ι_map_preserves_dim i, rw hz.right,
      exact hw.right } },
  { unfold δ, erw dif_neg h, apply empty_subset }
end

lemma ι_map_δ_eq  (U : set P) [is_closed U] (α : bool) (n : ℤ) : i '' δ α n U = δ α n (i '' U) :=
subset_antisymm (ι_map_δ_sub i U α n) (ι_map_δ_sub' i U α n)

-- Corollary 1.3.5 -- bij version (on the range)
lemma ι_map_restrict_bij (U : set P) [is_closed U] (α : bool) (n : ℤ) : 
  set.bij_on i (δ α n U) (δ α n (i '' U)) :=
begin
  rw ←ι_map_δ_eq,
  apply set.inj_on.bij_on_image (inj_on_of_injective i.inj _)
end


end maps