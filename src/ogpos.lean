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

lemma mem_is_cl_of_below {U : set P} [is_closed U] {x y : P} (hy : y ∈ U) (hle : x ≤ y) : x ∈ U :=
begin
  rw ←closed_eq_closure U at *,
  apply mem_cl_of_below hy x hle
end

instance empty_closed : is_closed (∅ : set P) := 
{ is_eq_cl := empty_eq_cl_empty} 

lemma closure_nonempty {U : set P} (hnempty : U.nonempty) : (cl U).nonempty :=
nonempty.mono (subset_cl U) hnempty

-- Lemma 1.1.5 - part 1
lemma closure_monotonic (U V : set P) (hsub : U ⊆ V) : cl U ⊆ cl V :=
λ x ⟨u, ⟨hu, hle⟩⟩, ⟨u, ⟨hsub hu, hle⟩⟩

-- Lemma 1.1.5 - part 2
lemma closure_sub {U V: set P} [is_closed V] (hsub : U ⊆ V) : cl U ⊆ V :=
begin
  rw ←closed_eq_closure V,
  exact closure_monotonic _ _ hsub,
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

variable (U : set P)

-- 1.1.7 (Maximal element)
def maximal (x : P) : Prop := (x ∈ U) ∧ ∀ {u}, u ∈ U → ¬(x ⋖ u)

lemma eq_of_maximal_of_le [is_closed U] {x y : P} (hy : y ∈ U) (hle : x ≤ y) (hmax : maximal U x) : x = y :=
begin
  rw le_iff_lt_or_eq at hle,
  cases hle,
  { cases exists_right_cov_of_lt hle with w hw,
    exfalso,
    apply hmax.right (mem_is_cl_of_below hy hw.right) hw.left },
  { assumption }
end

def Max : set P := { x | maximal U x }

def Max_subset : Max U ⊆ U := 
begin
  intros x hx,
  exact hx.left
end

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

variables (U) 

-- 1.1.13 (Grading of a subset)
def grading (n : ℤ) : set P := { x ∈ U | dim x = n }

@[simp] lemma mem_grading_dim (x : P) (hx : x ∈ U) : x ∈ grading U (dim x) :=
begin
  unfold grading, simp [hx],
end

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
          apply mem_is_cl_of_below _ hle, exact _inst_1,
          apply sΔ_subset hy },
        { rw mem_Union at hu,
          cases hu with i hu,
          cases hu with y hy,
          cases hy with hy hle,
          cases hx.left,
          apply right _ hcov,
          apply mem_is_cl_of_below _ hle, exact _inst_1,
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

-- Auxiliary lemma for next Corollary
lemma Dim_mem_Dim_eq_min_nonempty [is_closed U] (h : U.nonempty) : 
  (Dim U).to_nat ∈ {n : ℕ | ∀ α, δ α n U = U} :=
begin
  rw mem_set_of, 
  intro α,
  rw [δ_eq_iff_Dim_le_n, int.to_nat_of_nonneg (Dim_pos h)] 
end
-- Corollary 1.2.13
lemma Dim_eq_min' [is_closed U] (h : U.nonempty) (n : ℕ) : 
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


end faces
 
