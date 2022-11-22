import order.interval
import order.locally_finite
import data.set.basic
import data.nat.interval


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
(is_eq_cl : U = cl U)

lemma closed_eq_closure (U : set P) [is_closed U] : U = cl U := is_closed.is_eq_cl
 
lemma empty_eq_cl_empty : (∅ : set P) = cl ∅ :=
begin
  ext, unfold cl, simp
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
  rw closed_eq_closure V,
  exact closure_monotonic _ _ hsub,
end

lemma closure_indempotent (U : set P) : cl U = cl (cl U) :=
begin
  apply subset_antisymm,
  { exact subset_cl _ },
  { intros x hx,
    cases hx with w hw,
    cases hw with hw hlew,
    apply mem_cl_of_below hw _ hlew }
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
lemma closure_union_eq_union_closure (ι : Sort*) (s : ι → set P) : cl (⋃ i, s i) = ⋃ i, cl (s i) :=
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

variable (U : set P)

-- 1.1.7 (Maximal element)
def maximal (x : P) : Prop := (x ∈ U) ∧ ∀ {u}, u ∈ U → ¬(x ⋖ u)
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

lemma not_covering_of_normal {x : P} (norm : is_normal x) : ∀ y : P, ¬ y ⋖ x :=
λ y h, (norm y).false h

-- It is equivalent to say that there is no element below x
lemma normal_iff_no_lt (x : P) : is_normal x ↔ ∀ y : P, ¬ y < x :=
begin
  split; intros h y,
  { intro hlt, 
    cases exists_left_cov_of_lt hlt with w hw,
    exact not_covering_of_normal h _ (hom_of_cov hw.right) },
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
def dim (x : P) : nat := (max_path x).path.length

-- The only elements of dim 0 are the normal one 
lemma dim_0_iff_normal (x : P) : dim x = 0 ↔ is_normal x :=
begin
  unfold dim,
  split; intro h,
  { intros y, refine ⟨_⟩, intro e,
    have n := maximal_path.normal_cod (max_path x), 
    rw ←path.eq_of_length_zero _ h at n,
    exact (n y).false e },
  { by_contra' hm,
    apply hm,
    apply all_paths_length_0_of_normal h }
end

--Lemma 1.1.12
lemma dim_monotonic (x y : P) (hle : x ≤ y) : dim x ≤ dim y :=
begin
  cases lt_or_eq_of_le hle,
  { have p := path_of_lt h, 
    unfold dim,
    have hh : (maximal_path_concat p (max_path x)).path.length = (max_path y).path.length := 
      same_length y _ _,
    rw ←hh, erw path.length_comp, simp },
  { rw h }
end

variables (U) 

-- 1.1.13 (Grading of a subset)
def grading (n : ℕ) : set P := { x ∈ U | dim x = n }

@[simp] lemma mem_grading_dim (x : P) (hx : x ∈ U) : x ∈ grading U (dim x) :=
begin
  unfold grading, simp [hx],
end

lemma eq_union_grading : U = ⋃ n, grading U n :=
begin
  apply subset_antisymm; intros x hx; simp at *,
  { use dim x, simp [hx]},
  { cases hx with _ h, erw mem_set_of_eq at h,
    exact h.left }
end

variable [is_closed U]


-- Various auxiliary results about dimension of a subset
namespace dim

-- This won't be the final dim_set
-- We only use it to prove it's bounded
def dim_set : set ℕ := { n | ∃ x ∈ U, n = dim x }

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
def pick {n : ℕ} (hn : n ∈ dim_set U) : {x : P // x ∈ U ∧ n = dim x} :=
begin
  convert (classical.indefinite_description _ hn), 
  simp,
end

noncomputable
def undounded_pick_greater (h : ∀ (N : ℕ), ∃ (n : ℕ), n ∈ dim_set U ∧ N < n) (n : ℕ) : 
  {x : P // n < dim x } :=
begin
  have k := classical.indefinite_description _ (h n),
  have pt := pick U k.prop.left,
  refine ⟨pt.val, _⟩,
  erw ←pt.prop.right,
  exact k.prop.right,
end

variables {U} (x0 : P) (hx0 : x0 ∈ U)

noncomputable
def next (h : ∀ (N : ℕ), ∃ (n : ℕ), n ∈ dim_set U ∧ N < n) (xn : P) := undounded_pick_greater U h (dim xn)

noncomputable
def dim_seq (h : ∀ (N : ℕ), ∃ (n : ℕ), n ∈ dim_set U ∧ N < n) : ℕ → P 
| 0       := x0
| (n + 1) := next h (dim_seq n)

lemma dim_seq_lt_succ (h : ∀ (N : ℕ), ∃ (n : ℕ), n ∈ dim_set U ∧ N < n) :
  ∀ n, dim (dim_seq x0 h n) < dim (dim_seq x0 h (n + 1)) :=
begin
  intro n,
  unfold dim_seq next,
  exact (undounded_pick_greater U h (dim (dim_seq x0 h n))).prop,
end

lemma dim_seq_lt_pred (h : ∀ (N : ℕ), ∃ (n : ℕ), n ∈ dim_set U ∧ N < n) :
  ∀ n m, n < m → dim (dim_seq x0 h n) < dim (dim_seq x0 h m) :=
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

lemma dim_congr_contra (x y : P) : dim x < dim y → x ≠ y :=
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
lemma bounded_dim_set' (x : P) (U : set P) [is_closed U] : ∃ N, ∀ n ∈ dim_set U, n ≤ N :=
begin
  by_contra' h,
  apply finite.no_forall_neq_preds (dim_seq x h),
  apply dim_seq_neq_preds,
end

-- And if P is empty, we can as well show it is bounded (trivially)
lemma bounded_dim_set (U : set P) [is_closed U] : ∃ N, ∀ n ∈ dim_set U, n ≤ N :=
begin
  by_cases h : is_empty P,
  { use 0, intros n hn, exfalso, 
    exact h.false (pick U hn).val }, 
  { simp at h,
    apply bounded_dim_set' (classical.choice h) }
end

-- Do I really need to do this?
noncomputable
def dim_set_injective (U : set P) [is_closed U] : 
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
def upper_bound (U : set P) [is_closed U] : { N // ∀ n ∈ dim_set U, n ≤ N } := 
classical.indefinite_description _ (bounded_dim_set U)  

lemma dim_mem_dim_set (U : set P) [is_closed U] : ∀ x ∈ U, dim x ∈ dim_set U :=
begin
  intros x hx,
  use x,
  exact and.intro hx (eq.refl _)
end

-- The two useful constructions from this namespace

-- The upper bound
noncomputable
def M (U : set P) [is_closed U] := (dim.upper_bound U).val

-- The fact that it's an upper bound
lemma M_prop {U : set P} [is_closed U] : ∀ x ∈ U, dim x ≤ M U :=
begin
  intros x hx,
  exact (upper_bound U).prop (dim x) (dim_mem_dim_set U x hx)
end

end dim

noncomputable
def dim_set : finset ℕ := 
finset.filter (λ n, ∃ x ∈ U, n = dim x) (finset.Icc 0 (dim.M U))

lemma dim_set_complete : ∀ x ∈ U, dim x ∈ dim_set U :=
begin
  intros x hx,
  erw finset.mem_filter,
  split,
  { rw finset.mem_Icc, simp, apply dim.M_prop _ hx },
  { use x, use hx }
end

@[simp] lemma dim_set_empty : dim_set (∅ : set P) = ∅ :=
begin
  unfold dim_set, simp,
end

@[simp] lemma dim_set_of_is_empty (hempty : U = ∅) : dim_set U = ∅ :=
begin
  unfold dim_set, ext, simp,
  intros hle x hx,
  rw [hempty, set.mem_empty_iff_false] at hx,
  exfalso,
  exact hx
end

-- 1.1.14 (Dimension of a subset)
noncomputable
def Dim [is_closed U] : with_bot ℕ := finset.max (dim_set U)

lemma Dim_empty : Dim (∅ : set P) = ⊥ := by { unfold Dim, simp }

lemma dim_set_nonempty_of_U_nonempty {U : set P} [is_closed U] (hnempty : U.nonempty) : 
  (dim_set U).nonempty :=
begin
  cases hnempty with w hw,
  use dim w,
  apply dim_set_complete U w hw,
end

-- To work directly in ℕ with non empty sets
noncomputable
def Dim' [is_closed U] (hnempty : U.nonempty) : ℕ := 
finset.max' (dim_set U) (dim_set_nonempty_of_U_nonempty hnempty)

lemma Dim_eq_Dim' [is_closed U] (hnempty : U.nonempty) : some (Dim' U hnempty) = Dim U :=
finset.coe_max' _

-- 1.1.15
lemma Dim'_cl_singleton (x : P) : 
  Dim' (cl ({x} : set P)) (closure_nonempty (set.singleton_nonempty x)) = dim x :=
begin
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

lemma Dim_cl_singleton (x : P) : Dim (cl ({x} : set P)) = some (dim x) :=
by { rw [←Dim_eq_Dim', Dim'_cl_singleton] }

-- 1.1.16 (Codimension of an element)
noncomputable
def coDim {U : set P} [is_closed U] {x : P} (hx : x ∈ U) : ℤ := 
  Dim' U (set.nonempty_of_mem hx) - dim x

def coDim_positive {U : set P} [is_closed U] {x : P} (hx : x ∈ U) : 0 ≤ coDim hx :=
begin
  unfold coDim,
  rw [sub_nonneg, nat.cast_le],
  apply finset.le_max' _ _ (dim_set_complete _ _ hx)
end

-- 1.1.17 (Pure subset).
def pure (U : set P) [is_closed U] := 
  ∀ x ∈ Max U, dim x = Dim' U (set.nonempty_of_mem (Max_subset U H))


/- 1.2. Orientation and boundaries -/

variable (P)

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
def sΔ' (α : bool) (n : nat) (U : set P) [is_closed U] : set P := 
{x ∈ grading U n | coΔ (to_bool (¬↥α)) x ∩ U = ∅}

def sΔ (α : bool) (n : int) (U : set P) [is_closed U] : set P := 
dite (0 ≤ n) (λ (h : 0 ≤ n), sΔ' α n.to_nat U) (λ _, ∅)

def δ' (α : bool) (n : nat) (U : set P) [is_closed U] : set P := 
cl (sΔ α n U) ∪ ⋃ (k : finset.Ico 0 n), cl (grading (Max U) k)

def δ (α : bool) (n : int) (U : set P) [is_closed U] : set P :=
dite (0 ≤ n) (λ (h : 0 ≤ n), δ' α n.to_nat U) (λ _, ∅)
  
lemma Δ_eq_sΔ_cl_singleton (α : bool) (x : P) : Δ α x = sΔ α (dim x - 1) (cl {x}) :=
begin
  sorry
end
end faces