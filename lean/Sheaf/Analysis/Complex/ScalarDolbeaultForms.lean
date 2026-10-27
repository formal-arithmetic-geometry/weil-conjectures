module

public import Sheaf.Geometry.Manifold.KahlerCoordinateData
public import Mathlib.Order.Fin.Basic

/-! # Scalar antiholomorphic forms in complex coordinates

Source: Demailly, Complex Analytic and Differential Geometry, I §3.C, (3.14)--(3.17).
(blueprint: def-sfb-scalar-dolbeault-forms)

Increasing coordinate tuples index the wedge basis. Coefficients are functions on the
actual domain, not ambient representatives. Their zero extensions are used only to test
smoothness and take derivatives within the open domain. Thus no boundary regularity or
extension across the boundary is required. The existing conjugate Wirtinger derivative
supplies precisely the coefficient derivative, including its factor of one half.
-/

@[expose] public section

open scoped ContDiff

namespace ComplexManifold

/-- Scalar `(0,q)` coefficient fields on a domain in `ℂ^n`. The increasing tuple `J`
stands for `dbar z_(J 0) ∧ ... ∧ dbar z_(J (q-1))`. If `q > n`, there are no tuples,
so there is only the zero field. Source: Demailly I §3.C, (3.14).
(blueprint: def-sfb-scalar-dolbeault-forms) -/
abbrev ScalarAntiholomorphicForm (n q : ℕ) (U : Set (Fin n → ℂ)) :=
  (Fin q ↪o Fin n) → U → ℂ

/-- The zero extension of a coefficient on its domain. Only its germ at interior points
is used. Source: Demailly I §3.C, coordinate coefficient functions in (3.14).
(blueprint: def-sfb-scalar-dolbeault-forms) -/
noncomputable def scalarCoefficientExtension {n : ℕ} (U : Set (Fin n → ℂ))
    (f : U → ℂ) (z : Fin n → ℂ) : ℂ := by
  classical
  exact if hz : z ∈ U then f ⟨z, hz⟩ else 0

/-- Smoothness means real smoothness of each coefficient on the domain. On open `U`
this tests only interior germs, even though the extension may jump at the boundary.
Source: Demailly I §3.C, smooth coefficients in (3.14).
(blueprint: def-sfb-scalar-dolbeault-forms) -/
def IsSmoothScalarForm {n q : ℕ} {U : Set (Fin n → ℂ)}
    (α : ScalarAntiholomorphicForm n q U) : Prop :=
  ∀ J : Fin q ↪o Fin n, ContDiffOn ℝ ∞ (scalarCoefficientExtension U (α J)) U

/-- Restriction of all coefficients along an inclusion of domains.
Source: Demailly I §3.E, restriction to a neighborhood in Lemma (3.29).
(blueprint: def-sfb-scalar-dolbeault-forms) -/
def restrictScalarForm {n q : ℕ} {U V : Set (Fin n → ℂ)} (hVU : V ⊆ U)
    (α : ScalarAntiholomorphicForm n q U) : ScalarAntiholomorphicForm n q V :=
  fun J z ↦ α J ⟨z.val, hVU z.property⟩

/-- The coefficient formula for `∂bar`: delete the `r`th wedge index and differentiate
in that coordinate, with sign `(-1)^r`. Repeated indices vanish automatically in this
wedge-basis formula. The reused `wirtingerBarPartial` is `(∂x + i ∂y)/2`.
Source: Demailly I §3.C, (3.14). (blueprint: def-sfb-scalar-dolbeault-forms) -/
noncomputable def scalarDolbeault {n q : ℕ} {U : Set (Fin n → ℂ)}
    (α : ScalarAntiholomorphicForm n q U) : ScalarAntiholomorphicForm n (q + 1) U :=
  fun K z ↦ ∑ r : Fin (q + 1), (-1 : ℂ) ^ r.val *
    wirtingerBarPartial
      (scalarCoefficientExtension U (α ((Fin.succAboveOrderEmb r).comp K))) U (K r) z.val

end ComplexManifold
