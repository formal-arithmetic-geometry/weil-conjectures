module

public import Sheaf.AlgebraicGeometry.SmoothAnalyticData
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Coordinate presentations of Dolbeault sheaves

Source: Demailly, Complex Analytic and Differential Geometry, I §3.C and IV §6,
Example (6.13) (blueprint: def-sfb-dolbeault-sheaf-data).

The atlas is the existing varying-dimension analytic atlas. Sections are exactly compatible
smooth alternating tensors of the stated type, and holomorphic sections are exactly those
with analytic coefficients. Every map is fixed by its coordinate formula. No metric,
compactness, resolution exactness, or vanishing is part of this presentation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ContDiff

namespace AlgebraicGeometry.SmoothAnalytic

/-- Coordinate alternating tensor fields in all degrees, with values only on chart domains.
Source: Demailly I §3.C (blueprint: def-sfb-dolbeault-sheaf-data). -/
abbrev CoordinateForms {M : Type u} [TopologicalSpace M] (A : Atlas M) (U : Opens M) :=
  ∀ (k n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ)), c ∈ A.charts n →
    ∀ x : U, x.val ∈ c.source → ContinuousAlternatingMap ℝ (Fin n → ℂ) ℂ (Fin k)

open Classical in
/-- The coordinate coefficient field, extended by zero away from its open domain.
Only germs inside the domain are used. Source: Demailly I §3.C
(blueprint: def-sfb-dolbeault-sheaf-data). -/
def tensorCoordinates {M : Type u} [TopologicalSpace M] {A : Atlas M} {U : Opens M}
    (a : CoordinateForms A U) (k n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ))
    (hc : c ∈ A.charts n) :
    (Fin n → ℂ) → ContinuousAlternatingMap ℝ (Fin n → ℂ) ℂ (Fin k) :=
  fun z ↦ if h : c.symm z ∈ U ∧ c.symm z ∈ c.source then
    a k n c hc ⟨c.symm z, h.1⟩ h.2 else 0

/-- Smooth tensors of type `(p,q)`: smooth local coefficients, Jacobian transition law,
exterior-degree support, and the complex-structure eigenvalue `i(p-q)`.
Negative and excessive degrees give zero. This is the coordinate version of
`ComplexManifold.typeForms`, allowing varying chart dimension and open-set sections.
Source: Demailly I §3.C (blueprint: def-sfb-dolbeault-sheaf-data). -/
def IsSmoothType {M : Type u} [TopologicalSpace M] {A : Atlas M} {U : Opens M}
    (p q : ℤ) (a : CoordinateForms A U) : Prop :=
  (∀ (k n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ)) (hc : c ∈ A.charts n)
    (x : U), x.val ∈ c.source → ContDiffAt ℝ ∞ (tensorCoordinates a k n c hc) (c x.val)) ∧
  (∀ (k n m : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ))
    (d : OpenPartialHomeomorph M (Fin m → ℂ)) (hc : c ∈ A.charts n)
    (hd : d ∈ A.charts m) (x : U) (hx : x.val ∈ c.source) (hy : x.val ∈ d.source),
    a k n c hc x hx = (a k m d hd x hy).compContinuousLinearMap
      ((fderiv ℂ (d ∘ c.symm) (c x.val)).restrictScalars ℝ)) ∧
  (∀ (k n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ)) (hc : c ∈ A.charts n)
    (x : U) (hx : x.val ∈ c.source),
    (¬ (0 ≤ p ∧ p ≤ n ∧ 0 ≤ q ∧ q ≤ n) ∨ k ≠ (p + q).toNat) →
      a k n c hc x hx = 0) ∧
  (∀ (k n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ)) (hc : c ∈ A.charts n)
    (x : U) (hx : x.val ∈ c.source) (v : Fin k → (Fin n → ℂ)),
    (∑ j : Fin k, a k n c hc x hx (Function.update v j (Complex.I • v j))) =
      ((p - q : ℤ) : ℂ) * Complex.I * a k n c hc x hx v)

/-- Holomorphic `p`-forms: type `(p,0)` tensors with holomorphic coefficient fields.
In degree zero this is `IsHolomorphic`; in degree one the transition and analytic
conditions are those of `IsOneForm`, after restriction of scalars on covectors.
Source: Demailly I §3.C (blueprint: def-sfb-dolbeault-sheaf-data). -/
def IsHolomorphicForm {M : Type u} [TopologicalSpace M] {A : Atlas M} {U : Opens M}
    (p : ℕ) (a : CoordinateForms A U) : Prop :=
  IsSmoothType (p : ℤ) 0 a ∧
    ∀ (k n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ)) (hc : c ∈ A.charts n)
      (x : U), x.val ∈ c.source → AnalyticAt ℂ (tensorCoordinates a k n c hc) (c x.val)

/-- Sheaves of complex vector spaces on the open site, using Mathlib's category verbatim.
Source: Demailly IV §6 (blueprint: def-sfb-dolbeault-sheaf-data). -/
abbrev ComplexSheaves (M : Type u) [TopologicalSpace M] :=
  Sheaf (Opens.grothendieckTopology M) (ModuleCat.{u} (ULift.{u} ℂ))

/-- A fully normalized presentation of the smooth and holomorphic form sheaves and
Dolbeault operators. The range, restriction, type, and exterior-derivative requirements
fix the sheaves and arrows up to their unique section-compatible identifications.
The operators are not assumed to square to zero, and no exactness is assumed.
Source: Demailly I §3.C and IV §6, Example (6.13)
(blueprint: def-sfb-dolbeault-sheaf-data). -/
structure DolbeaultSheafData {M : Type u} [TopologicalSpace M] (A : Atlas M) where
  /-- Smooth form sheaves, with all integer bidegrees. -/
  smooth : ℤ → ℤ → ComplexSheaves M
  /-- Holomorphic form sheaves, including the holomorphic functions in degree zero. -/
  omega : ℕ → ComplexSheaves M
  /-- The actual coordinate tensors of a smooth section, with pointwise operations. -/
  smoothEval : ∀ (p q : ℤ) (U : Opens M),
    (smooth p q).obj.obj (op U) → CoordinateForms A U
  /-- Evaluation preserves linear combinations pointwise. -/
  smooth_linear : ∀ (p q : ℤ) (U : Opens M) (a b : (smooth p q).obj.obj (op U))
    (t : ℂ) (k n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ))
    (hc : c ∈ A.charts n) (x : U) (hx : x.val ∈ c.source),
    smoothEval p q U (a + (ULift.up t : ULift.{u} ℂ) • b) k n c hc x hx =
      smoothEval p q U a k n c hc x hx + t • smoothEval p q U b k n c hc x hx
  /-- Smooth tensors determine sections. -/
  smooth_injective : ∀ (p q : ℤ) (U : Opens M), Function.Injective (smoothEval p q U)
  /-- Precisely all smooth tensors of the indicated type are sections. -/
  smooth_range : ∀ (p q : ℤ) (U : Opens M) (a : CoordinateForms A U),
    (∃ s, smoothEval p q U s = a) ↔ IsSmoothType p q a
  /-- Restriction is the literal restriction of coordinate tensors. -/
  smooth_restrict : ∀ (p q : ℤ) (U V : Opens M) (h : V ≤ U)
    (s : (smooth p q).obj.obj (op U)) (k n : ℕ)
    (c : OpenPartialHomeomorph M (Fin n → ℂ)) (hc : c ∈ A.charts n)
    (x : V) (hx : x.val ∈ c.source),
    smoothEval p q V ((smooth p q).obj.map (homOfLE h).op s) k n c hc x hx =
      smoothEval p q U s k n c hc ⟨x.val, h x.property⟩ hx
  /-- The actual coordinate tensors of a holomorphic section. -/
  omegaEval : ∀ (p : ℕ) (U : Opens M),
    (omega p).obj.obj (op U) → CoordinateForms A U
  /-- Holomorphic evaluation preserves linear combinations pointwise. -/
  omega_linear : ∀ (p : ℕ) (U : Opens M) (a b : (omega p).obj.obj (op U))
    (t : ℂ) (k n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ))
    (hc : c ∈ A.charts n) (x : U) (hx : x.val ∈ c.source),
    omegaEval p U (a + (ULift.up t : ULift.{u} ℂ) • b) k n c hc x hx =
      omegaEval p U a k n c hc x hx + t • omegaEval p U b k n c hc x hx
  /-- Holomorphic tensors determine sections. -/
  omega_injective : ∀ (p : ℕ) (U : Opens M), Function.Injective (omegaEval p U)
  /-- Precisely all holomorphic tensors occur. -/
  omega_range : ∀ (p : ℕ) (U : Opens M) (a : CoordinateForms A U),
    (∃ s, omegaEval p U s = a) ↔ IsHolomorphicForm p a
  /-- Holomorphic restriction is restriction of the same tensors. -/
  omega_restrict : ∀ (p : ℕ) (U V : Opens M) (h : V ≤ U)
    (s : (omega p).obj.obj (op U)) (k n : ℕ)
    (c : OpenPartialHomeomorph M (Fin n → ℂ)) (hc : c ∈ A.charts n)
    (x : V) (hx : x.val ∈ c.source),
    omegaEval p V ((omega p).obj.map (homOfLE h).op s) k n c hc x hx =
      omegaEval p U s k n c hc ⟨x.val, h x.property⟩ hx
  /-- The augmentation is inclusion of the identical underlying tensors. -/
  inclusion : ∀ p : ℕ, omega p ⟶ smooth p 0
  /-- The augmentation's normalization. -/
  inclusion_eval : ∀ (p : ℕ) (U : Opens M) (s : (omega p).obj.obj (op U)),
    smoothEval p 0 U ((inclusion p).hom.app (op U) s) = omegaEval p U s
  /-- The antiholomorphic component, as a sheaf morphism, hence commuting with restriction. -/
  dbar : ∀ p q : ℤ, smooth p q ⟶ smooth p (q + 1)
  /-- The holomorphic component, also commuting with restriction. -/
  del : ∀ p q : ℤ, smooth p q ⟶ smooth (p + 1) q
  /-- Their sum is exactly the ordinary coordinate exterior derivative. Types distinguish
  the two components uniquely. No square-zero identity is imposed here. -/
  exterior_derivative : ∀ (p q : ℤ) (U : Opens M) (s : (smooth p q).obj.obj (op U))
    (k n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ)) (hc : c ∈ A.charts n)
    (x : U) (hx : x.val ∈ c.source) (v : Fin (k + 1) → (Fin n → ℂ)),
    smoothEval p (q + 1) U ((dbar p q).hom.app (op U) s) (k + 1) n c hc x hx v +
      smoothEval (p + 1) q U ((del p q).hom.app (op U) s) (k + 1) n c hc x hx v =
        extDeriv (tensorCoordinates (smoothEval p q U s) k n c hc) (c x.val) v
  /-- Holomorphic differentiation from functions to holomorphic one-forms. -/
  holomorphicDerivative : omega 0 ⟶ omega 1
  /-- Its coefficient formula is the complex derivative of the function coefficient. -/
  holomorphicDerivative_eval : ∀ (U : Opens M) (s : (omega 0).obj.obj (op U))
    (n : ℕ) (c : OpenPartialHomeomorph M (Fin n → ℂ)) (hc : c ∈ A.charts n)
    (x : U) (hx : x.val ∈ c.source) (v : Fin 1 → (Fin n → ℂ)),
    omegaEval 1 U (holomorphicDerivative.hom.app (op U) s) 1 n c hc x hx v =
      fderiv ℂ (fun z ↦ tensorCoordinates (omegaEval 0 U s) 0 n c hc z Fin.elim0)
        (c x.val) (v 0)

/-- Derived global sections in complex-vector-space sheaves, with no change of
coefficient category. Source: Demailly IV §3 and §6
(blueprint: def-sfb-dolbeault-sheaf-data). -/
def complexGlobalSections {M : Type u} [TopologicalSpace M] :
    ComplexSheaves M ⥤ ModuleCat.{u} (ULift.{u} ℂ) :=
  sheafToPresheaf _ _ ⋙ (evaluation (Opens M)ᵒᵖ (ModuleCat.{u} (ULift.{u} ℂ))).obj (op ⊤)

/-- Global sections is additive, by the existing additive sheaf inclusion and evaluation.
Source: Demailly IV §3 (blueprint: def-sfb-dolbeault-sheaf-data). -/
instance complexGlobalSections_additive {M : Type u} [TopologicalSpace M] :
    (complexGlobalSections (M := M)).Additive :=
  inferInstanceAs ((sheafToPresheaf (Opens.grothendieckTopology M)
    (ModuleCat.{u} (ULift.{u} ℂ)) ⋙
      (evaluation (Opens M)ᵒᵖ (ModuleCat.{u} (ULift.{u} ℂ))).obj (op ⊤)).Additive)

end AlgebraicGeometry.SmoothAnalytic
