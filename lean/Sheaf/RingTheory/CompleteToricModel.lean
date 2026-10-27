module
public import Sheaf.RingTheory.LogRegularSaturationNormality
public import Sheaf.AlgebraicGeometry.LogEtaleRestrictionStalkComparison
public import Sheaf.AlgebraicGeometry.LogRegularSharpChart
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Geometry.Convex.Cone.Basic
public import WeilConjectures.RingTheory.CohenRing

/-!
# Complete toric coefficient models and rational facet notation

Source: ILO, Travaux de Gabber, Exposé VI 1.6(i)--(ii), printed p. 70, for the
complete models `B_k(P,n)` and `B_C(P,n)/(θ)`; the lattice, rational cone, facet,
primitive-normal and boundary-ideal notation is the auxiliary statement notation of
`lem-trf-complete-toric-facet-valuations`
(blueprint: def-trf-complete-toric-model).

The complete-model constructions reuse the published `AddMonoidAlgebra` model of
`lem-trf-log-regular-saturation-normality`; the coefficient ring and the monoid live
in independent universes.
-/
@[expose] public section
universe u v w
noncomputable section
namespace ToricMonoid

/-- The monoid polynomial ring `L[P][t₁, …, tₙ]`.
Source: ILO VI 1.6(i)--(ii), printed p. 70 (blueprint: def-trf-complete-toric-model). -/
abbrev PolynomialRing (L : Type v) [CommRing L] (P : Type u) [AddCommMonoid P]
    (n : ℕ) := MvPolynomial (Fin n) (AddMonoidAlgebra L P)
/-- The chart ideal `(z^q : q ≠ 0, t₁, …, tₙ)` of `L[P][t₁, …, tₙ]`, the published
`AddMonoidAlgebra.localModelBoundaryIdeal`.
Source: ILO VI 1.6(i)--(ii), printed p. 70 (blueprint: def-trf-complete-toric-model). -/
abbrev chartIdeal (L : Type v) [CommRing L] (P : Type u) [AddCommMonoid P]
    (n : ℕ) := AddMonoidAlgebra.localModelBoundaryIdeal L P n
/-- The completion ideal `(m_L, z^q : q ≠ 0, t₁, …, tₙ)`, the published
`AddMonoidAlgebra.localModelCompletionIdeal`.
Source: ILO VI 1.6(i)--(ii), printed p. 70 (blueprint: def-trf-complete-toric-model). -/
abbrev completionIdeal (L : Type v) [CommRing L] [IsLocalRing L]
    (P : Type u) [AddCommMonoid P] (n : ℕ) : Ideal (PolynomialRing L P n) :=
  AddMonoidAlgebra.localModelCompletionIdeal L P n
/-- The complete model `B_L(P,n)`: the `AdicCompletion` of `L[P][t₁, …, tₙ]` at the
completion ideal, the published `AddMonoidAlgebra.CompletedLocalModel`.
Source: ILO VI 1.6(i)--(ii), printed p. 70 (blueprint: def-trf-complete-toric-model). -/
abbrev Complete (L : Type v) [CommRing L] [IsLocalRing L]
    (P : Type u) [AddCommMonoid P] (n : ℕ) :=
  AddMonoidAlgebra.CompletedLocalModel L P n
/-- The chart monomial `z^q` in `B_L(P,n)`: the image of `single q 1` under the constants
and the completion map. It is the map of `AddMonoidAlgebra.completedLocalModelMonomial`
with the coefficient and monoid universes independent.
Source: ILO VI 1.6(i)--(ii), printed p. 70 (blueprint: def-trf-complete-toric-model). -/
def monomial (L : Type v) [CommRing L] [IsLocalRing L]
    (P : Type u) [AddCommMonoid P] (n : ℕ) (q : P) : Complete L P n :=
  algebraMap (MvPolynomial (Fin n) (AddMonoidAlgebra L P)) (Complete L P n)
    (MvPolynomial.C (AddMonoidAlgebra.single q (1 : L)))
/-- The extended chart ideal `(z^q : q ≠ 0, t₁, …, tₙ) B_L(P,n)`, the published
`AddMonoidAlgebra.completedLocalModelBoundaryIdeal`.
Source: ILO VI 1.6(ii), printed p. 70 (blueprint: def-trf-complete-toric-model). -/
abbrev completedChartIdeal (L : Type v) [CommRing L] [IsLocalRing L]
    (P : Type u) [AddCommMonoid P] (n : ℕ) : Ideal (Complete L P n) :=
  AddMonoidAlgebra.completedLocalModelBoundaryIdeal L P n

/-- Complete toric coefficient model predicate: `R` with chart monomials `z` is, by a ring
isomorphism carrying the model monomials to `z`, either (i) `B_k(P,n)` for a field `k`,
or (ii) `B_C(P,n)/(θ)` for a Cohen ring `C` of residue characteristic `p` and
`θ - p ∈ (z^q : q ≠ 0, t₁, …, tₙ) B_C(P,n)`.
Source: ILO VI 1.6(i)--(ii), printed p. 70 (blueprint: def-trf-complete-toric-model). -/
def IsCompleteModel (P : Type u) [AddCommMonoid P] (n : ℕ)
    (R : Type w) [CommRing R] (z : P → R) : Prop :=
  (∃ (k : Type v) (_ : Field k) (e : Complete k P n ≃+* R),
    ∀ q : P, z q = e (monomial k P n q)) ∨
  (∃ (C : Type v) (_ : CommRing C) (_ : IsLocalRing C) (p : ℕ),
    IsCohenRing p C ∧ ∃ (θ : Complete C P n),
      θ - (p : Complete C P n) ∈ completedChartIdeal C P n ∧
        ∃ e : (Complete C P n ⧸ Ideal.span {θ}) ≃+* R,
          ∀ q : P, z q = e (Ideal.Quotient.mk _ (monomial C P n q)))

/-- The lattice `G = P^gp`, written additively.
Source: ILO VI 1.4, printed p. 69, and the statement notation of
`lem-trf-complete-toric-facet-valuations` (blueprint: def-trf-complete-toric-model). -/
abbrev Lattice (P : Type u) [AddCommMonoid P] :=
  Additive (Algebra.GrothendieckGroup (Multiplicative P))
/-- The image of `q ∈ P` in `G = P^gp`.
Source: ILO VI 1.4, printed p. 69 (blueprint: def-trf-complete-toric-model). -/
def latticePoint {P : Type u} [AddCommMonoid P] (q : P) : Lattice P :=
  Additive.ofMul (Algebra.GrothendieckGroup.of (Multiplicative.ofAdd q))
/-- The rational space `V = G ⊗_ℤ ℚ`, written `ℚ ⊗[ℤ] G`.
Source: statement notation of `lem-trf-complete-toric-facet-valuations`
(blueprint: def-trf-complete-toric-model). -/
abbrev RationalSpace (P : Type u) [AddCommMonoid P] := TensorProduct ℤ ℚ (Lattice P)
/-- The image `1 ⊗ q` of `q ∈ P` in `V`.
Source: statement notation of `lem-trf-complete-toric-facet-valuations`
(blueprint: def-trf-complete-toric-model). -/
def rationalPoint {P : Type u} [AddCommMonoid P] (q : P) : RationalSpace P :=
  TensorProduct.tmul ℤ (1 : ℚ) (latticePoint q)
/-- The cone `σ ⊂ V` of nonnegative rational combinations of the images of `P` (the hull
contains `0 = 1 ⊗ 0`, so it equals the pointed hull).
Source: statement notation of `lem-trf-complete-toric-facet-valuations`
(blueprint: def-trf-complete-toric-model). -/
def cone (P : Type u) [AddCommMonoid P] : ConvexCone ℚ (RationalSpace P) :=
  ConvexCone.hull ℚ (Set.range (rationalPoint (P := P)))
/-- `F` is a facet of `σ`: `F = σ ∩ ker h` for a nonzero rational form `h` nonnegative on
`σ`, with `dim span F = dim V - 1`.
Source: statement notation of `lem-trf-complete-toric-facet-valuations`
(blueprint: def-trf-complete-toric-model). -/
def IsFacet (P : Type u) [AddCommMonoid P] (F : Set (RationalSpace P)) : Prop :=
  ∃ h : RationalSpace P →ₗ[ℚ] ℚ, h ≠ 0 ∧
    (∀ v ∈ cone P, 0 ≤ h v) ∧
    F = {v | v ∈ cone P ∧ h v = 0} ∧
    Module.finrank ℚ (Submodule.span ℚ F) + 1 = Module.finrank ℚ (RationalSpace P)
/-- The type of facets of `σ`.
Source: statement notation of `lem-trf-complete-toric-facet-valuations`
(blueprint: def-trf-complete-toric-model). -/
abbrev Facet (P : Type u) [AddCommMonoid P] := {F : Set (RationalSpace P) // IsFacet P F}
/-- `h` is the rational extension of `ν : G → ℤ` to `V`: `h (1 ⊗ g) = ν g`.
Source: statement notation of `lem-trf-complete-toric-facet-valuations`
(blueprint: def-trf-complete-toric-model). -/
def IsRationalExtension {P : Type u} [AddCommMonoid P]
    (ν : Lattice P →+ ℤ) (h : RationalSpace P →ₗ[ℚ] ℚ) : Prop :=
  ∀ g : Lattice P, h (TensorProduct.tmul ℤ (1 : ℚ) g) = (ν g : ℚ)
/-- `ν : G → ℤ` is a primitive normal of the facet `F`: image `ℤ`, nonnegative on `P`, and
`F = σ ∩ ker ν` for its rational extension.
Source: statement notation of `lem-trf-complete-toric-facet-valuations`
(blueprint: def-trf-complete-toric-model). -/
def IsPrimitiveNormal {P : Type u} [AddCommMonoid P] (F : Facet P)
    (ν : Lattice P →+ ℤ) : Prop :=
  Function.Surjective ν ∧ (∀ q : P, 0 ≤ ν (latticePoint q)) ∧
    ∃ h : RationalSpace P →ₗ[ℚ] ℚ, IsRationalExtension ν h ∧
      F.val = {v | v ∈ cone P ∧ h v = 0}
/-- The boundary ideal `p_F = (z^q : q ∈ P, q ∉ F) R` of a facet.
Source: statement notation of `lem-trf-complete-toric-facet-valuations`
(blueprint: def-trf-complete-toric-model). -/
noncomputable def boundaryIdeal {P : Type u} [AddCommMonoid P]
    {R : Type w} [CommRing R] (z : P → R) (F : Facet P) : Ideal R :=
  Ideal.span {a | ∃ q : P, rationalPoint q ∉ F.val ∧ a = z q}
end ToricMonoid
