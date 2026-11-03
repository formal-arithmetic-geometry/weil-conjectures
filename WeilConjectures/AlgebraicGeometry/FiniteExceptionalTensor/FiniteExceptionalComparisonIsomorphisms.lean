/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.DerivedScalarRestrictionTensor
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Invertibility of the finite scalar comparisons

Source: latest blueprint, reduction compatibilities proof (3), Tensor map, comparison isomorphisms.
(blueprint: lem-pur-finite-exceptional-comparison-isomorphisms).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

attribute [local instance 2000] CommRing.toRing isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

namespace AlgebraicGeometry.ProEtale.FiniteExceptionalTensor

/-- The ordinary finite-ring projection, support-scalar, tensor-pullback and unit
maps are isomorphisms on their stated domains. This has no exceptional right adjoint
and asserts no equality of exceptional tensor maps.
Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), Tensor map, comparison domains.
(blueprint: lem-pur-finite-exceptional-comparison-isomorphisms).

Proof: The finite-discrete equivalence identifies ordinary intrinsic constructibility
and finite Tor amplitude with their fixed-scalar counterparts. Apply the finite-ring
compact-support projection theorem over A and B and compose its two Koszul braidings.
For compactComparison, compute on a proper/open compactification. The restriction
mate on the proper factor is the scalar extension of its counit, by transposing
under the scalar and proper adjunctions; the open factor is the normalized open
scalar tensor map. Therefore it is the specified compact-support scalar comparison,
which is invertible on Dctf by independent constructibility and scalar direct-image
comparison. This is before purity or biduality. On common flat-term K-flat resolutions,
scalarTensor is balanced tensor reassociation and scalarPull is geometric scalar
balancing. The defining restriction units send x tensor y to (1 tensor x) tensor
(1 tensor y), so their transpose is the usual invertible tensor comparison. Scalar
unit multiplication identifies scalar extension of the degree-zero A unit with the
B unit. Uniqueness of left adjoints transports each computation to the supplied aX
aY, including their units. Localization of the resolutions proves the assertions for
all objects, without assuming flatness of B over A. The zero ring, empty scheme,
identity ring map and the nonflat map Z/ell^2 to Z/ell are included. -/
theorem finite_exceptional_comparison_isomorphisms
    (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) (_hell : ell.Prime) (_hellp : ell ≠ D₀.p)
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, 1 ≤ n ∧ ∀ r : A, (ell ^ n) • r = 0)
    (_hB : ∃ n : ℕ, 1 ≤ n ∧ ∀ r : B, (ell ^ n) • r = 0)
    (φ : A →+* B) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D₀.k))] [Y.Over (Spec (.of D₀.k))]
    [IsSeparated (X ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D₀.k))]
    [QuasiCompact (X ↘ Spec (.of D₀.k))]
    [IsSeparated (Y ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D₀.k))]
    [QuasiCompact (Y ↘ Spec (.of D₀.k))]
    (f : X ⟶ Y)
    (c : Compactification f) [c.Z.Over (Spec (.of D₀.k))]
    [IsSeparated (c.Z ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of D₀.k))]
    [QuasiCompact (c.Z ↘ Spec (.of D₀.k))]
    [c.i.IsOver (Spec (.of D₀.k))] [c.g.IsOver (Spec (.of D₀.k))]
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y)
    : (∀ (K : D A Y) (M : D A X), ctf A Y K → ctf A X M →
        IsIso (projection A c K M)) ∧
      (∀ (K : D B Y) (M : D B X), ctf B Y K → ctf B X M →
        IsIso (projection B c K M)) ∧
      (∀ M : D A X, ctf A X M → IsIso (compactComparison φ c aX aY M)) ∧
      (∀ (K : D A Y) (M : D A X), IsIso (sigma φ f aX aY K M)) ∧
      IsIso (scalarUnit φ Y aY) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteExceptionalTensor
