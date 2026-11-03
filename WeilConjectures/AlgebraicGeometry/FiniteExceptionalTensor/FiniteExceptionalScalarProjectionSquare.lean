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

/-! # The ordinary finite scalar projection square

Source: latest blueprint, reduction compatibilities proof (3), Tensor map.
(blueprint: lem-pur-finite-exceptional-scalar-projection-square).
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

/-- The ordered forward scalar projection square and its coefficient-unit equation.
This statement involves no exceptional right adjoint, counit, or tensor mate.
Source: latest blueprint, reduction compatibilities proof (3), Tensor map: projection
formula compatibility with scalar extension; Stacks 07A4 and 0E48.
(blueprint: lem-pur-finite-exceptional-scalar-projection-square).

Proof: On flat-term K-flat representatives, the scalar tensorator is balanced tensor
reassociation and its unit is scalar-unit multiplication, by the exact-restriction
adjunction and the canonical restriction tensorator's localization normalization.
The same adjunction computes scalarPull from the exact restriction/pullback square.
Thus the scalar tensor, scalar unit, and pullback maps are the normalized monoidal
maps under the finite-coefficient encoding. The compact-support restriction square
is the proper direct-image square followed by the open inverse mate. Transposing it
under scalar adjunctions gives compactComparison; equivalently it is the proper
counit scalar map followed by the open tensor comparison. Apply normalized condensed
compact-support scalar projection coherence and transport along the tensor-compatible
finite-discrete ordinary encoding. Naturality of the Koszul braiding puts K first
and yields the displayed forward square. No projection or support comparison is
inverted. The normalized monoidal right-unit axiom yields the second equation.
The representative comparison extends to arbitrary unbounded objects by resolving
each input, using naturality and canceling the resulting localization isomorphisms.
This uses no scalar flatness and covers identity maps, zero rings and empty sites. -/
theorem finite_exceptional_scalar_projection_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y) :
    (∀ (K : D A Y) (M : D A X),
      (scalar φ Y).map (projection A c K M) ≫
          compactComparison φ c aX aY ((pull A f).obj K ⊗ M) ≫
          (support B c).map (sigma φ f aX aY K M) =
        scalarTensor φ Y aY K ((support A c).obj M) ≫
          (𝟙 ((scalar φ Y).obj K) ⊗ₘ compactComparison φ c aX aY M) ≫
          projection B c ((scalar φ Y).obj K) ((scalar φ X).obj M)) ∧
    (∀ K : D A Y,
      scalarTensor φ Y aY K (𝟙_ (D A Y)) ≫
          (𝟙 ((scalar φ Y).obj K) ⊗ₘ scalarUnit φ Y aY) ≫
          (ρ_ ((scalar φ Y).obj K)).hom =
        (scalar φ Y).map (ρ_ K).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteExceptionalTensor
