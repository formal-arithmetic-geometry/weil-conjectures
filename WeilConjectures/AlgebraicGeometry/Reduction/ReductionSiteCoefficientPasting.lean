/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects

/-! # The coefficient square in intrinsic realization coordinates

Source: Stacks Tags 0GL6, 099R and 00YV; blueprint Charts in
`sk-lem-sp-reduction-exceptional.proof.md`
(blueprint: lem-sp-reduction-site-coefficient-pasting).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale

/-- The actual coefficient square, followed by a map to a bounded-below ordinary
object. This mixed-endpoint form does not assume that scalar extension preserves D+.
Source: Stacks 0GL6, 099R, 00YV; Charts, coefficient/site square
(blueprint: lem-sp-reduction-site-coefficient-pasting).

Proof: express the site functor as comparison inverse image followed by the specified
intrinsic realization. The realization scalar comparison is the inverse mate of the
section-normalized restriction square. The realization compact-support comparison
cancels the open realization equivalence and uses the section-normalized derived
proper direct-image comparison. These are the same comparisons used in transporting
the recorded reductionDirectImageComparison to fixed coefficients. Uniqueness of
left-adjoint comparisons identifies the scalar boundaries; uniqueness of the proper
right-adjoint comparison identifies the direct-image boundaries. The open boundaries
agree termwise with extension by zero. For the proper factor, transpose the two
endpoint maps under the geometric
adjunctions. The bounded-below site-comparison counit equations and the scalar/pullback
cube identify these transposes, by mate pasting and the triangle identities. The
restriction square agrees sectionwise, so its inverse scalar mates give that cube.
The exact open-extension comparison agrees termwise. Compose these proper and open
squares and use naturality to move the given map a through the B-support comparison.
This gives the displayed mixed-endpoint identity. Only M and N use the bounded-below
site comparison: no comparison or lower
bound for the intermediate scalar extension is used. -/
theorem reductionSiteCoefficientPasting
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (M : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X)
    (hM : DerivedCategory.TStructure.t.plus M)
    (N : Etale.DerivedCategoryModule (ULift.{u + 1, u} B) X)
    (hN : DerivedCategory.TStructure.t.plus N)
    (a : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj M ⟶ N) :
    let C : Compactification (j ≫ p) :=
      ⟨Z, p, j, rfl, inferInstance, inferInstance⟩
    (scalarExtensionFunctor φ Y).map
        ((reductionSiteCompactSupportIso A j p).hom.app ⟨M, hM⟩) ≫
      (reductionSiteScalarIso φ Y).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) C).obj M) ≫
      (reductionSite B Y).map
        (Etale.ExceptionalCoefficients.compactSupportMap
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) C M ≫
          (Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) C).map a) =
    (reductionDirectImageComparison φ j p).app ((reductionSite A X).obj M) ≫
      (reductionCompactSupport B j p).map
        ((reductionSiteScalarIso φ X).hom.app M ≫ (reductionSite B X).map a) ≫
      (reductionSiteCompactSupportIso B j p).hom.app ⟨N, hN⟩ := by
  sorry

end AlgebraicGeometry.ProEtale
