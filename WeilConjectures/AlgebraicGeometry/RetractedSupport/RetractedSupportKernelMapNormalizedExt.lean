/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
public import WeilConjectures.AlgebraicGeometry.SupportedHomAdjunctionClass
import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportRepresentability
import WeilConjectures.CategoryTheory.RestrictedCoyonedaRigidity

/-! Uniqueness of the normalized support kernel map.
Source: the represented-functor rigidity step in
`lem-pur-gysin-structure.proof.md`
(blueprint: lem-pur-retracted-support-kernel-map-normalized-ext).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.ProEtale.RetractedSupport

/-- Two natural support kernel maps satisfying the same forget-support square agree.
Source: the represented-functor and epimorphic coefficient-quotient argument in
`lem-pur-gysin-structure.proof.md`.

The proof represents the supported and ambient degree-two functors by the closed and
ambient constant objects, lifts the ratio through the fully faithful single-object
functor, and cancels the epimorphic coefficient quotient. Restricted Yoneda then
forces equality on every bounded-below input.
(blueprint: lem-pur-retracted-support-kernel-map-normalized-ext).

Proof:
1. The closed injective-kernel model and the site comparison identify the source
   functor with the supported functor. The invertible first comparison identifies
   its source with closedTerm, and the counit equation supplies its normalization.
2. Compose the inverse of this isomorphism with each input map. Both endomorphisms
   of the supported functor have the identity's forget-support composite, by hκ and hκ'.
3. Represent support and ambient cohomology by the closed and ambient etale constant
   objects. At the shifted single closed object, lift the endomorphism through the
   fully faithful single functor. The forget-support equation says its precomposition
   with the coefficient quotient is that quotient. The quotient is epi in sheaves,
   so cancellation makes the lifted endomorphism the identity.
4. Restricted Yoneda propagates this equality to all bounded-below shifted test objects.
   Faithfulness of the underlying-set functor and cancellation of the source
   isomorphism give equality of the original natural transformations. -/
theorem kernelCounitMap_normalized_ext
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) [IsLocallyNoetherian (Line T)]
    (first : closedTerm P (zeroSection T) ⟶ middleTerm P (lineProjection T))
    (hfirstIso : ∀ B : DerivedCategory.Plus (EtSheaves P (Line T)),
      IsIso (firstComparison P (lineProjection T) (zeroSection T)
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) T) B))
    (hfirst : ∀ B : DerivedCategory.Plus (EtSheaves P (Line T)),
      firstComparison P (lineProjection T) (zeroSection T)
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) T) B ≫ first.app B =
        (nu P T).map ((Etale.lowerStar (Modules P) (lineProjection T)).rightDerivedFunctor.map
          ((Adjunction.ofIsLeftAdjoint
            (Etale.lowerStar (Modules P) (zeroSection T)).rightDerivedFunctor).counit.app B.obj)) ≫
          imageComparison P (lineProjection T) B)
    (κ κ' : closedTerm P (zeroSection T) ⋙ hyper P T 2 ⟶
        nuPlus P (Line T) ⋙ Sheaf.supportHypercohomologyFunctor
          (Scheme.ProEt.topology (Line T)) (Modules P)
          (supportRestrictionArrow (zeroSection T)) 2)
    (hκ : ∀ B : DerivedCategory.Plus (EtSheaves P (Line T)),
        (hyper P T 2).map (first.app B) ≫
            (middleGlobalIso P (lineProjection T) 2).hom.app B =
          κ.app B ≫ (Sheaf.supportHypercohomologyInclusion
            (Scheme.ProEt.topology (Line T)) (Modules P)
            (supportRestrictionArrow (zeroSection T)) 2).app ((nuPlus P (Line T)).obj B))
    (hκ' : ∀ B : DerivedCategory.Plus (EtSheaves P (Line T)),
        (hyper P T 2).map (first.app B) ≫
            (middleGlobalIso P (lineProjection T) 2).hom.app B =
          κ'.app B ≫ (Sheaf.supportHypercohomologyInclusion
            (Scheme.ProEt.topology (Line T)) (Modules P)
            (supportRestrictionArrow (zeroSection T)) 2).app ((nuPlus P (Line T)).obj B)) :
    κ = κ' := by
  sorry

end AlgebraicGeometry.ProEtale.RetractedSupport
