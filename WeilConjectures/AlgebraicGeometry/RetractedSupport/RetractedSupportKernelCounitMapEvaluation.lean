/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
public import WeilConjectures.AlgebraicGeometry.SupportedHomAdjunctionClass
public import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportKernelCanonicalEvaluation
public import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportKernelMapNormalizedExt
public import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportKernelCounitMapExistence
public import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportRepresentability
public import WeilConjectures.CategoryTheory.RestrictedCoyonedaRigidity

/-! Evaluation of the canonical support kernel map.
Source: the closed-adjunction counit transport in
`lem-pur-gysin-structure.proof.md` (blueprint: lem-pur-retracted-support-kernel-counit-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.ProEtale.RetractedSupport

/-- A map normalized by the forget-support square evaluates by the closed counit.
Source: `lem-pur-supported-hom.proof.md` and the second assertion of
`lem-pur-gysin-structure.proof.md`
(blueprint: lem-pur-retracted-support-kernel-counit-map-evaluation).

Proof:
1. First use the ordinary injective-kernel model for the closed adjoint, with the
   canonical site-comparison unit. The comparison is an isomorphism on bounded-below
   inputs: this follows by comparing the support and global/open localization
   triangles, or directly from the closed injective kernel model and full faithfulness
   of the site comparison. Denote the resulting degree-two natural isomorphism by sigma.
2. The ratio sigma.inv followed by kappa is an endomorphism of the supported functor
   fixing its map to ambient cohomology, by the two forget-support squares. Represent
   the supported functor by Hom from the closed constant coefficient object and ambient
   cohomology by Hom from the ambient constant. At the shifted single representing
   object, full faithfulness of the single functor lifts the endomorphism to sheaves.
   Forgetting support is precomposition by the coefficient quotient, which is epic in
   sheaves. Cancellation makes that lifted endomorphism the identity. Restricted Yoneda
   then makes the ratio the identity on all inputs. This uses naturality in all inputs;
   it does not cancel the degree-two forget-support map at a single input.
3. Evaluate the canonical kernel map on gysinGlobalClass(m). Under the ordinary closed
   adjunction this is closed direct image of m followed by its counit. The inverse
   single-object comparison supplies the first factor of the displayed morphism.
4. Replace the exceptional value via eK.inv and the direct-image comparison via d.inv.
   Substitute heK and hd. The ordinary shifted counit is boundaryEtaleCounit, and the
   comparison with the shifted target contributes nu.commShiftIso. Applying the actual
   supported derived adjunction reads the element as supportedHomPairAdjunctionClass.
   Naturality removes the chosen representatives. Zero m and empty T satisfy the same
   formulas; no pointwise injectivity of the forget-support map is assumed. -/
theorem kernelCounitMap_evaluation
    (P : WeilConjectures.PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
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
    (κ : closedTerm P (zeroSection T) ⋙ hyper P T 2 ⟶
        nuPlus P (Line T) ⋙ Sheaf.supportHypercohomologyFunctor
          (Scheme.ProEt.topology (Line T)) (Modules P)
          (supportRestrictionArrow (zeroSection T)) 2)
    (hκ : ∀ B : DerivedCategory.Plus (EtSheaves P (Line T)),
        (hyper P T 2).map (first.app B) ≫
            (middleGlobalIso P (lineProjection T) 2).hom.app B =
          κ.app B ≫ (Sheaf.supportHypercohomologyInclusion
            (Scheme.ProEt.topology (Line T)) (Modules P)
            (supportRestrictionArrow (zeroSection T)) 2).app ((nuPlus P (Line T)).obj B))
    (hb : DerivedCategory.TStructure.t.plus (P.boundaryEtaleValue h T))
    (eK : (nu P T).obj (P.boundaryEtaleValue h T) ≅ P.gysinValue h T)
    (d : (nu P (Line T)).obj
        ((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.obj
          (P.boundaryEtaleValue h T)) ≅
      (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.obj
        ((nu P T).obj (P.boundaryEtaleValue h T)))
    (heK : eK.hom = P.boundaryExceptionalComparison h T)
    (hd : d.hom = P.boundaryImageComparison T ⟨P.boundaryEtaleValue h T, hb⟩)
    (m : P.derivedSheaf h T false ⟶ P.gysinValue h T) :
        κ.app (P.gysinEtaleInput h T) (P.gysinGlobalClass T 2 m) =
          supportedHomPairAdjunctionClass P (zeroSection T) (P.gysinInput h T) 2
          (((lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor 0).inv.app
          (P.constant T) ≫
        (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map m ≫
        (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map eK.inv ≫
        d.inv ≫ (nu P (Line T)).map (P.boundaryEtaleCounit h T) ≫
        ((nu P (Line T)).commShiftIso (2 : ℤ)).hom.app (P.gysinEtaleInput h T).obj)  := by
  obtain ⟨κ₀, hκ₀⟩ := kernelCounitMap_exists P h T first hfirstIso hfirst
  have hext := kernelCounitMap_normalized_ext P h T first hfirstIso hfirst κ κ₀ hκ hκ₀
  have happ := congrArg (fun z =>
    z.app (P.gysinEtaleInput h T) (P.gysinGlobalClass T 2 m)) hext
  change κ.app (P.gysinEtaleInput h T) (P.gysinGlobalClass T 2 m) =
    κ₀.app (P.gysinEtaleInput h T) (P.gysinGlobalClass T 2 m) at happ
  rw [happ]
  exact kernelCounitMap_canonical_evaluation P h T first hfirstIso hfirst κ₀ hκ₀ hb eK d heK hd m

end AlgebraicGeometry.ProEtale.RetractedSupport
