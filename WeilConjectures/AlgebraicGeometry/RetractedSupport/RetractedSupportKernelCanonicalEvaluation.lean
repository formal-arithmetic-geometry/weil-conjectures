/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
public import WeilConjectures.AlgebraicGeometry.SupportedHomAdjunctionClass
public import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportKernelCounitMapExistence

/-! Evaluation of the chosen canonical support kernel map.
Source: the ordinary closed-adjunction calculation in
`lem-pur-gysin-structure.proof.md`
(blueprint: lem-pur-retracted-support-kernel-canonical-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.ProEtale.RetractedSupport

/-- The chosen map supplied by the kernel construction has the closed-counit value.
Source: the injective-kernel evaluation and the derived supported adjunction in
`lem-pur-gysin-structure.proof.md`.

The chosen map is obtained from `kernelCounitMap_exists`; its value is computed on an
injective closed-adjoint representative, transported through the exceptional and image
comparisons, and read through the supported derived adjunction. -/
theorem kernelCounitMap_canonical_evaluation
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
    (κ₀ : closedTerm P (zeroSection T) ⋙ hyper P T 2 ⟶
        nuPlus P (Line T) ⋙ Sheaf.supportHypercohomologyFunctor
          (Scheme.ProEt.topology (Line T)) (Modules P)
          (supportRestrictionArrow (zeroSection T)) 2)
    (hκ₀ : ∀ B : DerivedCategory.Plus (EtSheaves P (Line T)),
        (hyper P T 2).map (first.app B) ≫
            (middleGlobalIso P (lineProjection T) 2).hom.app B =
          κ₀.app B ≫ (Sheaf.supportHypercohomologyInclusion
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
      κ₀.app (P.gysinEtaleInput h T) (P.gysinGlobalClass T 2 m) =
        supportedHomPairAdjunctionClass P (zeroSection T) (P.gysinInput h T) 2
          (((lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor 0).inv.app
          (P.constant T) ≫
        (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map m ≫
        (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map eK.inv ≫
        d.inv ≫ (nu P (Line T)).map (P.boundaryEtaleCounit h T) ≫
        ((nu P (Line T)).commShiftIso (2 : ℤ)).hom.app (P.gysinEtaleInput h T).obj) := by
  sorry

end AlgebraicGeometry.ProEtale.RetractedSupport
