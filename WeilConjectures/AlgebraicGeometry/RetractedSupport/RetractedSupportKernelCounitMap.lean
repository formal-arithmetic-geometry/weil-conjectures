/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
public import WeilConjectures.AlgebraicGeometry.SupportedHomAdjunctionClass
import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportKernelCounitMapExistence
import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportKernelCounitMapEvaluation

/-! # Canonical support map and the ordinary closed counit

The support map is natural on every ordinary etale input. Its counit formula is
stated only for the affine-line twist needed by the orientation argument.
(blueprint: lem-pur-retracted-support-kernel-counit-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.ProEtale.RetractedSupport

/-- The injective-kernel construction gives a natural support map normalized by the
closed counit. This assertion constructs the map and its normalizations, without
identifying it with any previously supplied supportIso.
Source: the injective-kernel proof in `lem-pur-supported-hom.proof.md`, the second
assertion of `lem-pur-gysin-structure.proof.md`, and finite etale-origin counit transport
in `cor-pur-affine-space-zero-section-purity.proof.md`
(blueprint: lem-pur-retracted-support-kernel-counit-map).

Proof:
1. On an ordinary etale injective representative, the closed right adjoint preserves
   injectives because its left adjoint is exact. Global sections of its closed value
   are the kernel of restriction to the complementary open. The ordinary counit is
   the inclusion of this kernel. This is a natural isomorphism of complexes.
2. Derive that comparison, keeping the actual derived units. The first comparison
   and the retraction collapse identify its source with global cohomology of closedTerm.
   The first-square hypothesis ensures that the resulting forget-support arrow is
   precisely H² RΓ(first) followed by middleGlobalIso.
3. Transport the support kernel through the finite etale/pro-etale comparison. The
   constant-unit and restriction equations identify its kernel inclusion with the
   recorded supported-section inclusion. The comparison on bounded-below inputs
   commutes with its derived unit; hence it defines the displayed natural map κ.
4. Evaluate κ on gysinGlobalClass(m). The ordinary closed adjunction sends this class
   to the closed direct image of m followed by the counit. Transporting the exceptional
   value by eK.inv and the direct image by d.inv gives the displayed six factors.
   The exact single-object comparison contributes its inverse at the source, and
   the commShiftIso of nu contributes the final factor. Apply the supported derived
   adjunction to read the same element as supportedHomPairAdjunctionClass.
5. Naturality of all derived-unit, direct-image, single and shift comparisons removes
   the representatives. The equations heK and hd allow any specified isomorphisms with
   the prescribed homs; their inverses are then uniquely determined. No arbitrary
   supportIso or orientation chart is used. The zero morphism and empty support
   satisfy the same construction. -/
theorem kernelCounitClassNaturalMap
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
          imageComparison P (lineProjection T) B) :
    ∃ κ : closedTerm P (zeroSection T) ⋙ hyper P T 2 ⟶
        nuPlus P (Line T) ⋙ Sheaf.supportHypercohomologyFunctor
          (Scheme.ProEt.topology (Line T)) (Modules P)
          (supportRestrictionArrow (zeroSection T)) 2,
      (∀ B : DerivedCategory.Plus (EtSheaves P (Line T)),
        (hyper P T 2).map (first.app B) ≫
            (middleGlobalIso P (lineProjection T) 2).hom.app B =
          κ.app B ≫ (Sheaf.supportHypercohomologyInclusion
            (Scheme.ProEt.topology (Line T)) (Modules P)
            (supportRestrictionArrow (zeroSection T)) 2).app ((nuPlus P (Line T)).obj B)) ∧
      ∀
    (hb : DerivedCategory.TStructure.t.plus (P.boundaryEtaleValue h T))
    (eK : (nu P T).obj (P.boundaryEtaleValue h T) ≅ P.gysinValue h T)
    (d : (nu P (Line T)).obj
        ((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.obj
          (P.boundaryEtaleValue h T)) ≅
      (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.obj
        ((nu P T).obj (P.boundaryEtaleValue h T)))
    (heK : eK.hom = P.boundaryExceptionalComparison h T)
    (hd : d.hom = P.boundaryImageComparison T ⟨P.boundaryEtaleValue h T, hb⟩)
    (m : P.derivedSheaf h T false ⟶ P.gysinValue h T),
        κ.app (P.gysinEtaleInput h T) (P.gysinGlobalClass T 2 m) =
          supportedHomPairAdjunctionClass P (zeroSection T) (P.gysinInput h T) 2
          (((lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor 0).inv.app
          (P.constant T) ≫
        (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map m ≫
        (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map eK.inv ≫
        d.inv ≫ (nu P (Line T)).map (P.boundaryEtaleCounit h T) ≫
        ((nu P (Line T)).commShiftIso (2 : ℤ)).hom.app (P.gysinEtaleInput h T).obj) := by
  obtain ⟨κ, hκ⟩ := kernelCounitMap_exists P h T first hfirstIso hfirst
  refine ⟨κ, hκ, ?_⟩
  intro hb eK d heK hd m
  simpa only using kernelCounitMap_evaluation P h T first hfirstIso hfirst κ hκ
    hb eK d heK hd m

end AlgebraicGeometry.ProEtale.RetractedSupport
