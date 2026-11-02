/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
public import WeilConjectures.AlgebraicGeometry.SupportedHomAdjunctionClass

/-! The canonical support kernel map and its forget-support square.
Source: the injective-kernel and derived-unit construction in
`lem-pur-gysin-structure.proof.md` (blueprint: lem-pur-retracted-support-kernel-counit-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.ProEtale.RetractedSupport

/-- The ordinary closed-adjoint kernel construction produces the natural support map.
Source: `lem-pur-supported-hom.proof.md` and the second assertion of
`lem-pur-gysin-structure.proof.md`
(blueprint: lem-pur-retracted-support-kernel-counit-map-existence).

Proof:
1. For a bounded-below injective etale complex I, the ordinary closed right adjoint
   preserves injectives since closed direct image is exact. Its sections are exactly
   the kernel of I(X) to I(U); the kernel inclusion is the closed counit. These are
   natural identifications of complexes, including their differentials.
2. Pass to the derived functors using their actual units. Compare the chosen right
   adjoint with the closed-support model by right-adjoint uniqueness. Compose with
   the global etale/pro-etale comparison. The retraction collapse and the invertible
   specified first comparison identify this source with global sections of closedTerm.
3. Apply the unit-normalized comparison of support kernels between the two sites.
   Naturality of the restriction square identifies its composite with forgetting
   support with the usual global comparison. Apply degree-two homology.
4. The hypothesis hfirst identifies the counit arrow after that source comparison
   with the specified first arrow. Naturality of the derived direct-image compositor
   identifies the global comparison with middleGlobalIso, giving the square. This
   construction applies also to zero inputs, empty T, and the zero coefficient ring. -/
theorem kernelCounitMap_exists
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
      ∀ B : DerivedCategory.Plus (EtSheaves P (Line T)),
        (hyper P T 2).map (first.app B) ≫
            (middleGlobalIso P (lineProjection T) 2).hom.app B =
          κ.app B ≫ (Sheaf.supportHypercohomologyInclusion
            (Scheme.ProEt.topology (Line T)) (Modules P)
            (supportRestrictionArrow (zeroSection T)) 2).app ((nuPlus P (Line T)).obj B) := by
  sorry

end AlgebraicGeometry.ProEtale.RetractedSupport
