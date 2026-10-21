/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# Ordinary scalar extension and closed direct image

Source: Stacks Project, Tags 09AA, 09AH, 03EK and 03EL
(blueprint: lem-weil-pbc-closed-immersion-scalar-change).
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The ordinary closed projection formula, expressed with actual sheafified
changes of rings and transported source coefficients.
Source: Stacks Project, Tags 09AA, 09AH, 03EK and 03EL
(blueprint: lem-weil-pbc-closed-immersion-scalar-change).
Proof: apply the underived closed projection formula to R, its module B, and the
restriction of M along cR. The projection is invertible because its source has
zero restriction to the complementary open; localization identifies it with its
closed direct image. Its closed restriction is the tensor of M with inverse
image of B, by inverse-image tensor comparison and the closed counit. Identify
ordinary change of rings with the sheafification of B tensor_R N, using tensor
symmetry. On the closed site, transport the same tensor through cR and cB. The
coefficient-square hypothesis identifies its balancing relation with the one
for b. The resulting maps are linear over B: on pure tensors the projection
sends m tensor s to m tensor bar(s), where bar is the ring-adjunction unit, so
multiplication on the B factor is preserved. Pure tensors locally generate the
sheafifications; hence the linear maps extend uniquely and their inverse
identities can be checked there. This supplies an isomorphism of B-modules,
without flatness, finite presentation or constructibility hypotheses. -/
theorem closedImmersion_scalar_change {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (R B : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S T : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (a : R ⟶ B) (b : S ⟶ T)
    (cR : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R ≅ S)
    (cB : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj B ≅ T)
    (h : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).map a ≫ cB.hom =
      cR.hom ≫ b)
    (M : SheafOfModules.{u + 1} (proEtaleModuleCoefficients S)) :
    Nonempty (SheafOfModules.changeOfRings.{u, u + 1, u + 1} a
        ((SheafOfModules.restrictScalars
          ((sheafCompose (ProEt.topology Z)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map cR.hom) ⋙
              proEtaleRingedDirectImage i R).obj M) ≅
      (SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology Z)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map cB.hom) ⋙
            proEtaleRingedDirectImage i B).obj
              (SheafOfModules.changeOfRings.{u, u + 1, u + 1} b M)) := by sorry

end AlgebraicGeometry.Scheme
