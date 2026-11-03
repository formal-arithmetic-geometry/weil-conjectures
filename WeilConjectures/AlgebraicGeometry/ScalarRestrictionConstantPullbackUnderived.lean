/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarRestrictionTensor

/-! The ordinary mate square underlying scalar restriction and constant pullback. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)

private theorem ordinary_mate
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)).natTrans =
        (lowerStarRestrictScalarsIso φ f).hom := by
  apply (mateEquiv (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ)
    (Sheaf.restrictCoextendScalarsAdj W.smallEtaleTopology φ)).injective
  change (mateEquiv (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ)
    (Sheaf.restrictCoextendScalarsAdj W.smallEtaleTopology φ)
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom))).natTrans = _
  rw [iterated_mateEquiv_conjugateEquiv]
  simp only [upperStarRestrictScalarsIsoSheaf, Adjunction.leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, TwoSquare.mk]
  erw [Equiv.apply_symm_apply]
  ext M ⟨U⟩ x
  exact congrArg (fun t ↦ t.hom x)
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).right_triangle_components
      (M.obj.obj (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)))).symm

/-- Ordinary scalar restriction/constant pullback coherence.

Source: Stacks 0F1E and 0FPI; the ordinary mate square in the proof of
`new-lem-pur-scalar-restriction-constant-pullback`.
The proof compares the two maps by the upper-star adjunction hom equivalence,
uses the unit mate of `upperStarRestrictScalarsIsoSheaf`, and applies the
constant-sheaf counit compatibility with sheaf composition.
Proof (in words): both sides are maps out of the constant sheaf `c_Z (res X)`, so they are
equal once their transposes `res X ⟶ Γ(Z, res (p^* c_T X))` under `constantSheaf ⊣ Γ`
agree. `constantSheafCompUpperStarNatIso` is the left-adjoint uniqueness isomorphism for
`c_T ⋙ p^* ⊣ p_* ⋙ Γ_T = Γ_Z`, and `upperStarRestrictScalarsIsoSheaf` has mate the identity
`lowerStarRestrictScalarsIso` (the private `ordinary_mate`); so both transposes reduce to
`res` of the unit `X ⟶ Γ(T, c_T X) ⟶ Γ(Z, p^* c_T X)`, the sheaf-composition comparison
`constantSheafCompSheafComposeIso` being compatible with these units.
(blueprint: new-lem-pur-scalar-restriction-constant-pullback-underived).
-/
theorem scalarRestrictionConstantPullback_underived
    {Z T : Scheme.{u}} (p : Z ⟶ T)
    (X : ModuleCat.{u + 1} B) :
    (constantSheafCompSheafComposeIso Z.smallEtaleTopology
      (ModuleCat.restrictScalars φ)).inv.app X ≫
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).map
        ((constantSheafCompUpperStarNatIso (ModuleCat.{u + 1} B) p).inv.app X) =
    (constantSheafCompUpperStarNatIso (ModuleCat.{u + 1} A) p).inv.app
        ((ModuleCat.restrictScalars φ).obj X) ≫
      (upperStar (ModuleCat.{u + 1} A) p).map
        ((constantSheafCompSheafComposeIso T.smallEtaleTopology
          (ModuleCat.restrictScalars φ)).inv.app X) ≫
      (upperStarRestrictScalarsIsoSheaf φ p).hom.app
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)).obj X) := by
  sorry

end AlgebraicGeometry.Etale
