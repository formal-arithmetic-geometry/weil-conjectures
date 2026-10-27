/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.UnitStructureCoefficientIso
public import Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionIso
public import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent

/-! # Local scalar conjugation in the normalized unit coordinates -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj coherentEtaleRestrictionIso
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

/-- The explicit localized unit identification, before taking cohomology.
Source: Stacks Project, Tags 0096, 0097 and 03DR.
(blueprint: new-unit-localized-scalar-conjugation). -/
def unitLocalizedCoefficientIso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] :
    (Etale.upperStar AddCommGrpCat.{u + 1} j).obj X.etaleAdditiveSheaf ≅
      liftedCoherentEtaleSheaf ((tensorPullback j).obj
        (SheafOfModules.unit X.ringCatSheaf)) :=
  (Etale.upperStar AddCommGrpCat.{u + 1} j).mapIso (unitStructureCoefficientIso X).symm ≪≫
    coherentEtaleRestrictionIso j (SheafOfModules.unit X.ringCatSheaf)

private theorem unitLocalizedCoefficientIso_inv_coordinate
    {X Y : Scheme.{u}} (j : Y ⟶ X) [AlgebraicGeometry.Etale j] (T : Y.Etale)
    (x : (liftedCoherentEtaleSheaf ((tensorPullback j).obj
      (SheafOfModules.unit X.ringCatSheaf))).obj.obj (op T)) :
    (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
      j inferInstance).hom.app X.etaleAdditiveSheaf).hom.app (op T))
        ((unitLocalizedCoefficientIso j).inv.hom.app (op T) x) =
      ULift.up (@id Γ(T.left, ⊤)
        ((tensorPullbackObjUnitToUnit (T.hom ≫ j)).app ⊤
          (((tensorSectionsComp T.hom j).hom.app
            (SheafOfModules.unit X.ringCatSheaf)).app ⊤ x.down))) := by
  let M := SheafOfModules.unit X.ringCatSheaf
  let ρ := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    j inferInstance).app (liftedCoherentEtaleSheaf M)
  let ρ' := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    j inferInstance).app X.etaleAdditiveSheaf
  let K := coherentEtaleRestrictionIso j M
  let p := (tensorSectionsComp T.hom j).app M
  let s := p.hom.app ⊤ x.down
  have hk : K.hom.hom.app (op T) (ρ.inv.hom.app (op T) (ULift.up s)) =
      ULift.up (p.inv.app ⊤ s) := by
    dsimp only [K, ρ, p]
    unfold coherentEtaleRestrictionIso
    convert (Classical.choose_spec (existsUnique_coherentEtaleRestrictionIso j M)).1 T s
      using 1 <;> rfl
  have hp : p.inv.app ⊤ s = x.down := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun a ↦ a.app ⊤) p.hom_inv_id) x.down
  rw [hp] at hk
  have hki : K.inv.hom.app (op T) x = ρ.inv.hom.app (op T) (ULift.up s) := by
    have h := congrArg (fun y ↦ K.inv.hom.app (op T) y) hk
    have hcancel := congrArg (fun a ↦ a.hom.app (op T)
      (ρ.inv.hom.app (op T) (ULift.up s))) K.hom_inv_id
    change K.inv.hom.app (op T) (K.hom.hom.app (op T)
      (ρ.inv.hom.app (op T) (ULift.up s))) = ρ.inv.hom.app (op T) (ULift.up s) at hcancel
    rw [hcancel] at h
    exact h.symm
  have hn := congrArg (fun a ↦ a.hom.app (op T))
    ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
      j inferInstance).hom.naturality (unitStructureCoefficientIso X).hom)
  have hn' := ConcreteCategory.congr_hom hn (K.inv.hom.app (op T) x)
  change ρ'.hom.hom.app (op T)
      (((Etale.upperStar AddCommGrpCat.{u + 1} j).map
        (unitStructureCoefficientIso X).hom).hom.app (op T)
          (K.inv.hom.app (op T) x)) =
    (unitStructureCoefficientIso X).hom.hom.app (op (Scheme.Etale.mk (T.hom ≫ j)))
      (ρ.hom.hom.app (op T) (K.inv.hom.app (op T) x)) at hn'
  rw [hki] at hn'
  have hcancel := congrArg (fun a ↦ a.hom.app (op T) (ULift.up s)) ρ.inv_hom_id
  change ρ.hom.hom.app (op T) (ρ.inv.hom.app (op T) (ULift.up s)) = ULift.up s at hcancel
  rw [hcancel] at hn'
  change ρ'.hom.hom.app (op T)
    (((Etale.upperStar AddCommGrpCat.{u + 1} j).map
      (unitStructureCoefficientIso X).hom).hom.app (op T)
        (K.inv.hom.app (op T) x)) = _
  rw [hki]
  convert hn' using 1
  rfl

/-- Multiplication in actual structural coordinates conjugates to coherent multiplication.
This concerns coefficient sheaves only; no realization, action on higher images or
cohomology comparison is assumed.
Source: Stacks Project, Tags 0096, 0097 and 03DR, equation (35.8.1).
(blueprint: new-unit-localized-scalar-conjugation).
Proof: let ρ identify inverse image along j with restriction of the small etale site.
At T→Y the inverse of the displayed coefficient isomorphism, followed by ρ, sends
a lifted tensor section s to the structural coordinate of c(T,j)(s), where c is
the unit-normalized tensor composition isomorphism. Indeed the specification of
coherentEtaleRestrictionIso gives the inverse c(T,j) on sections; cancel this
isomorphism, and use naturality of ρ with respect to unitStructureCoefficientIso.
The section formula of the latter then gives the claimed inverse coordinate map.
Both c(T,j) and the adjoint structure-module map on T are O_T-linear. Pullback of
smulHom r is smulHom of T.hom.appTop r, by tensorPullback_map_smulHom, and its
coherent coefficient map has exactly these section components. Consequently the
inverse coordinate map commutes with multiplication by T.hom.appTop r. Substitute
the hypothesis for μ in structural coordinates. Cancel the invertible component
of ρ and the coefficient isomorphism to obtain the conjugation identity at T.
Sectionwise equality gives equality of sheaf morphisms. For r=0, r=1, zero modules
and empty T the same linearity and cancellation prove the identity. -/
theorem unitLocalizedCoefficientIso_scalar {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (r : Γ(Y, ⊤))
    (μ : (Etale.upperStar AddCommGrpCat.{u + 1} j).obj X.etaleAdditiveSheaf ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} j).obj X.etaleAdditiveSheaf)
    (hμ : ∀ (T : Y.Etale)
      (x : ((Etale.upperStar AddCommGrpCat.{u + 1} j).obj
        X.etaleAdditiveSheaf).obj.obj (op T)),
      (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
        j inferInstance).hom.app X.etaleAdditiveSheaf).hom.app (op T))
          (μ.hom.app (op T) x) =
        ULift.up (@id Γ(T.left, ⊤) (T.hom.appTop r) *
          (@id Γ(T.left, ⊤) ((((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
            j inferInstance).hom.app X.etaleAdditiveSheaf).hom.app (op T)) x).down))) :
    μ ≫ (unitLocalizedCoefficientIso j).hom =
      (unitLocalizedCoefficientIso j).hom ≫ coherentEtaleMap _ _
        (((tensorPullback j).obj (SheafOfModules.unit X.ringCatSheaf)).smulHom r) := by
  let e := unitLocalizedCoefficientIso j
  let ρ := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    j inferInstance).app X.etaleAdditiveSheaf
  let M := (tensorPullback j).obj (SheafOfModules.unit X.ringCatSheaf)
  let m := coherentEtaleMap M M (M.smulHom r)
  have he : e.inv ≫ μ ≫ ρ.hom = m ≫ e.inv ≫ ρ.hom := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext T
    induction T using Opposite.rec
    rename_i T
    apply ConcreteCategory.hom_ext
    intro x
    change ρ.hom.hom.app (op T) (μ.hom.app (op T) (e.inv.hom.app (op T) x)) =
      ρ.hom.hom.app (op T) (e.inv.hom.app (op T) (m.hom.app (op T) x))
    dsimp only [ρ, e, Iso.app_hom]
    rw [hμ, unitLocalizedCoefficientIso_inv_coordinate,
      unitLocalizedCoefficientIso_inv_coordinate, coherentEtaleMap_smulHom_app]
    apply ULift.ext
    let p := ((tensorSectionsComp T.hom j).hom.app
      (SheafOfModules.unit X.ringCatSheaf)).app ⊤
    let d := (tensorPullbackObjUnitToUnit (T.hom ≫ j)).app ⊤
    change _ = d (p ((T.hom.appTop r) •
      (@id Γ((tensorPullback T.hom).obj M, ⊤) x.down)))
    rw [Hom.app_smul, Hom.app_smul]
    rfl
  have he' : e.inv ≫ μ = m ≫ e.inv := by
    apply (cancel_mono ρ.hom).mp
    simpa only [Category.assoc] using he
  change μ ≫ e.hom = e.hom ≫ m
  apply (cancel_epi e.inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    using congrArg (fun k ↦ k ≫ e.hom) he'


end
end AlgebraicGeometry.Scheme.Modules
