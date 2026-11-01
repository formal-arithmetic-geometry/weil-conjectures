/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperTensorComparison

/-! # The normalized native pullback unit complex

Source: Stacks Tag 03EL; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-sf-native-pullback-unit)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper

/-- The pullback of the coefficient unit complex is the coefficient unit complex,
with its value on every adjunction-unit section specified by the coefficient adjunct.
Source: Stacks Tag 03EL; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-sf-native-pullback-unit).

Proof: compare the chosen ordinary adjunction with the canonical ringed module
pullback adjunction to their common direct image. Apply its left-adjoint uniqueness
isomorphism to the regular module and follow it by scalar multiplication, which
identifies pullback of the regular module with the regular module. Its adjunct is
the coefficient map, so evaluating the adjunction-unit equation gives the required
section formula. Apply the degree-zero single-complex functor. Naturality of the
ordinary adjunction unit moves the single-complex evaluation isomorphism across it.
The other degrees are zero, including on empty site objects and for zero rings. -/
theorem nativePullbackUnit (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (O : Operations l p R S) (A : At l X R) (C : At l Y S) :
    ∃ j : ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).obj
        (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S)) ≅
      ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R),
      unitSections l p R S O A C j := by
  let H := ContinuousRational.modulePull p O.coefficient
  let ρ := (proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _ O.coefficient
  let φ : (adicLisseForget Y).obj (ring l Y S) ⟶
      ((proEtaleBaseChange p).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((adicLisseForget X).obj (ring l X R)) :=
    ⟨Functor.whiskerRight ρ.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
    O.moduleAdjunction.isRightAdjoint
  let d := SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
    (F := proEtaleBaseChange p) (J := ProEt.topology Y) (K := ProEt.topology X) φ
  let q := O.moduleAdjunction.leftAdjointUniq d
  let e := q.app (SheafOfModules.unit _) ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  have he : O.moduleAdjunction.homEquiv _ _ e.hom =
      SheafOfModules.unitToPushforwardObjUnit φ := by
    change O.moduleAdjunction.homEquiv _ _ (q.hom.app _ ≫ _) = _
    rw [O.moduleAdjunction.homEquiv_naturality_right]
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ
  have hs (V : Y.ProEt) (s : (ring l Y S).obj.obj (op V)) :
      e.hom.val.app (op ((proEtaleBaseChange p).obj V))
        ((O.moduleAdjunction.unit.app (SheafOfModules.unit _)).val.app (op V) s) =
      ρ.hom.app (op V) s := by
    have hh := congrArg (fun z ↦ z.val.app (op V) s) he
    rw [Adjunction.homEquiv_unit] at hh
    exact hh
  let j := (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).app _ ≪≫
    (HomologicalComplex.single (modules l X R) (.up ℤ) 0).mapIso e
  refine ⟨j, ?_⟩
  intro V s
  let sy := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit ((adicLisseForget Y).obj (ring l Y S)))
  let sx := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit ((adicLisseForget X).obj (ring l X R)))
  have hj : j.hom.f 0 = H.map sy.hom ≫ e.hom ≫ sx.inv := by
    dsimp only [j, Iso.trans_hom, HomologicalComplex.comp_f, Functor.mapIso_hom]
    simp only [Iso.app_hom]
    rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  have hn := congrArg (fun z ↦ z.val.app (op V) (sy.inv.val.app (op V) s))
    (O.moduleAdjunction.unit.naturality sy.hom).symm
  have hy := congrArg (fun z ↦ z.val.app (op V) s) sy.inv_hom_id
  change sy.hom.val.app (op V) (sy.inv.val.app (op V) s) = s at hy
  change (H.map sy.hom).val.app (op ((proEtaleBaseChange p).obj V))
      ((O.moduleAdjunction.unit.app _).val.app (op V) (sy.inv.val.app (op V) s)) =
    (O.moduleAdjunction.unit.app _).val.app (op V)
      (sy.hom.val.app (op V) (sy.inv.val.app (op V) s)) at hn
  change (j.hom.f 0).val.app (op ((proEtaleBaseChange p).obj V))
    ((O.moduleAdjunction.unit.app _).val.app (op V) (sy.inv.val.app (op V) s)) =
      sx.inv.val.app (op ((proEtaleBaseChange p).obj V)) (ρ.hom.app (op V) s)
  rw [hj]
  change sx.inv.val.app _ (e.hom.val.app _ ((H.map sy.hom).val.app _ _)) = _
  rw [hn, hy]
  exact congrArg (fun z ↦ sx.inv.val.app (op ((proEtaleBaseChange p).obj V)) z) (hs V s)

end WeilConjectures.AdicQbarRealization.Proper
