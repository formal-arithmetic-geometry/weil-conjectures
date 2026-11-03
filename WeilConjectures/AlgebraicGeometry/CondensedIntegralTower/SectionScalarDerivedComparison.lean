/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CondensedCoefficientTowers
import all WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Opposites

/-! # Normalized scalar extension in section coordinates

Source: sk-prop-sp-integral-adjunction, finite scalar normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower

private theorem scalarComparisonFromRestriction
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {U : B ⥤ A} {F : D ⥤ E} {V : E ⥤ D}
    {G : A ⥤ D} {H : B ⥤ E} [G.IsEquivalence] [H.IsEquivalence]
    (adj : L ⊣ U) (adj' : F ⊣ V) (β : U ⋙ G ≅ H ⋙ V) :
    ∃! e : L ⋙ H ≅ G ⋙ F,
      ∀ X, G.map (adj.unit.app X) ≫ β.hom.app (L.obj X) ≫
        V.map (e.hom.app X) = adj'.unit.app (G.obj X) := by
  let α := ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ β.hom)).natTrans
  have hα : IsIso α := by
    let βop : TwoSquare H.op U.op V.op G.op :=
      TwoSquare.mk _ _ _ _ (NatTrans.op β.hom)
    have hi := isIso_mateEquiv_of_isEquivalence adj.op adj'.op βop
    have he : NatTrans.op α = (mateEquiv adj.op adj'.op βop).natTrans := by
      ext X
      simp [α, βop, mateEquiv]
    have : IsIso (NatTrans.op α) := by rw [he]; exact hi
    have (X : A) : IsIso (α.app X) := by
      have : IsIso ((α.app X).op) :=
        NatIso.isIso_app_of_isIso (NatTrans.op α) (Opposite.op X)
      exact isIso_of_op (α.app X)
    exact NatIso.isIso_of_isIso_app α
  refine ⟨(asIso α).symm, ?_, ?_⟩
  · intro X
    have h := unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ β.hom) X
    change G.map (adj.unit.app X) ≫ β.hom.app (L.obj X) =
      adj'.unit.app (G.obj X) ≫ V.map (α.app X) at h
    rw [← Category.assoc, h, Category.assoc, ← V.map_comp]
    simp
  · intro e he
    have hm : mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.inv) =
        TwoSquare.mk _ _ _ _ β.hom := by
      apply mateEquiv_eq_of_unit
      intro X
      have h := congrArg (fun t ↦ t ≫ V.map (e.inv.app X)) (he X)
      simp only [Category.assoc, ← V.map_comp, Iso.hom_inv_id_app] at h
      dsimp only [Functor.comp_obj] at h
      rw [V.map_id, Category.comp_id] at h
      exact h
    have hx := (mateEquiv adj adj').symm_apply_apply (TwoSquare.mk _ _ _ _ e.inv)
    rw [hm] at hx
    have hi : e.inv = α := congrArg TwoSquare.natTrans hx.symm
    exact Iso.ext_inv hi

set_option maxHeartbeats 3200000 in
-- The internal and section derived-category coordinates involve dependent ring actions.
/-- Every normalized section scalar model agrees with internal derived scalar extension.
The comparison is uniquely pinned by the extension/restriction units and by the
restriction comparison which is the identity on sections.

Source: sk-prop-sp-integral-adjunction, normalization through sk-lem-sp-reduction;
sk-def-sp-coefficient-towers, section-action convention
(blueprint: lem-sp-section-scalar-derived-comparison).

Proof: internal-section scalar reconstruction supplies the identity-on-sections
restriction isomorphism. Localize this exact comparison termwise. The internal derived
extension and the given section scalar model are left adjoints of these identified
restriction functors. Their inverse mate is invertible, since both section equivalences
are equivalences. Its unit equation is the mate equation. Any second isomorphism with
that unit equation has the same mate, so injectivity of the mate correspondence proves
uniqueness. No flatness of the coefficient map is needed. -/
theorem sectionScalarDerivedComparison
    (T : Scheme.{u}) {R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    (M : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) a)) :
    let J := Scheme.ProEt.topology T
    let eR := sectionModuleEquivalence.{u + 1, u + 1, u} J R
    let eS := sectionModuleEquivalence.{u + 1, u + 1, u} J S
    let V := SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (sectionScalarMap.{u + 1, u + 1, u} J a))
    ∃ r : Mod.comap a ⋙ eR.functor ≅ eS.functor ⋙ V,
      (∀ (N : Mod (Sheaf J Ab.{u + 1}) S) (U : T.ProEtᵒᵖ)
        (x : N.X.obj.obj U), (r.hom.app N).val.app U x = x) ∧
      ∃ β : (Mod.comap a).mapDerivedCategory ⋙ eR.functor.mapDerivedCategory ≅
          eS.functor.mapDerivedCategory ⋙ V.mapDerivedCategory,
        β = (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
          Functor.mapDerivedCategoryNatIso r ≪≫ Functor.mapDerivedCategoryCompIso _ _ ∧
        ∃! e : (Mod.extendScalars a).leftDerivedFunctor ⋙
            eS.functor.mapDerivedCategory ≅ eR.functor.mapDerivedCategory ⋙ M.model.T,
          ∀ K, eR.functor.mapDerivedCategory.map
              ((Mod.derivedExtendMapDerivedCategoryAdjunction a).unit.app K) ≫
            β.hom.app ((Mod.extendScalars a).leftDerivedFunctor.obj K) ≫
            V.mapDerivedCategory.map (e.hom.app K) =
          M.adjunction.unit.app (eR.functor.mapDerivedCategory.obj K) := by
  dsimp only
  let r := scalarRestrictionIso (Scheme.ProEt.topology T) a
  let β := (Functor.mapDerivedCategoryCompIso (Mod.comap a)
      (sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T) R).functor).symm ≪≫
    Functor.mapDerivedCategoryNatIso r ≪≫
      Functor.mapDerivedCategoryCompIso
        (sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T) S).functor
        (SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose (Scheme.ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) a)))
  refine ⟨r, ?_, β, rfl, ?_⟩
  · intros
    rfl
  · exact scalarComparisonFromRestriction
      (Mod.derivedExtendMapDerivedCategoryAdjunction a) M.adjunction β

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
