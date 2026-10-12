/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-!
# Abelian sheaves and modules over the lifted integers

The forgetful equivalence from modules over `ULift ℤ` to abelian groups induces an exact
equivalence of étale sheaves and of their bounded below derived categories. Geometric
stalks and homology commute with this equivalence, so it identifies the two torsion
homology conditions used in proper base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The coefficient equivalence transports the derived proper base-change mate. The proof is
the remaining formal transport step: use the restriction-of-scalars derived comparison,
the `forget₂` pullback mate, and uniqueness of left adjoints. -/
lemma isIso_baseChange_of_isProper_of_moduleComparison [IsProper f]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : DerivedCategory.Plus.torsionHomology X K) :
    IsIso ((Etale.baseChange Ab.{u + 1} sq.toCommSq).app K) := by
  sorry

/-- Forgetting the action of the lifted integers is an equivalence: restriction of scalars
along `ℤ ≃+* ULift ℤ` followed by the usual equivalence between integer modules and
abelian groups. -/
noncomputable instance forgetULiftInt_isEquivalence :
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Ab.{u + 1}).IsEquivalence := by
  let F := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv (R := ℤ)).symm.toRingHom
  have : F.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv _
  exact inferInstanceAs (F ⋙ forget₂ (ModuleCat.{u + 1} ℤ) Ab.{u + 1}).IsEquivalence

/-- The underlying abelian sheaf functor for modules over the lifted integers. -/
noncomputable abbrev forgetIntSheaf (X : Scheme.{u}) :=
  sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Ab.{u + 1})

/-- Forgetting the integer action induces an equivalence on étale sheaves. -/
noncomputable instance forgetIntSheaf_isEquivalence (X : Scheme.{u}) :
    (forgetIntSheaf X).IsEquivalence := by
  let E := (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Ab.{u + 1}).asEquivalence
  have : E.functor.IsEquivalence := inferInstanceAs
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Ab.{u + 1}).IsEquivalence
  have : (sheafCompose X.smallEtaleTopology E.functor).EssSurj := ⟨fun F ↦ by
    let F' := (sheafCompose X.smallEtaleTopology E.inverse).obj F
    refine ⟨F', ⟨?_⟩⟩
    exact {
      hom := ObjectProperty.homMk (Functor.whiskerLeft F.obj E.counitIso.hom)
      inv := ObjectProperty.homMk (Functor.whiskerLeft F.obj E.counitIso.inv)
      hom_inv_id := by ext U : 3; exact E.counitIso.hom_inv_id_app _
      inv_hom_id := by ext U : 3; exact E.counitIso.inv_hom_id_app _ }⟩
  change (sheafCompose X.smallEtaleTopology E.functor).IsEquivalence
  exact { }

/-- Forgetting the integer action on sheaves preserves addition of morphisms. -/
instance forgetIntSheaf_additive (X : Scheme.{u}) : (forgetIntSheaf X).Additive where
  map_add := by intros; rfl

/-- The equivalence of bounded below derived categories obtained by forgetting the
integer action degreewise. -/
noncomputable def abModuleDerivedEquivalence (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) ≌
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}) := by
  let E := (forgetIntSheaf X).asEquivalence
  have : E.functor.Additive := inferInstanceAs (forgetIntSheaf X).Additive
  exact CategoryTheory.Equivalence.mk E.functor.mapDerivedCategoryPlus E.inverse.mapDerivedCategoryPlus
    ((Functor.mapDerivedCategoryPlusIdIso _).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso E.unitIso ≪≫
      Functor.mapDerivedCategoryPlusCompIso _ _)
    ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso E.counitIso ≪≫
      Functor.mapDerivedCategoryPlusIdIso _)

/-- Torsion of abelian étale sheaves is invariant under isomorphisms, since the
isomorphisms on geometric stalks are isomorphisms of abelian groups. -/
lemma isTorsionSheaf_iff_of_iso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology Ab.{u + 1}} (e : F ≅ G) :
    Scheme.IsTorsionSheaf F ↔ Scheme.IsTorsionSheaf G := by
  refine ⟨fun h ↦ ⟨fun Ω _ _ s ↦ ?_⟩, fun h ↦ ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · let e' := (Scheme.pointSmallEtale s).sheafFiber.mapIso e
    exact IsAddTorsion.of_surjective (f := e'.hom.hom)
      (ConcreteCategory.bijective_of_isIso _).2 (h.isTorsion_sheafFiber Ω s)
  · let e' := (Scheme.pointSmallEtale s).sheafFiber.mapIso e
    exact IsAddTorsion.of_surjective (f := e'.inv.hom)
      (ConcreteCategory.bijective_of_isIso _).2 (h.isTorsion_sheafFiber Ω s)

/-- The forgetful equivalence identifies stalkwise torsion of module sheaves with
stalkwise torsion of abelian sheaves. Geometric stalks commute with `forget₂`. -/
lemma isTorsionModuleSheaf_iff_forgetIntSheaf {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    Scheme.IsTorsionModuleSheaf F ↔ Scheme.IsTorsionSheaf ((forgetIntSheaf X).obj F) := by
  rw [Scheme.isTorsionSheaf_iff_isTorsion, Scheme.isTorsionModuleSheaf_iff_isTorsion]

/-- Exactness of the forgetful equivalence identifies the torsion conditions on all
homology sheaves of a bounded below complex. -/
lemma moduleTorsionHomology_iff_forgetIntSheaf {X : Scheme.{u}}
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))) :
    DerivedCategory.Plus.moduleTorsionHomology (ULift.{u + 1} ℤ) X K ↔
      DerivedCategory.Plus.torsionHomology X
        ((forgetIntSheaf X).mapDerivedCategoryPlus.obj K) := by
  change (∀ n, Scheme.IsTorsionModuleSheaf _) ↔ ∀ n, Scheme.IsTorsionSheaf _
  apply forall_congr'
  intro n
  rw [isTorsionModuleSheaf_iff_forgetIntSheaf]
  exact (isTorsionSheaf_iff_of_iso
    (((forgetIntSheaf X).mapDerivedCategoryPlusHomologyFunctorIso n).app K))

/-- Torsion homology of bounded below complexes of abelian sheaves is invariant under
isomorphisms, by invariance of each homology sheaf. -/
lemma torsionHomology_iff_of_iso {X : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})} (e : K ≅ L) :
    DerivedCategory.Plus.torsionHomology X K ↔ DerivedCategory.Plus.torsionHomology X L := by
  apply forall_congr'
  intro n
  exact isTorsionSheaf_iff_of_iso
    ((_root_.DerivedCategory.Plus.homologyFunctor _ n).mapIso e)

end AlgebraicGeometry.Etale
