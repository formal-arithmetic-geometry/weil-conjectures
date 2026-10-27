/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-!
# Normalized derived open adjunction for condensed modules

Source: Stacks Project, proetale.tex, Tag 09BN, lemma-open-immersion;
categories.tex, Tag 04VG, lemma-properties-left-localization; blueprint main-20261015,
det-sf-comp-composition-interchange, Proof (2)
(blueprint: lem-sfb-condensed-open-adjunction-localization).

The two factorization equations specify the descent of the actual module adjunction.
Integer shifts use the canonical exact-functor shift structures on the unbounded
localizations. No constructibility restriction is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem derived_unit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (adj : L ⊣ R) (b : L.mapDerivedCategory ⊣ R.mapDerivedCategory)
    (hb : ∀ K, b.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        R.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj K) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app K)) :
    NatTrans.CommShift b.unit ℤ := by
  have : NatTrans.CommShift (adj.mapHomologicalComplex (.up ℤ)).unit ℤ := by
    constructor
    intro n
    ext K i
    dsimp [Adjunction.mapHomologicalComplex]
    simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app,
      HomologicalComplex.id_f, CochainComplex.shiftFunctor_obj_X', Category.id_comp]
    erw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  have he : Functor.whiskerLeft DerivedCategory.Q b.unit =
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (adj.mapHomologicalComplex (.up ℤ)).unit DerivedCategory.Q ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (L.mapHomologicalComplex (.up ℤ)) R.mapDerivedCategoryFactors.inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight L.mapDerivedCategoryFactors.inv R.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom := by
    ext K
    simpa using hb K
  have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Q b.unit) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Q
    (fun X ↦ ⟨_, (DerivedCategory.Q.objObjPreimageIso X).inv, inferInstance⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem shifted_hom_equiv
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {L : C ⥤ D} {R : D ⥤ C} [L.CommShift ℤ] [R.CommShift ℤ]
    (b : L ⊣ R) [b.CommShift ℤ] (A : C) (B : D) (f : L.obj A ⟶ B) (n : ℤ) :
    b.homEquiv (A⟦n⟧) (B⟦n⟧) ((L.commShiftIso n).hom.app A ≫ f⟦n⟧') =
      (shiftFunctor _ n).map (b.homEquiv A B f) ≫ (R.commShiftIso n).inv.app B := by
  rw [← cancel_mono ((R.commShiftIso n).hom.app B)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [R.commShiftIso_hom_naturality, ← Category.assoc, ← Category.assoc,
    Category.assoc (b.unit.app _) (R.map _) _, ← b.shift_unit_app n A]
  exact ((shiftFunctor _ n).map_comp _ _).symm

private theorem derived_unit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (adj : L ⊣ R) [IsIso adj.unit] (b : L.mapDerivedCategory ⊣ R.mapDerivedCategory)
    (hb : ∀ K, b.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        R.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj K) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app K)) :
    IsIso b.unit := by
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  have := (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q W
    (DerivedCategory C)).reflectsIsomorphisms
  have (K : CochainComplex C ℤ) : IsIso (b.unit.app (DerivedCategory.Q.obj K)) := by
    have (i : ℤ) : IsIso (((adj.mapHomologicalComplex (.up ℤ)).unit.app K).f i) := by
      change IsIso (adj.unit.app (K.X i))
      infer_instance
    have := HomologicalComplex.Hom.isIso_of_components
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app K)
    rw [hb]
    infer_instance
  have : ∀ K, IsIso ((Functor.whiskerLeft DerivedCategory.Q b.unit).app K) :=
    fun K ↦ ‹∀ K, IsIso (b.unit.app (DerivedCategory.Q.obj K))› K
  have hi : IsIso (Functor.whiskerLeft DerivedCategory.Q b.unit) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (((Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q).map b.unit) := hi
  exact isIso_of_reflects_iso b.unit ((Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q)

private theorem open_unit_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {V X : Scheme.{u}}
    (h : V ⟶ X) [IsOpenImmersion h] :
    IsIso (openImmersionLowerShriekUpperStarAdjunction Λ h).unit := by
  let ff := (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ h)).fullyFaithfulFunctor.comp
    (AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction
      AddCommGrpCat.{u + 1} h).fullyFaithfulMapModLeft
  have : (openImmersionLowerShriek Λ h).Full := ff.full
  have : (openImmersionLowerShriek Λ h).Faithful := ff.faithful
  infer_instance

/-- Exactness, normalized descent, invertible units and integer-shift compatibility for
open extension by zero on internal modules over the pulled-back condensed coefficient.
Source: Stacks 09BN and 04VG; blueprint det-sf-comp-composition-interchange, Proof (2)
(blueprint: lem-sfb-condensed-open-adjunction-localization).

Proof: the existing exactness instances supply the first six clauses. The abelian
open extension is fully faithful, as is its projection-formula linearization. Composing
with restriction along the coefficient isomorphism proves full faithfulness of the
actual module extension, hence invertibility of its specified adjunction unit.
Localize the termwise adjunction using the canonical exact-functor factorization maps;
Mathlib's localization unit and counit formulas give the two normalization equations.
The cochain unit is invertible degreewise, and fully faithful precomposition with the
localization reflects invertibility of the derived unit. In degree i, the termwise
unit shift square reduces to the original unit in degree i+n. Its localization and
both canonical factorization maps commute with shifts, so the derived unit does too.
The adjunction identities then give the counit shift square. Finally expand the Hom
bijection using the unit, and apply its shift square and shift-comparison naturality.
All these calculations use arbitrary unbounded complexes and every integer shift.
-/
theorem condensed_open_adjunction_localization
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    {V X : Scheme.{u}} [V.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (h : V ⟶ X) [h.IsOver (Spec (.of k))] [IsOpenImmersion h] [QuasiCompact h] :
    (openImmersionLowerShriek Λ h).Additive ∧
    PreservesFiniteLimits (openImmersionLowerShriek Λ h) ∧
    PreservesFiniteColimits (openImmersionLowerShriek Λ h) ∧
    (upperStar Λ h).Additive ∧ PreservesFiniteLimits (upperStar Λ h) ∧
    PreservesFiniteColimits (upperStar Λ h) ∧
    IsIso (openImmersionLowerShriekUpperStarAdjunction Λ h).unit ∧
    ∃ adj : (openImmersionLowerShriek Λ h).mapDerivedCategory ⊣
        (upperStar Λ h).mapDerivedCategory,
      (∀ K : CochainComplex
          (Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1})
            (condensedRingObj Λ V)) ℤ,
        adj.unit.app (DerivedCategory.Q.obj K) ≫
            (upperStar Λ h).mapDerivedCategory.map
              ((openImmersionLowerShriek Λ h).mapDerivedCategoryFactors.hom.app K) ≫
            (upperStar Λ h).mapDerivedCategoryFactors.hom.app
              (((openImmersionLowerShriek Λ h).mapHomologicalComplex (.up ℤ)).obj K) =
          DerivedCategory.Q.map
            (((openImmersionLowerShriekUpperStarAdjunction Λ h).mapHomologicalComplex
              (.up ℤ)).unit.app K)) ∧
      (∀ M : CochainComplex
          (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
            (condensedRingObj Λ X)) ℤ,
        adj.counit.app (DerivedCategory.Q.obj M) =
          (openImmersionLowerShriek Λ h).mapDerivedCategory.map
              ((upperStar Λ h).mapDerivedCategoryFactors.hom.app M) ≫
            (openImmersionLowerShriek Λ h).mapDerivedCategoryFactors.hom.app
              (((upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj M) ≫
            DerivedCategory.Q.map
              (((openImmersionLowerShriekUpperStarAdjunction Λ h).mapHomologicalComplex
                (.up ℤ)).counit.app M)) ∧
      IsIso adj.unit ∧ NatTrans.CommShift adj.unit ℤ ∧
      NatTrans.CommShift adj.counit ℤ ∧
      (∀ (A : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1})
            (condensedRingObj Λ V)))
        (B : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
            (condensedRingObj Λ X)))
        (f : (openImmersionLowerShriek Λ h).mapDerivedCategory.obj A ⟶ B) (n : ℤ),
        adj.homEquiv (A⟦n⟧) (B⟦n⟧)
            (((openImmersionLowerShriek Λ h).mapDerivedCategory.commShiftIso n).hom.app A ≫
              f⟦n⟧') =
          (shiftFunctor _ n).map (adj.homEquiv A B f) ≫
            ((upperStar Λ h).mapDerivedCategory.commShiftIso n).inv.app B) := by
  have _hΛ := hΛ
  have _hp := hp
  have _hpℓ := hpℓ
  have hu := open_unit_isIso Λ h
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hu, ?_⟩
  let L := openImmersionLowerShriek Λ h
  let R := upperStar Λ h
  let a := openImmersionLowerShriekUpperStarAdjunction Λ h
  let : CatCommSq (L.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q L.mapDerivedCategory := ⟨L.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (R.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q R.mapDerivedCategory := ⟨R.mapDerivedCategoryFactors.symm⟩
  let b := (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    L.mapDerivedCategory R.mapDerivedCategory
  have hb (K) : b.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        R.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj K) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app K) :=
    (a.mapHomologicalComplex (.up ℤ)).localization_unit_app _ _ _ _ _ _ K
  refine ⟨b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K
    dsimp only [L, R, a] at hb
    rw [hb]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app,
      Category.comp_id]
  · intro M
    exact (a.mapHomologicalComplex (.up ℤ)).localization_counit_app _ _ _ _ _ _ M
  · exact derived_unit_isIso a b hb
  · exact derived_unit_commShift a b hb
  · have := derived_unit_commShift a b hb
    have := Adjunction.CommShift.mk' b ℤ this
    infer_instance
  · intro A B f n
    have := derived_unit_commShift a b hb
    have := Adjunction.CommShift.mk' b ℤ this
    exact shifted_hom_equiv b A B f n

end AlgebraicGeometry.ProEtale.CondensedRing
