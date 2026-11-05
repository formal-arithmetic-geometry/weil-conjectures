/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.OpenProjectionForget
public import WeilConjectures.WeilSheaf.Native.Projection.CompactForgetComparison
public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionForgetIsoTransport
public import WeilConjectures.WeilSheaf.Native.Projection.MateComponentFormula

/-! # The canonical open forget square on bounded constructible complexes -/

@[expose] public noncomputable section

universe u

open CategoryTheory Endofunctor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  (j : U ⟶ Z) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] [QuasiCompact j]

local notation "jb" => geometricFiberHom (k₀ := k₀) j
local notation "Λ" => Profinite.padicAlgClRingObj l

local instance : IsOpenImmersion (jb).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsOpenImmersion) j
    (comp_over j (Spec (CommRingCat.of k₀))) ‹_›

/-- The open forget square in the composite realization model. -/
def projectionOpenCompositeForgetIso :=
  projectionPushForgetIso (ProEtaleWeilSheaf.nativeOpenForgetIso k₀ l j)
    (Functor.mapDerivedCategoryCompIso
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U))
      (adicSheafEquivCondensedMod l _).functor)
    (Functor.mapDerivedCategoryCompIso
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
      (adicSheafEquivCondensedMod l _).functor)

/-- The canonical open forget square, restricted to Weil complexes. -/
def projectionOpenForgetIso :
    extensionByZero j ⋙ compactProjectionForget k₀ l Z ≅
      compactProjectionForget k₀ l U ⋙
        CondensedRing.boundedConstructibleOpenImmersionLowerShriek Λ l jb :=
  ((boundedConstructible _).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (objectProperty k₀ l U).ι (projectionOpenCompositeForgetIso k₀ l j))

/-- The bounded Weil open counit is the ambient counit. -/
lemma projectionOpenAdjunction_counit_app_hom (M : WeilComplex k₀ l Z) :
    ((extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j).counit.app M).hom =
      (ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l j).counit.app M.obj := by
  let A := ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l j
  change (objectProperty k₀ l Z).ι.map ((A.restrictFullyFaithful
    (L := extensionByZero (k₀ := k₀) (l := l) j) (R := upperStar j)
    (objectProperty k₀ l U).fullyFaithfulι (objectProperty k₀ l Z).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)).counit.app M) = _
  refine (Adjunction.map_restrictFullyFaithful_counit_app A
    (L := extensionByZero (k₀ := k₀) (l := l) j) (R := upperStar j)
    (objectProperty k₀ l U).fullyFaithfulι (objectProperty k₀ l Z).fullyFaithfulι
    (Iso.refl _) (Iso.refl _) M).trans ?_
  simp only [Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The bounded geometric open unit is the ambient unit. -/
lemma projectionOpenAdjunction_unit_app_hom (K : BoundedConstructible (condensedRingObj Λ
      (U ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :
      ((CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l jb).unit.app K).hom =
      (CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ (jb).left).unit.app K.obj := by
    let B := CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ (jb).left
    change (ObjectProperty.ι _).map ((B.restrictFullyFaithful
      (L := CondensedRing.boundedConstructibleOpenImmersionLowerShriek Λ l jb)
      (R := CondensedRing.boundedConstructibleUpperStar Λ l jb)
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (CondensedRing.boundedConstructibleOpenImmersionLowerShriekCompatibility Λ l jb).symm
      (CondensedRing.boundedConstructibleUpperStarCompatibility Λ l jb).symm).unit.app K) = _
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp [CondensedRing.boundedConstructibleOpenImmersionLowerShriekCompatibility,
      CondensedRing.boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso]
    rfl

/-- The bounded open mate has the underlying ambient mate. -/
lemma projectionOpenMate_app_hom (M : WeilComplex k₀ l Z) :
    ((mateEquiv (extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j)
      (CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l jb)
      (projectionOpenForgetIso k₀ l j).inv).app M).hom =
    (mateEquiv (ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l j)
      (CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ (jb).left)
      (projectionOpenCompositeForgetIso k₀ l j).inv).app M.obj := by
  rw [projection_mateEquiv_app, projection_mateEquiv_app]
  change ((CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l jb).unit.app _).hom ≫ _ ≫ _ = _
  rw [projectionOpenAdjunction_unit_app_hom]
  change _ ≫ _ ≫ (CondensedRing.upperStar Λ (jb).left).leftDerivedFunctor.map
    (((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)).mapDerivedCategory ⋙
      (adicSheafEquivCondensedMod l _).functor.mapDerivedCategory).map
        (((extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j).counit.app M).hom)) = _
  rw [projectionOpenAdjunction_counit_app_hom]
  rfl

/-- The exceptional mate of the open forget square is invertible. -/
theorem isIso_mateEquiv_projectionOpenForgetIso :
    IsIso (mateEquiv (extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j)
      (CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l jb)
      (projectionOpenForgetIso k₀ l j).inv).natTrans := by
  let A := ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l j
  let B := CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ (jb).left
  have hcan : IsIso (mateEquiv A B (ProEtaleWeilSheaf.nativeOpenForgetIso k₀ l j).inv).natTrans := by
    change IsIso ((mateEquiv A B) ((mateEquiv A B).symm
      (TwoSquare.mk _ _ _ _ (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso
        k₀ l j).inv))).natTrans
    rw [Equiv.apply_symm_apply]
    infer_instance
  have hd : IsIso (mateEquiv A B (projectionOpenCompositeForgetIso k₀ l j).inv).natTrans :=
    isIso_mateEquiv_projectionPushForgetIso A B _ _ _
  let a := extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j
  let b := CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l jb
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hm := projectionOpenMate_app_hom k₀ l j M
  apply isIso_of_reflects_iso _ (boundedConstructible _).ι
  change IsIso (((mateEquiv a b (projectionOpenForgetIso k₀ l j).inv).app M).hom)
  rw [hm]
  infer_instance

end AlgebraicGeometry.WeilComplex
