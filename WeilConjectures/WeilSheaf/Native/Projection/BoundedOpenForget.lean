/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.OpenProjectionForget
public import WeilConjectures.WeilSheaf.Native.Projection.CompactForgetComparison
public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionForgetIsoTransport

/-! # The canonical open forget square on bounded constructible complexes -/

@[expose] public noncomputable section

universe u

open CategoryTheory Endofunctor

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

/-- The exceptional mate of the open forget square is invertible. -/
theorem isIso_mateEquiv_projectionOpenForgetIso :
    IsIso (mateEquiv (extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j)
      (CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l jb)
      (projectionOpenForgetIso k₀ l j).inv).natTrans := by
  let A := ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l j
  let B := CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ jb.left
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
  have hu (K : BoundedConstructible (condensedRingObj Λ
      (U ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :
      (b.unit.app K).hom = B.unit.app K.obj := by
    change (ObjectProperty.ι _).map ((B.restrictFullyFaithful
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (Iso.refl _) (Iso.refl _)).unit.app K) = _
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hc : (a.counit.app M).hom = A.counit.app M.obj := by
    change (ObjectProperty.ι _).map ((A.restrictFullyFaithful
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (Iso.refl _) (Iso.refl _)).counit.app M) = _
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    simp
  have hm : ((mateEquiv a b (projectionOpenForgetIso k₀ l j).inv).app M).hom =
      (mateEquiv A B (projectionOpenCompositeForgetIso k₀ l j).inv).app M.obj := by
    simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
      Category.comp_id]
    change (b.unit.app _).hom ≫ _ ≫ _ = _
    rw [hu, hc]
    rfl
  apply isIso_of_reflects_iso _ (boundedConstructible _).ι
  change IsIso (((mateEquiv a b (projectionOpenForgetIso k₀ l j).inv).app M).hom)
  rw [hm]
  infer_instance

end AlgebraicGeometry.WeilComplex
