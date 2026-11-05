/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.BoundedProperForget
public import WeilConjectures.WeilSheaf.Native.Projection.BoundedProjectionIso
public import WeilConjectures.WeilSheaf.Native.Projection.BoundedForgetNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.ProperProjectionForgetSquare
public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionPushNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.MonoidalProjectionForgetSquare
public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion

import WeilConjectures.Tactic.ExactModProofs

/-! # The proper projection square on Weil complexes -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory Endofunctor

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : X ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsProper g]

local notation "gb" => geometricFiberHom (k₀ := k₀) g
local notation "Λ" => Profinite.padicAlgClRingObj l

local instance : IsProper (gb).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) g
    (comp_over g (Spec (CommRingCat.of k₀))) ‹_›

set_option backward.isDefEq.respectTransparency false in
/-- The bounded proper forget square has the same components as the canonical realization
mate transported along the exact-functor compositor. -/
lemma projectionProperForgetIso_hom_app (M : WeilComplex k₀ l X) :
    ((projectionProperForgetIso k₀ l g).hom.app M).hom =
      (projectionPushForgetIso (ProEtaleWeilSheaf.nativeProperForgetIso k₀ l g)
        (projectionRealizationCompIso k₀ l X)
        (projectionRealizationCompIso k₀ l Y)).hom.app M.obj := by
  have h := projectionPushForgetIso_hom_app_of_factorization
    (ProEtaleWeilSheaf.nativeProperForgetIso k₀ l g)
    (projectionRealizationCompIso k₀ l X) (projectionRealizationCompIso k₀ l Y) M.obj
    ((adicSheafDerivedEquivCondensedMod l _).functor.map
      ((IsoAlgebra.derivedForgetCommIso (adicLowerStarGeometricFiberMapCompFrobeniusIso l g
        (comp_over g (Spec (CommRingCat.of k₀))))).hom.app M.obj) ≫
      (projectionAdicCondensedDerivedPushIso l (gb).left).hom.app
        ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory.obj M.obj))
    (by
      dsimp only [projectionRealizationCompIso, ProEtaleWeilSheaf.nativeProperForgetIso,
        asIso_hom]
      simp only [Category.assoc]
      exact_mod_proofs ProEtaleWeilSheaf.nativeProjectionPushMate_normalization k₀ l g M.obj)
  rw [h]
  simp only [projectionProperForgetIso, Functor.isoHComp, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    ObjectProperty.FullSubcategory.comp_hom]
  simp only [ObjectProperty.FullSubcategory.id_hom, Category.id_comp, Category.comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the proper projection isomorphism gives the geometric projection morphism. -/
theorem projectionForgetSquare_proper :
    ProjectionForgetSquare (projectionProperForgetIso k₀ l g)
      (compactProjectionForgetUpperStarIso k₀ l g)
      (compactProjectionForgetTensorIso k₀ l X) (compactProjectionForgetTensorIso k₀ l Y)
      (nativeBoundedProperProjectionIso (k₀ := k₀) (l := l) g).hom
      (CondensedRing.boundedConstructibleUpperStarLowerStarAdjunction l gb).projectionMorphismNatTrans := by
  have h := projectionForgetSquare_of_iso
    (ProEtaleWeilSheaf.nativeProperForgetIso k₀ l g)
    (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l g).symm
    (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l X)
    (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l Y)
    (projectionRealizationCompIso k₀ l X) (projectionRealizationCompIso k₀ l Y)
    (ProEtaleWeilSheaf.nativeProperProjectionNatTrans k₀ l g)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (gb).left).uncurriedProjectionMorphismNatTrans
    (ProEtaleWeilSheaf.nativeProperProjection_forgetSquare k₀ l g)
  apply (projectionForgetSquare_monoidal_iff _ _ _ _ _ _).2
  intro M N
  apply ObjectProperty.hom_ext
  have hm := (projectionForgetSquare_uncurried_iff _ _ _ _ _ _).1 h M.obj N.obj
  have hg := CondensedRing.boundedConstructibleProjectionMorphism_hom l gb
    ((compactProjectionForget k₀ l X).obj M) ((compactProjectionForget k₀ l Y).obj N)
  change ((CondensedRing.boundedConstructibleUpperStarLowerStarAdjunction l gb).projectionMorphism
    ((compactProjectionForget k₀ l X).obj M) ((compactProjectionForget k₀ l Y).obj N)).hom = _ at hg
  change _ ≫ _ ≫ _ = _ ≫ _ ≫
    ((CondensedRing.boundedConstructibleUpperStarLowerStarAdjunction l gb).projectionMorphism
      ((compactProjectionForget k₀ l X).obj M) ((compactProjectionForget k₀ l Y).obj N)).hom
  rw [hg]
  change ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory ⋙
      (adicSheafEquivCondensedMod l _).functor.mapDerivedCategory).map
        (((nativeBoundedProperProjectionIso g).hom.app (M, N)).hom) ≫
      ((projectionProperForgetIso k₀ l g).hom.app _).hom ≫
      (CondensedRing.lowerStar Λ (gb).left).rightDerivedFunctor.map
        (((compactProjectionForgetTensorIso k₀ l X).hom.app (M, (upperStar g).obj N)).hom ≫
          ((compactProjectionForget k₀ l X).obj M).obj ◁
            ((compactProjectionForgetUpperStarIso k₀ l g).hom.app N).hom) =
    ((compactProjectionForgetTensorIso k₀ l Y).hom.app ((derivedLowerStar g).obj M, N)).hom ≫
      ((projectionProperForgetIso k₀ l g).hom.app M).hom ▷
        ((compactProjectionForget k₀ l Y).obj N).obj ≫ _
  simp only [nativeBoundedProperProjectionIso_hom_app, projectionProperForgetIso_hom_app,
    compactProjectionForgetTensorIso_hom_app, compactProjectionForgetUpperStarIso_hom_app]
  exact hm

end AlgebraicGeometry.WeilComplex
