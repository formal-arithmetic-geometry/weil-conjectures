/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.GeometricFiber.Forget
public import WeilConjectures.WeilSheaf.LowerShriekIndependence
public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationCoherence
public import WeilConjectures.CategoryTheory.Adjunction.BifunctorProjectionComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedComplement
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIsomorphisms

/-!
# Forgetting the Weil structure commutes with the extension by zero

Let `X ⟶[i] Z ⟶[g] Y` be the compactification of `f : X ⟶ Y` defining the direct image with
compact support of Weil complexes, and `ī` the base change of the open immersion `i` to the
geometric fibres. Forgetting the Weil structures (`For`,
`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctor`) commutes with the
extensions by zero: `ī_! ∘ For ≅ For ∘ i_!`, the mate `For ∘ i^* ⟶ ī^* ∘ For` of this
isomorphism is invertible, and `For` carries a projection formula `i_! M ⊗ N ≅ i_!(M ⊗ i^* N)` of
Weil complexes to the inverse of the projection comparison of `ī_! ⊣ ī^*` on bounded
constructible complexes
(`AlgebraicGeometry.WeilComplex.exists_extensionByZero_forget_iso_projection`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section PullTensor

variable (k₀ l) {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

set_option maxHeartbeats 1000000 in
-- the derived categories of condensed module objects are slow to elaborate
set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
/-- The derived condensed realization carries the inverse of the native pullback–tensor
comparison to the lax monoidal structure of the derived pullback `Lḡ^*` of condensed module
objects, up to the tensor comparisons `AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTensor`
and the pullback comparison
`AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso`: a reformulation of
`AlgebraicGeometry.ProEtaleWeilSheaf.comparisonCompatible_derivedCondensedRealization`. -/
theorem map_nativePullTensor_inv_app_comp (a b : DerivedCategory (ProEtaleWeilSheaf k₀ l Y)) :
    (derivedCondensedRealization k₀ l Z).map ((nativePullTensor k₀ l g).inv.app (a, b)) ≫
        (derivedCondensedRealizationUpperStarIso k₀ l g).inv.app
          ((nativeDerivedTensor k₀ l Y).obj (a, b)) ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor.map
          ((condensedRealizationTensor k₀ l Y).hom.app (a, b)) =
      (condensedRealizationTensor k₀ l Z).hom.app
          ((nativeOpenPull k₀ l g).obj a, (nativeOpenPull k₀ l g).obj b) ≫
        ((derivedCondensedRealizationUpperStarIso k₀ l g).inv.app a ⊗ₘ
          (derivedCondensedRealizationUpperStarIso k₀ l g).inv.app b) ≫
        Functor.LaxMonoidal.μ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor
          ((derivedCondensedRealization k₀ l Y).obj a)
          ((derivedCondensedRealization k₀ l Y).obj b) := by
  have H := comparisonCompatible_derivedCondensedRealization k₀ l g a b
  simp only [nativeCurriedPullTensor, condensedRealizationCurriedTensor,
    Functor.curryCompIsoOfIso_hom_app_app, Functor.curryCompIsoOfIso'_hom_app_app] at H
  simp only [curriedTensor_map_app, curriedTensor_obj_map] at H
  have H' : (derivedCondensedRealization k₀ l Z).map ((nativePullTensor k₀ l g).hom.app (a, b)) ≫
      (condensedRealizationTensor k₀ l Z).hom.app
        ((nativeOpenPull k₀ l g).obj a, (nativeOpenPull k₀ l g).obj b) =
      ((derivedCondensedRealizationUpperStarIso k₀ l g).inv.app
          ((nativeDerivedTensor k₀ l Y).obj (a, b)) ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor.map
          ((condensedRealizationTensor k₀ l Y).hom.app (a, b)) ≫
        Functor.OplaxMonoidal.δ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor
          ((derivedCondensedRealization k₀ l Y).obj a)
          ((derivedCondensedRealization k₀ l Y).obj b)) ≫
        (tensorIso ((derivedCondensedRealizationUpperStarIso k₀ l g).app a)
          ((derivedCondensedRealizationUpperStarIso k₀ l g).app b)).hom := by
    refine H.trans ?_
    simp only [Category.assoc, tensorIso_hom, Iso.app_hom, MonoidalCategory.tensorHom_def]
    rfl
  have H4 := ((Iso.comp_inv_eq _).2 H').symm
  have H5 := (Iso.comp_inv_eq (Functor.Monoidal.μIso
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g
        (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor
    ((derivedCondensedRealization k₀ l Y).obj a)
    ((derivedCondensedRealization k₀ l Y).obj b))).1 ((Category.assoc _ _ _).trans H4)
  refine (congrArg (fun t ↦ (derivedCondensedRealization k₀ l Z).map
    ((nativePullTensor k₀ l g).inv.app (a, b)) ≫ t) H5).trans ?_
  simp only [Category.assoc]
  exact ((derivedCondensedRealization k₀ l Z).mapIso
    ((nativePullTensor k₀ l g).app (a, b))).inv_hom_id_assoc _

end PullTensor

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilComplex

open ProEtale

attribute [local instance] Compactification.over

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The components of a natural isomorphism of functors to a full subcategory, obtained as the
preimage of a natural isomorphism after composition with the inclusion. -/
lemma _root_.CategoryTheory.ObjectProperty.ι_map_whiskeringRight_preimageIso_hom_app
    {C D : Type*} [Category* C] [Category* D] {P : ObjectProperty D}
    {F G : C ⥤ P.FullSubcategory} (e : F ⋙ P.ι ≅ G ⋙ P.ι) (c : C) :
    P.ι.map (((P.fullyFaithfulι.whiskeringRight C).preimageIso e).hom.app c) = e.hom.app c :=
  P.fullyFaithfulι.map_preimage _

section OpenImmersion

variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] [QuasiCompact j]
  [IsSeparated j] [LocallyOfFiniteType j]

variable (k₀ l) in
/-- Forgetting the Weil structure commutes with the restriction along `j`: the restriction to
Weil and bounded constructible complexes of the comparison
`AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso`. -/
noncomputable def upperStarForgetIso :
    upperStar j ⋙ geometricFiberBoundedConstructibleFunctor k₀ l U ≅
      geometricFiberBoundedConstructibleFunctor k₀ l X ⋙
        CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) j) :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l U) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l j).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (CondensedRing.boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj l) l
          (geometricFiberHom (k₀ := k₀) j)).symm ≪≫
      (Functor.associator _ _ _).symm)

set_option maxHeartbeats 2000000 in
lemma ι_map_upperStarForgetIso_hom_app (N : WeilComplex k₀ l X) :
    (ObjectProperty.ι _).map ((upperStarForgetIso k₀ l j).hom.app N) =
      (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l U).hom.app ((upperStar j).obj N) ≫
        (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l j).inv.app N.obj ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap j
            (comp_over j (Spec (CommRingCat.of k₀))))).leftDerivedFunctor.map
          ((geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).inv.app N) := by
  refine (ObjectProperty.ι_map_whiskeringRight_preimageIso_hom_app _ N).trans ?_
  simp [CondensedRing.boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftFullSubcategoryCompιIso]
  erw [Category.id_comp, Category.comp_id]

example : (geometricFiberHom (k₀ := k₀) j).left =
    Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))) := rfl

end OpenImmersion

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [QuasiCompact (nativeProjectionCompactification k₀ f).i]

set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
/-- **Forgetting the Weil structure commutes with the extension by zero, compatibly with the
restrictions and the projection formulas.** For the compactification `X ⟶[i] Z ⟶[g] Y` defining
`Rf₀!`, there is a natural isomorphism `β : ī_! ∘ For ≅ For ∘ i_!` such that
- its mate `For ∘ i^* ⟶ ī^* ∘ For` under `i_! ⊣ i^*` and `ī_! ⊣ ī^*` is invertible;
- for some natural isomorphism `γ : For ∘ i^* ≅ ī^* ∘ For` and some projection formula
  `e : i_! M ⊗ N ≅ i_!(M ⊗ i^* N)` of Weil complexes, `For(e)` is the inverse of the projection
  comparison `ī_!(M̄ ⊗ ī^* N̄) ⟶ ī_! M̄ ⊗ N̄` of `ī_! ⊣ ī^*`, up to `β`, `γ` and the tensor
  comparisons `AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorTensorIso`.
-/
theorem exists_extensionByZero_forget_iso_projection :
    ∃ β : geometricFiberBoundedConstructibleFunctor k₀ l X ⋙
          CondensedRing.boundedConstructibleOpenImmersionLowerShriek _ l
            (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i) ≅
        extensionByZero (nativeProjectionCompactification k₀ f).i ⋙
          geometricFiberBoundedConstructibleFunctor k₀ l (nativeProjectionCompactification k₀ f).Z,
      (∀ L, IsIso ((mateEquiv
        (extensionByZeroUpperStarAdjunction (nativeProjectionCompactification k₀ f).i)
        (CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l
          (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i))
        (TwoSquare.mk _ _ _ _ β.hom)).natTrans.app L)) ∧
      ∃ (γ : upperStar (nativeProjectionCompactification k₀ f).i ⋙
            geometricFiberBoundedConstructibleFunctor k₀ l X ≅
          geometricFiberBoundedConstructibleFunctor k₀ l (nativeProjectionCompactification k₀ f).Z ⋙
            CondensedRing.boundedConstructibleUpperStar _ l
              (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i))
        (e : (extensionByZero (nativeProjectionCompactification k₀ f).i).prod (𝟭 _) ⋙
            nativeConstructibleTensor k₀ l (nativeProjectionCompactification k₀ f).Z ≅
          (𝟭 _).prod (upperStar (nativeProjectionCompactification k₀ f).i) ⋙
            nativeConstructibleTensor k₀ l X ⋙
              extensionByZero (nativeProjectionCompactification k₀ f).i),
        ∀ M N, (geometricFiberBoundedConstructibleFunctor k₀ l
              (nativeProjectionCompactification k₀ f).Z).map (e.hom.app (M, N)) ≫
            β.inv.app _ ≫
            (CondensedRing.boundedConstructibleOpenImmersionLowerShriek _ l
              (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i)).map
              ((geometricFiberBoundedConstructibleFunctorTensorIso k₀ l X).hom.app
                  (M, (upperStar (nativeProjectionCompactification k₀ f).i).obj N) ≫
                (geometricFiberBoundedConstructibleFunctor k₀ l X).obj M ◁ γ.hom.app N) =
          (geometricFiberBoundedConstructibleFunctorTensorIso k₀ l
              (nativeProjectionCompactification k₀ f).Z).hom.app
              ((extensionByZero (nativeProjectionCompactification k₀ f).i).obj M, N) ≫
            β.inv.app M ▷ (geometricFiberBoundedConstructibleFunctor k₀ l
              (nativeProjectionCompactification k₀ f).Z).obj N ≫
            inv ((CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l
              (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i)).projectionComparison
              ((geometricFiberBoundedConstructibleFunctor k₀ l X).obj M)
              ((geometricFiberBoundedConstructibleFunctor k₀ l
                (nativeProjectionCompactification k₀ f).Z).obj N)) :=
  sorry

end AlgebraicGeometry.WeilComplex
