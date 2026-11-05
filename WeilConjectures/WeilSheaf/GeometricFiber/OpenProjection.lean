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
objects, up to the tensor comparisons
`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTensor`
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

/-- The components of a natural isomorphism of functors to a full subcategory, obtained as the
preimage of a natural isomorphism after composition with the inclusion. -/
lemma _root_.CategoryTheory.ObjectProperty.whiskeringRight_preimageIso_hom_app_hom
    {C D : Type*} [Category* C] [Category* D] {P : ObjectProperty D}
    {F G : C ⥤ P.FullSubcategory} (e : F ⋙ P.ι ≅ G ⋙ P.ι) (c : C) :
    (((P.fullyFaithfulι.whiskeringRight C).preimageIso e).hom.app c).hom = e.hom.app c :=
  P.fullyFaithfulι.map_preimage _

/-- The tensor product of morphisms in a full monoidal subcategory is computed in the ambient
category. -/
lemma _root_.CategoryTheory.ObjectProperty.FullSubcategory.tensorHom_hom {C : Type*} [Category* C]
    [MonoidalCategory C] {P : ObjectProperty C} [P.IsMonoidal] {A B A' B' : P.FullSubcategory}
    (f : A ⟶ B) (g : A' ⟶ B') : (f ⊗ₘ g).hom = f.hom ⊗ₘ g.hom :=
  rfl

/-- The image under a functor of the inverse and the hom of a natural isomorphism cancel. -/
@[reassoc]
lemma _root_.CategoryTheory.Functor.map_inv_app_comp_map_hom_app {C D E : Type*} [Category* C]
    [Category* D] [Category* E] {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ E) (c : C) :
    H.map (e.inv.app c) ≫ H.map (e.hom.app c) = 𝟙 _ := by
  rw [← H.map_comp, Iso.inv_hom_id_app, H.map_id]

section Reflect

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Forgetting the Weil structure reflects isomorphisms: so does the derived condensed
realization. -/
lemma isIso_of_isIso_geometricFiberBoundedConstructibleFunctor_map {A B : WeilComplex k₀ l X}
    (φ : A ⟶ B) [IsIso ((geometricFiberBoundedConstructibleFunctor k₀ l X).map φ)] : IsIso φ := by
  have : (ProEtaleWeilSheaf.derivedCondensedRealization k₀ l X).ReflectsIsomorphisms :=
    Functor.reflectsIsomorphisms_mapDerivedCategory _
  have h : IsIso ((geometricFiberBoundedConstructibleFunctor k₀ l X ⋙ ObjectProperty.ι _).map φ) :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map
      ((geometricFiberBoundedConstructibleFunctor k₀ l X).map φ)))
  have h' : IsIso ((ProEtaleWeilSheaf.derivedCondensedRealization k₀ l X).map φ.hom) :=
    (NatIso.isIso_map_iff (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X) φ).1 h
  have : IsIso φ.hom :=
    isIso_of_reflects_iso φ.hom (ProEtaleWeilSheaf.derivedCondensedRealization k₀ l X)
  exact (ObjectProperty.isIso_hom_iff φ).1 this

end Reflect

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
      Functor.isoWhiskerLeft _
        (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l j).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (CondensedRing.boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj l) l
          (geometricFiberHom (k₀ := k₀) j)).symm ≪≫
      (Functor.associator _ _ _).symm)

set_option maxHeartbeats 2000000 in
-- comparing the restricted and the ambient derived pullbacks is slow
omit [IsOpenImmersion j] [QuasiCompact j] [IsSeparated j] [LocallyOfFiniteType j] in
/-- The restriction comparison `AlgebraicGeometry.WeilComplex.upperStarForgetIso` on the ambient
derived categories. -/
lemma upperStarForgetIso_hom_app_hom (N : WeilComplex k₀ l X) :
    ((upperStarForgetIso k₀ l j).hom.app N).hom =
      (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l U).hom.app ((upperStar j).obj N) ≫
        (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l j).inv.app N.obj ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap j
            (comp_over j (Spec (CommRingCat.of k₀))))).leftDerivedFunctor.map
          ((geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).inv.app N) := by
  refine (ObjectProperty.whiskeringRight_preimageIso_hom_app_hom _ N).trans ?_
  simp [CondensedRing.boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftFullSubcategoryCompιIso]
  erw [Category.id_comp, Category.comp_id]

/-- Forgetting the Weil structure on morphisms, on the ambient derived categories: the derived
condensed realization, up to
`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorCompιIso`. -/
lemma geometricFiberBoundedConstructibleFunctor_map_hom {A B : WeilComplex k₀ l X} (φ : A ⟶ B) :
    ((geometricFiberBoundedConstructibleFunctor k₀ l X).map φ).hom =
      (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).hom.app A ≫
        (ProEtaleWeilSheaf.derivedCondensedRealization k₀ l X).map φ.hom ≫
        (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).inv.app B :=
  (NatIso.naturality_2 (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X) φ).symm

set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
set_option backward.isDefEq.respectTransparency false in
-- `Mod.monoidalClosed` needs `IsCommMonObj (condensedRingObj _ _)` up to instance unfolding
/-- The tensor comparison of forgetting the Weil structure, on the ambient derived categories. -/
lemma geometricFiberBoundedConstructibleFunctorTensorIso_hom_app_hom (A B : WeilComplex k₀ l X) :
    ((geometricFiberBoundedConstructibleFunctorTensorIso k₀ l X).hom.app (A, B)).hom =
      (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).hom.app
          ((nativeConstructibleTensor k₀ l X).obj (A, B)) ≫
        (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l X).hom.app (A.obj, B.obj) ≫
        ((geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).inv.app A ⊗ₘ
          (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).inv.app B) := by
  refine (ObjectProperty.whiskeringRight_preimageIso_hom_app_hom _ (A, B)).trans ?_
  simp [boundedConstructibleιTensorIso, MonoidalCategory.tensorHom_def]

open scoped CategoryTheory.Obj in
omit [IsOpenImmersion j] [QuasiCompact j] [IsSeparated j] [LocallyOfFiniteType j] in
lemma boundedConstructibleUpperStar_map_hom {A B : BoundedConstructible (condensedRingObj
    (Profinite.padicAlgClRingObj l)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)} (φ : A ⟶ B) :
    ((CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) j)).map φ).hom =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap j
          (comp_over j (Spec (CommRingCat.of k₀))))).leftDerivedFunctor.map φ.hom :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
open scoped CategoryTheory.Obj in
omit [IsOpenImmersion j] [QuasiCompact j] [IsSeparated j] [LocallyOfFiniteType j] in
lemma μ_boundedConstructibleUpperStar_hom (A B : BoundedConstructible (condensedRingObj
    (Profinite.padicAlgClRingObj l)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)) :
    (Functor.LaxMonoidal.μ
      (CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) j)) A B).hom =
      Functor.LaxMonoidal.μ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap j
          (comp_over j (Spec (CommRingCat.of k₀))))).leftDerivedFunctor A.obj B.obj :=
  rfl

variable (k₀ l) in
/-- The inverse `j^* A ⊗ j^* B ⟶ j^*(A ⊗ B)` of the native pullback–tensor comparison
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTensor`) on Weil complexes. -/
noncomputable def upperStarTensorComparison :
    (upperStar j).prod (upperStar j) ⋙ nativeConstructibleTensor k₀ l U ⟶
      nativeConstructibleTensor k₀ l X ⋙ upperStar j where
  app A := ObjectProperty.homMk
    ((ProEtaleWeilSheaf.nativePullTensor k₀ l j).inv.app (A.1.obj, A.2.obj))
  naturality _ _ φ := ObjectProperty.hom_ext _
    ((ProEtaleWeilSheaf.nativePullTensor k₀ l j).inv.naturality (Prod.mkHom φ.1.hom φ.2.hom))

set_option maxHeartbeats 8000000 in
-- the derived categories of condensed module objects are slow to elaborate
set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
omit [IsOpenImmersion j] [QuasiCompact j] [IsSeparated j] [LocallyOfFiniteType j] in
/-- Forgetting the Weil structure carries the inverse native pullback–tensor comparison to the
lax monoidal structure of the restriction `ī^*` of bounded constructible complexes, up to the
tensor comparisons
`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorTensorIso`
and `AlgebraicGeometry.WeilComplex.upperStarForgetIso`. -/
theorem map_upperStarTensorComparison_app_comp (a b : WeilComplex k₀ l X) :
    (geometricFiberBoundedConstructibleFunctor k₀ l U).map
        ((upperStarTensorComparison k₀ l j).app (a, b)) ≫
      (upperStarForgetIso k₀ l j).hom.app ((nativeConstructibleTensor k₀ l X).obj (a, b)) ≫
      (CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) j)).map
        ((geometricFiberBoundedConstructibleFunctorTensorIso k₀ l X).hom.app (a, b)) =
    (geometricFiberBoundedConstructibleFunctorTensorIso k₀ l U).hom.app
        ((upperStar j).obj a, (upperStar j).obj b) ≫
      ((upperStarForgetIso k₀ l j).hom.app a ⊗ₘ (upperStarForgetIso k₀ l j).hom.app b) ≫
      Functor.LaxMonoidal.μ
        (CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) j)) _ _ := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [geometricFiberBoundedConstructibleFunctor_map_hom, upperStarForgetIso_hom_app_hom,
    boundedConstructibleUpperStar_map_hom,
    geometricFiberBoundedConstructibleFunctorTensorIso_hom_app_hom,
    geometricFiberBoundedConstructibleFunctorTensorIso_hom_app_hom]
  simp only [ObjectProperty.FullSubcategory.tensorHom_hom, upperStarForgetIso_hom_app_hom,
    μ_boundedConstructibleUpperStar_hom]
  have H0 : (ProEtaleWeilSheaf.derivedCondensedRealization k₀ l U).map
        ((upperStarTensorComparison k₀ l j).app (a, b)).hom ≫
      (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l j).inv.app
        ((nativeConstructibleTensor k₀ l X).obj (a, b)).obj ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap j
          (comp_over j (Spec (CommRingCat.of k₀))))).leftDerivedFunctor.map
        ((ProEtaleWeilSheaf.condensedRealizationTensor k₀ l X).hom.app (a.obj, b.obj)) =
      (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l U).hom.app
        (((upperStar j).obj a).obj, ((upperStar j).obj b).obj) ≫
      ((ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l j).inv.app a.obj ⊗ₘ
        (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l j).inv.app b.obj) ≫
      Functor.LaxMonoidal.μ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap j
          (comp_over j (Spec (CommRingCat.of k₀))))).leftDerivedFunctor
        ((ProEtaleWeilSheaf.derivedCondensedRealization k₀ l X).obj a.obj)
        ((ProEtaleWeilSheaf.derivedCondensedRealization k₀ l X).obj b.obj) :=
    ProEtaleWeilSheaf.map_nativePullTensor_inv_app_comp k₀ l j a.obj b.obj
  have H := (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l U).hom.app
      ((nativeConstructibleTensor k₀ l U).obj ((upperStar j).obj a, (upperStar j).obj b)) ≫=
    (H0 =≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap j
          (comp_over j (Spec (CommRingCat.of k₀))))).leftDerivedFunctor.map
        ((geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).inv.app a ⊗ₘ
          (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).inv.app b))
  simp only [← Functor.LaxMonoidal.μ_natural, tensorHom_comp_tensorHom_assoc, Category.assoc] at H
  simp only [Category.assoc, Functor.map_comp, Functor.comp_obj, Functor.prod_obj,
    Iso.inv_hom_id_app_assoc, Functor.map_inv_app_comp_map_hom_app_assoc,
    tensorHom_comp_tensorHom_assoc]
  exact H

variable (k₀ l) in
/-- Forgetting the Weil structure of the extension by zero of a Weil complex `M` gives the
extension by zero of the underlying complex of `M`: forgetting the Weil structure commutes with
the extension by zero, and so does the condensed model
(`AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekMapDerivedCategoryCompIso`). -/
noncomputable def extensionByZeroForgetObjIso (M : WeilComplex k₀ l U) :
    (geometricFiberBoundedConstructibleFunctor k₀ l X).obj ((extensionByZero j).obj M) ≅
      (CondensedRing.boundedConstructibleOpenImmersionLowerShriek _ l
        (geometricFiberHom (k₀ := k₀) j)).obj
          ((geometricFiberBoundedConstructibleFunctor k₀ l U).obj M) :=
  ObjectProperty.isoMk _
    ((adicSheafDerivedEquivCondensedMod l _).functor.mapIso
      ((Functor.mapDerivedCategoryCompIsoOfIso (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
        (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l j
          (comp_over j _)))).app M.obj) ≪≫
     (adicOpenImmersionLowerShriekMapDerivedCategoryCompIso l _
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))).app _)

variable (k₀ l) in
/-- The comparison `ī_! ∘ For ⟶ For ∘ j_!` of the extensions by zero: the mate of the inverse of
`AlgebraicGeometry.WeilComplex.upperStarForgetIso` under `j_! ⊣ j^*` and `ī_! ⊣ ī^*`. -/
noncomputable def extensionByZeroForgetHom :
    TwoSquare (geometricFiberBoundedConstructibleFunctor k₀ l U) (extensionByZero j)
      (CondensedRing.boundedConstructibleOpenImmersionLowerShriek _ l
        (geometricFiberHom (k₀ := k₀) j))
      (geometricFiberBoundedConstructibleFunctor k₀ l X) :=
  (mateEquiv (extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j)
    (CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l
      (geometricFiberHom (k₀ := k₀) j))).symm
    (TwoSquare.mk _ _ _ _ (upperStarForgetIso k₀ l j).hom)

set_option maxHeartbeats 2000000 in
-- the derived categories of condensed module objects are slow to elaborate
/-- The comparison `ī_! ∘ For ⟶ For ∘ j_!` is an isomorphism: it is the transpose of an
isomorphism, followed by the counit of `ī_! ⊣ ī^*` at `For (j_! M) ≅ ī_! (For M)`, invertible since
`ī_!` is fully faithful. -/
instance isIso_extensionByZeroForgetHom : IsIso (extensionByZeroForgetHom k₀ l j).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have h := unit_mateEquiv_symm (extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j)
    (CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l
      (geometricFiberHom (k₀ := k₀) j)) (TwoSquare.mk _ _ _ _ (upperStarForgetIso k₀ l j).hom) M
  have h' : (extensionByZeroForgetHom k₀ l j).natTrans.app M =
      ((CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l
        (geometricFiberHom (k₀ := k₀) j)).homEquiv _ _).symm
        ((geometricFiberBoundedConstructibleFunctor k₀ l U).map
          ((extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j).unit.app M) ≫
          (upperStarForgetIso k₀ l j).hom.app ((extensionByZero j).obj M)) :=
    (Equiv.eq_symm_apply _).2 ((Adjunction.homEquiv_unit _ _ _ _).trans h.symm)
  have := (CondensedRing.fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek
    (Profinite.padicAlgClRingObj l) l
    (geometricFiberHom (k₀ := k₀) j)).full
  have := (CondensedRing.fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek
    (Profinite.padicAlgClRingObj l) l
    (geometricFiberHom (k₀ := k₀) j)).faithful
  have := (CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l
    (geometricFiberHom (k₀ := k₀) j)).isIso_counit_app_of_iso (extensionByZeroForgetObjIso k₀ l j M)
  have : IsIso (geometricFiberBoundedConstructibleFunctor k₀ l U |>.map
    ((extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j).unit.app M)) := inferInstance
  rw [h', Adjunction.homEquiv_counit]
  infer_instance

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

set_option maxHeartbeats 8000000 in
-- the derived categories of condensed module objects are slow to elaborate
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
                (nativeProjectionCompactification k₀ f).Z).obj N)) := by
  have : IsOpenImmersion (nativeProjectionCompactification k₀ f).i :=
    (nativeProjectionCompactification k₀ f).isOpenImmersion
  set adj := extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l)
    (nativeProjectionCompactification k₀ f).i
  set adj' := CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj l) l
    (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i)
  have hμ := map_upperStarTensorComparison_app_comp (k₀ := k₀) (l := l)
    (nativeProjectionCompactification k₀ f).i
  have : IsIso ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _
      (upperStarForgetIso k₀ l (nativeProjectionCompactification k₀ f).i).hom)).natTrans :=
    isIso_extensionByZeroForgetHom (k₀ := k₀) (l := l) (nativeProjectionCompactification k₀ f).i
  have hp (M : WeilComplex k₀ l X)
      (N : WeilComplex k₀ l (nativeProjectionCompactification k₀ f).Z) :
      IsIso (adj.bifunctorProjectionComparison
        (upperStarTensorComparison k₀ l (nativeProjectionCompactification k₀ f).i) M N) := by
    have := adj.isIso_map_bifunctorProjectionComparison
      (upperStarTensorComparison k₀ l (nativeProjectionCompactification k₀ f).i) adj'
      (upperStarForgetIso k₀ l (nativeProjectionCompactification k₀ f).i).hom
      (geometricFiberBoundedConstructibleFunctorTensorIso k₀ l X)
      (geometricFiberBoundedConstructibleFunctorTensorIso k₀ l
        (nativeProjectionCompactification k₀ f).Z) hμ M N
    exact isIso_of_isIso_geometricFiberBoundedConstructibleFunctor_map _
  refine ⟨asIso (extensionByZeroForgetHom k₀ l (nativeProjectionCompactification k₀ f).i).natTrans,
    fun L ↦ ?_, upperStarForgetIso k₀ l (nativeProjectionCompactification k₀ f).i,
    adj.bifunctorProjectionIso
      (upperStarTensorComparison k₀ l (nativeProjectionCompactification k₀ f).i),
    fun M N ↦ adj.map_bifunctorProjectionIso_hom_app
      (upperStarTensorComparison k₀ l (nativeProjectionCompactification k₀ f).i) adj'
      (upperStarForgetIso k₀ l (nativeProjectionCompactification k₀ f).i).hom
      (geometricFiberBoundedConstructibleFunctorTensorIso k₀ l X)
      (geometricFiberBoundedConstructibleFunctorTensorIso k₀ l
        (nativeProjectionCompactification k₀ f).Z) hμ _ rfl M N⟩
  have h : mateEquiv adj adj' (TwoSquare.mk _ _ _ _
      (asIso (extensionByZeroForgetHom k₀ l
        (nativeProjectionCompactification k₀ f).i).natTrans).hom) =
      TwoSquare.mk _ _ _ _
        (upperStarForgetIso k₀ l (nativeProjectionCompactification k₀ f).i).hom :=
    (mateEquiv adj adj').apply_symm_apply _
  rw [h]
  exact inferInstanceAs
    (IsIso ((upperStarForgetIso k₀ l (nativeProjectionCompactification k₀ f).i).hom.app L))

end AlgebraicGeometry.WeilComplex
