/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ScalarPullbackStrictConeData
import all WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
import all WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement

/-! # Unique derived descent of a supplied scalar pullback chain map -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
attribute [local implicit_reducible] integralOperationsGoodLocalization
  integralOperationsPullbackOnGood
attribute [local instance 5000] integralTowerHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} W.ProEt :=
  essentiallySmallSelf.{u, t, t + 1} _

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} W

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} W

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory in
@[irreducible] private def scalarCounitTransformation
    (W : AlgebraicGeometry.Scheme.{t}) :
    DerivedCategory.Q ⋙ completedDerivedScalarExtension l E L ι W ⟶
      completedOrdinaryScalarComplex l E L ι W ⋙ DerivedCategory.Q :=
  (completedScalarCochainModel l E L ι W).ε

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory in
private theorem scalarCounitTransformation_app
    (W : AlgebraicGeometry.Scheme.{t})
    (P : CochainComplex (integralTowerModules l E W) ℤ) :
    (scalarCounitTransformation l E L ι W).app P =
      completedScalarCounit l E L ι W P := by
  unfold scalarCounitTransformation
  exact completedScalarCochainModel_counit l E L ι W P

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory in
/-- A supplied natural chain map descends uniquely through the good localization.
Source: Stacks, categories.tex, Tag 04VG; sites-cohomology.tex, Tags 06YS and 06YT;
Steps 8–9 of strict scalar pullback cone naturality.
(blueprint: lem-sf-scalar-pullback-unique-derived-descent).

Proof: scalar extension maps good representatives to good representatives by the
first hypothesis. Lift that functor to the good subcategory. The canonical scalar
counit on Y is invertible by the second hypothesis, so its naturality gives an
isomorphism between scalar extension after the good localization and localization
after this lifted functor. On good representatives compose the E-pullback
comparison, the X scalar counit and the localization of the supplied chain map;
call the resulting transformation a. The Y scalar counit isomorphism followed by
the L-pullback comparison gives an isomorphism b from the restricted derived
target functor to the target of a. Use explicit functor associators in these
composites. Good representatives localize to the derived category, so fully
faithful precomposition descends a followed by b inverse to a unique derived
transformation. The component equation tau times b equals a is exactly the
published descent equation after inserting the two canonical counit formulas.
Proof irrelevance removes dependence on the supplied proof that the scalar
complex is good. Conversely that equation determines the restricted
transformation after cancellation of b, and faithfulness gives uniqueness. -/
theorem scalarPullbackDescent_existsUnique
    {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    (good : ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      integralOperationsGoodComplex l L Y
        ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj))
    (counit : ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
      IsIso (completedScalarCounit l E L ι Y P))
    (δ : integralOperationsPullbackComplexFunctor l E g ⋙
        completedOrdinaryScalarComplex l E L ι X ⟶
      completedOrdinaryScalarComplex l E L ι Y ⋙
        integralOperationsPullbackComplexFunctor l L g) :
    ∃! τ : integralDerivedPullback l E g ⋙ completedDerivedScalarExtension l E L ι X ⟶
        completedDerivedScalarExtension l E L ι Y ⋙ integralDerivedPullback l L g,
      ScalarPullbackDescentFormula l E L ι g δ τ := by
  let I := (integralOperationsGoodComplex l E Y).ι
  let q := integralOperationsGoodLocalization l E Y
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage I
  let : q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E Y
  let k := (integralOperationsGoodComplex l L Y).lift
    (I ⋙ completedOrdinaryScalarComplex l E L ι Y) good
  let εX : DerivedCategory.Q ⋙ completedDerivedScalarExtension l E L ι X ⟶
      completedOrdinaryScalarComplex l E L ι X ⋙ DerivedCategory.Q :=
    scalarCounitTransformation l E L ι X
  let εY : DerivedCategory.Q ⋙ completedDerivedScalarExtension l E L ι Y ⟶
      completedOrdinaryScalarComplex l E L ι Y ⋙ DerivedCategory.Q :=
    scalarCounitTransformation l E L ι Y
  have hεX (P : CochainComplex (integralTowerModules l E X) ℤ) :
      εX.app P = completedScalarCounit l E L ι X P :=
    scalarCounitTransformation_app l E L ι X P
  have hεY (P : CochainComplex (integralTowerModules l E Y) ℤ) :
      εY.app P = completedScalarCounit l E L ι Y P :=
    scalarCounitTransformation_app l E L ι Y P
  let η : q ⋙ completedDerivedScalarExtension l E L ι Y ≅
      k ⋙ integralOperationsGoodLocalization l L Y :=
    NatIso.ofComponents (fun P ↦ by
      change (completedDerivedScalarExtension l E L ι Y).obj
          (DerivedCategory.Q.obj P.obj) ≅
        DerivedCategory.Q.obj ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)
      let : IsIso (εY.app P.obj) := by rw [hεY]; exact counit _
      exact asIso (εY.app P.obj)) (by
        intro P P' f
        change (completedDerivedScalarExtension l E L ι Y).map
            (DerivedCategory.Q.map f.hom) ≫ εY.app P'.obj =
          εY.app P.obj ≫ DerivedCategory.Q.map
            ((completedOrdinaryScalarComplex l E L ι Y).map f.hom)
        exact εY.naturality f.hom)
  let Fd := integralDerivedPullback l E g ⋙ completedDerivedScalarExtension l E L ι X
  let Gd := completedDerivedScalarExtension l E L ι Y ⋙ integralDerivedPullback l L g
  let Vd := I ⋙ completedOrdinaryScalarComplex l E L ι Y ⋙
    integralOperationsPullbackComplexFunctor l L g ⋙ DerivedCategory.Q
  let AE := integralOperationsPullbackComplexFunctor l E g
  let AL := integralOperationsPullbackComplexFunctor l L g
  let SX := completedOrdinaryScalarComplex l E L ι X
  let SY := completedOrdinaryScalarComplex l E L ι Y
  let DE := integralDerivedPullback l E g
  let DL := integralDerivedPullback l L g
  let CX := completedDerivedScalarExtension l E L ι X
  let CY := completedDerivedScalarExtension l E L ι Y
  let QX : CochainComplex (integralTowerModules l E X) ℤ ⥤
      DerivedCategory (integralTowerModules l E X) := DerivedCategory.Q
  let QL : CochainComplex (integralTowerModules l L X) ℤ ⥤
      DerivedCategory (integralTowerModules l L X) := DerivedCategory.Q
  let IL := (integralOperationsGoodComplex l L Y).ι
  let qL := integralOperationsGoodLocalization l L Y
  let a : q ⋙ Fd ⟶ Vd :=
    (Functor.associator q DE CX).inv ≫
    Functor.whiskerRight (integralDerivedPullbackComparison l E g).hom CX ≫
    (Functor.associator I (AE ⋙ QX) CX).hom ≫
    Functor.whiskerLeft I
      ((Functor.associator AE QX CX).hom ≫ Functor.whiskerLeft AE εX ≫
        (Functor.associator AE SX QL).inv ≫ Functor.whiskerRight δ QL ≫
        (Functor.associator SY AL QL).hom)
  let b : q ⋙ Gd ≅ Vd :=
    (Functor.associator q CY DL).symm ≪≫ Functor.isoWhiskerRight η DL ≪≫
    Functor.associator k qL DL ≪≫
    Functor.isoWhiskerLeft k (integralDerivedPullbackComparison l L g) ≪≫
    (Functor.associator k IL (AL ⋙ QL)).symm ≪≫
    Functor.isoWhiskerRight
      ((integralOperationsGoodComplex l L Y).liftCompιIso (I ⋙ SY) good) (AL ⋙ QL) ≪≫
    Functor.associator I SY (AL ⋙ QL)
  obtain ⟨τ, hτ, hτu⟩ := localization_descent_with_comparison q V Fd Gd Vd b a
  have hb (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
      b.hom.app P =
        (integralDerivedPullback l L g).map (completedScalarCounit l E L ι Y P.obj) ≫
          (integralDerivedPullbackComparison l L g).hom.app
            ⟨(completedOrdinaryScalarComplex l E L ι Y).obj P.obj, good P⟩ := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app,
      Category.comp_id, η, NatIso.ofComponents_hom_app, id_eq, asIso_hom, hεY]
    (erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
      Category.id_comp, Category.comp_id]; rfl)
  have ha (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
      a.app P = (completedDerivedScalarExtension l E L ι X).map
          ((integralDerivedPullbackComparison l E g).hom.app P) ≫
        completedScalarCounit l E L ι X
          ((integralOperationsPullbackComplexFunctor l E g).obj P.obj) ≫
        DerivedCategory.Q.map (δ.app P.obj) := by
    simp only [a, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Functor.comp_obj, hεX]
    (erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.comp_id]; rfl)
  refine ⟨τ, ?_, ?_⟩
  · intro P hQ
    have ht := hτ P
    rw [hb P, ha P] at ht
    exact ht
  · intro τ' hτ'
    apply hτu
    intro P
    rw [hb P, ha P]
    exact hτ' P (good P)

end WeilConjectures
