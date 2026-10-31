/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.SfScalarExtensionComposition
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.AlgebraicGeometry.IntrinsicQbarCategory
public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Descent on the framework common-stage coefficient categories

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, algebraically closed coefficient
and Weil-structures paragraphs (blueprint: lem-sf-framework-common-stage-descent).

The stages, transitions, associators, units, shifts and triangles are the recorded
intrinsic framework constructions. The linear structures are their published
finite-compositum scalar actions. StageSystem.Morphism bundles exactly the tower
square; no identity transition is replaced by a literal identity functor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe d u t r v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry

namespace WeilConjectures

/-- The actual multiplication-unit square, expressed without normalizing the identity
transition to an identity functor. HEq transports the published equality of transitions.
Source: algebraically closed coefficient paragraph, unit compatibility
(blueprint: lem-sf-framework-common-stage-descent). -/
def sfFrameworkUnitCompatible (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{t}) (S : Scheme.{u})
    (F : StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω S)) : Prop :=
  ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq ((F.β (le_refl E)).hom.app K)
      ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω S E).hom.app
          ((F.Φ E).obj K) ≫
        (F.Φ E).map ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω T E).inv.app K))

/-- The hypotheses of framework descent, retaining the actual scalar tower square
in system.coh. The unit equation uses the actual multiplication units; HEq only
accommodates the published stage system's equality with the tensor transitions.
Source: algebraically closed coefficient paragraph, extracted descent interface
(blueprint: lem-sf-framework-common-stage-descent). -/
structure SfFrameworkFamily (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{t}) (S : Scheme.{u}) where
  system : StageSystem.Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω S)
  [shift : ∀ E, (system.Φ E).CommShift ℤ]
  [additive : ∀ E, (system.Φ E).Additive]
  [linear : ∀ E, (system.Φ E).Linear E.val]
  [exact : ∀ E, (system.Φ E).IsTriangulated]
  scalar_shift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    NatTrans.CommShift (system.β h).hom ℤ
  unit : sfFrameworkUnitCompatible l Ω T S system

attribute [instance] SfFrameworkFamily.shift SfFrameworkFamily.additive
  SfFrameworkFamily.linear SfFrameworkFamily.exact

variable {l : ℕ} [Fact l.Prime]
  {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {T : Scheme.{t}} {S : Scheme.{u}} {V : Scheme.{r}}

section PairTransformations
universe w a b a' b'
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type a} [∀ i, Category.{b} (C i)]
  {D : Type a'} [Category.{b'} D]

private def pairNatTrans (U : StageSystem C) (J K : U.PairCategory ⥤ D)
    (τ : ∀ i, U.ι i ⋙ J ⟶ U.ι i ⋙ K)
    (comm : ∀ {i j : I} (h : i ≤ j) (X : C i),
      J.map ((U.transIso h).hom.app X) ≫ (τ i).app X =
        (τ j).app ((U.T h).obj X) ≫ K.map ((U.transIso h).hom.app X)) : J ⟶ K where
  app X := (τ X.stage).app X.obj
  naturality {X Y} f := by
    have comm_inv {i j : I} (h : i ≤ j) (Z : C i) :
        J.map ((U.transIso h).inv.app Z) ≫ (τ j).app ((U.T h).obj Z) =
          (τ i).app Z ≫ K.map ((U.transIso h).inv.app Z) := by
      rw [← cancel_mono (K.map ((U.transIso h).hom.app Z)), Category.assoc,
        ← comm, ← J.map_comp_assoc]
      simp
    induction f using StageSystem.PairCategory.hom_induction with
    | h n hX hY u =>
      rw [StageSystem.mkHom_eq_isoToStage, J.map_comp, J.map_comp, K.map_comp, K.map_comp]
      simp only [Category.assoc]
      change J.map ((U.transIso hX).inv.app X.obj) ≫
          J.map ((U.ι n).map u) ≫ J.map ((U.transIso hY).hom.app Y.obj) ≫
          (τ Y.stage).app Y.obj =
        (τ X.stage).app X.obj ≫
          (K.map ((U.transIso hX).inv.app X.obj) ≫
            K.map ((U.ι n).map u) ≫ K.map ((U.transIso hY).hom.app Y.obj))
      have hn := (τ n).naturality u
      dsimp only [Functor.comp_map] at hn
      rw [comm, reassoc_of% hn, reassoc_of% (comm_inv hX X.obj)]

omit [IsDirectedOrder I] in
private theorem pairComposite_shift.{c, c'}
    {D' : I → Type a'} [∀ i, Category.{b'} (D' i)]
    {E' : I → Type c} [∀ i, Category.{c'} (E' i)]
    {U : StageSystem C} {W : StageSystem D'} {Z : StageSystem E'}
    [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D' i) ℤ]
    [∀ i, HasShift (E' i) ℤ]
    [∀ {i j : I} (h : i ≤ j), (U.T h).CommShift ℤ]
    [∀ {i j : I} (h : i ≤ j), (W.T h).CommShift ℤ]
    [∀ {i j : I} (h : i ≤ j), (Z.T h).CommShift ℤ]
    (F : U.Morphism W) (G : W.Morphism Z)
    [∀ i, (F.Φ i).CommShift ℤ] [∀ i, (G.Φ i).CommShift ℤ]
    (hF : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)
    (hG : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (G.β h).hom ℤ)
    {i j : I} (h : i ≤ j) :
    @NatTrans.CommShift _ _ _ _ _ _ ((F.comp G).β h).hom ℤ _ _ _
      (inferInstanceAs (((F.Φ i ⋙ G.Φ i) ⋙ Z.T h).CommShift ℤ))
      (inferInstanceAs ((U.T h ⋙ (F.Φ j ⋙ G.Φ j)).CommShift ℤ)) := by
  have := hF h
  have := hG h
  change NatTrans.CommShift
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (F.Φ i) (G.β h) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (F.β h) (G.Φ j) ≪≫
        Functor.associator _ _ _).hom ℤ
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance

private theorem pairFunctor_transIso
    {D' : I → Type a'} [∀ i, Category.{b'} (D' i)]
    {U : StageSystem C} {W : StageSystem D'} (F : U.Morphism W)
    {i j : I} (h : i ≤ j) (X : C i) :
    F.functor.map ((U.transIso h).hom.app X) =
      (W.ι j).map ((F.β h).inv.app X) ≫
        (W.transIso h).hom.app ((F.Φ i).obj X) := by
  rw [StageSystem.transIso_hom_app_eq, F.functor_map_mkHom,
    StageSystem.ι_map_eq le_rfl, StageSystem.transIso_hom_app_eq,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  congr 1
  change (F.β le_rfl).hom.app ((U.T h).obj X) ≫
      (F.Φ j).map ((U.assoc h le_rfl).hom.app X) ≫ (F.β h).inv.app X =
    (W.T le_rfl).map ((F.β h).inv.app X) ≫
      (W.assoc h le_rfl).hom.app ((F.Φ i).obj X)
  rw [← cancel_epi ((W.T le_rfl).map ((F.β h).hom.app X))]
  rw [reassoc_of% (F.coh h le_rfl X)]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  change (W.assoc h le_rfl).hom.app ((F.Φ i).obj X) ≫ 𝟙 _ =
    (W.T le_rfl).map (𝟙 ((W.T h).obj ((F.Φ i).obj X))) ≫
      (W.assoc h le_rfl).hom.app ((F.Φ i).obj X)
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

section PairShift
variable {D' : I → Type a'} [∀ i, Category.{b'} (D' i)]
  {U : StageSystem C} {W : StageSystem D'}
  [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D' i) ℤ]
  [HasShift U.PairCategory ℤ] [HasShift W.PairCategory ℤ]
  [∀ i, (U.ι i).CommShift ℤ] [∀ i, (W.ι i).CommShift ℤ]
  (F : U.Morphism W) [∀ i, (F.Φ i).CommShift ℤ]

private def pairStageShiftIso (n : ℤ) (i : I) :
    U.ι i ⋙ (shiftFunctor U.PairCategory n ⋙ F.functor) ≅
      U.ι i ⋙ (F.functor ⋙ shiftFunctor W.PairCategory n) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((U.ι i).commShiftIso n).symm F.functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (F.ιCompFunctorIso i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((F.Φ i).commShiftIso n) (W.ι i) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((W.ι i).commShiftIso n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.ιCompFunctorIso i).symm _ ≪≫
    Functor.associator _ _ _

private theorem pairStageShiftIso_hom_app (n : ℤ) (i : I) (X : C i) :
    (pairStageShiftIso F n i).hom.app X =
      F.functor.map (((U.ι i).commShiftIso n).inv.app X) ≫
        (W.ι i).map (((F.Φ i).commShiftIso n).hom.app X) ≫
          ((W.ι i).commShiftIso n).hom.app ((F.Φ i).obj X) := by
  simp [pairStageShiftIso]

variable [∀ {i j : I} (h : i ≤ j), (U.T h).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), (W.T h).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (U.transIso h).hom ℤ]
  [∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (W.transIso h).hom ℤ]

private theorem pairStageShiftIso_comm
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)
    (n : ℤ) {i j : I} (h : i ≤ j) (X : C i) :
    (shiftFunctor U.PairCategory n ⋙ F.functor).map ((U.transIso h).hom.app X) ≫
        (pairStageShiftIso F n i).hom.app X =
      (pairStageShiftIso F n j).hom.app ((U.T h).obj X) ≫
        (F.functor ⋙ shiftFunctor W.PairCategory n).map ((U.transIso h).hom.app X) := by
  have := hβ h
  have hb := NatTrans.shift_app_comm (F.β h).inv n X
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at hb
  have hk :
      (F.Φ j).map (((U.T h).commShiftIso n).inv.app X) ≫
        (F.β h).inv.app (X⟦n⟧) ≫
          (W.T h).map (((F.Φ i).commShiftIso n).hom.app X) ≫
            ((W.T h).commShiftIso n).hom.app ((F.Φ i).obj X) =
      ((F.Φ j).commShiftIso n).hom.app ((U.T h).obj X) ≫
        ((F.β h).inv.app X)⟦n⟧' := by
    erw [← hb]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have ht := (W.transIso h).hom.naturality (((F.Φ i).commShiftIso n).hom.app X)
  dsimp only [Functor.comp_map] at ht
  have hs := NatTrans.shift_app_comm (W.transIso h).hom n ((F.Φ i).obj X)
  have hw := ((W.ι j).commShiftIso n).hom.naturality ((F.β h).inv.app X)
  dsimp only [Functor.comp_map] at hw
  simp only [Functor.comp_map, pairStageShiftIso_hom_app]
  simp only [StageSystem.ι_obj, Functor.comp_obj, StageSystem.Morphism.functor_obj]
  erw [NatTrans.shift_app (U.transIso h).hom n X]
  simp only [Functor.commShiftIso_comp_inv_app, Functor.comp_obj,
    Functor.map_comp, Category.assoc]
  rw [← F.functor.map_comp_assoc (((U.ι i).commShiftIso n).hom.app X)]
  simp only [Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [pairFunctor_transIso, pairFunctor_transIso, F.functor_map_ι]
  simp only [Category.assoc]
  erw [cancel_epi, ← reassoc_of% ht, ← hs]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  erw [hk]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hw]

private def pairShiftIso
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ) (n : ℤ) :
    shiftFunctor U.PairCategory n ⋙ F.functor ≅
      F.functor ⋙ shiftFunctor W.PairCategory n :=
  NatIso.ofComponents (fun X ↦ (pairStageShiftIso F n X.stage).app X.obj)
    (fun f ↦ (pairNatTrans U _ _ (fun i ↦ (pairStageShiftIso F n i).hom)
      (pairStageShiftIso_comm F hβ n)).naturality f)

private theorem pairShiftIso_hom_app
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)
    (n : ℤ) (X : U.PairCategory) :
    (pairShiftIso F hβ n).hom.app X =
      F.functor.map (((U.ι X.stage).commShiftIso n).inv.app X.obj) ≫
        (W.ι X.stage).map (((F.Φ X.stage).commShiftIso n).hom.app X.obj) ≫
          ((W.ι X.stage).commShiftIso n).hom.app ((F.Φ X.stage).obj X.obj) := by
  exact pairStageShiftIso_hom_app F n X.stage X.obj

@[instance_reducible] private def pairCommShift
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ) :
    F.functor.CommShift ℤ where
  commShiftIso := pairShiftIso F hβ
  commShiftIso_zero := by
    ext X
    rw [pairShiftIso_hom_app, Functor.CommShift.isoZero_hom_app]
    simp only [Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
      Functor.CommShift.isoZero_inv_app, Functor.map_comp, F.functor_map_ι, Category.assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    change F.functor.map ((shiftFunctorZero U.PairCategory ℤ).hom.app X) ≫
        (W.ι X.stage).map ((F.Φ X.stage).map (𝟙 X.obj) ≫
          𝟙 ((F.Φ X.stage).obj X.obj)) ≫
        (shiftFunctorZero W.PairCategory ℤ).inv.app (F.functor.obj X) = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp,
      CategoryTheory.Functor.map_id, Category.id_comp]
  commShiftIso_add n m := by
    ext X
    rw [Functor.CommShift.isoAdd_hom_app, pairShiftIso_hom_app F hβ (n + m) X,
      pairShiftIso_hom_app F hβ n X]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (pairShiftIso F hβ m).hom.naturality
      (((U.ι X.stage).commShiftIso n).inv.app X.obj)
    dsimp only [Functor.comp_map, Functor.comp_obj, StageSystem.ι_obj] at hn
    rw [← reassoc_of% hn]
    rw [pairShiftIso_hom_app]
    simp only [Category.assoc]
    have hw := (((W.ι X.stage).commShiftIso m).hom.naturality
      (((F.Φ X.stage).commShiftIso n).hom.app X.obj))
    dsimp only [Functor.comp_map] at hw
    erw [← reassoc_of% hw]
    simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
      Functor.CommShift.isoAdd_inv_app, Functor.map_comp, F.functor_map_ι, Category.assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    congr 2
    dsimp only [Functor.comp_obj]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem pairRestrictionShift
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ) (i : I) :
    letI := pairCommShift F hβ
    NatTrans.CommShift (F.ιCompFunctorIso i).hom ℤ := by
  let _ := pairCommShift F hβ
  constructor
  intro n
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, StageSystem.Morphism.ιCompFunctorIso_hom_app,
    Category.assoc]
  change F.functor.map (((U.ι i).commShiftIso n).hom.app X) ≫
      (pairShiftIso F hβ n).hom.app ⟨i, X⟩ ≫
        (shiftFunctor W.PairCategory n).map (𝟙 (F.functor.obj ⟨i, X⟩)) =
      𝟙 _ ≫ (W.ι i).map (((F.Φ i).commShiftIso n).hom.app X) ≫
        ((W.ι i).commShiftIso n).hom.app ((F.Φ i).obj X)
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp,
    pairShiftIso_hom_app]
  simp only [← F.functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end PairShift

section ShiftRestriction
variable (U : StageSystem C) [∀ i, HasShift (C i) ℤ]
  [HasShift U.PairCategory ℤ] [HasShift D ℤ]
  [∀ i, (U.ι i).CommShift ℤ]
  {J K : U.PairCategory ⥤ D} [J.CommShift ℤ] [K.CommShift ℤ]

private theorem pairNatTrans_shift (τ : J ⟶ K)
    (hτ : ∀ i, NatTrans.CommShift (Functor.whiskerLeft (U.ι i) τ) ℤ) :
    NatTrans.CommShift τ ℤ := by
  constructor
  intro n
  ext X
  have := hτ X.stage
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft (U.ι X.stage) τ) n X.obj
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Category.assoc] at h
  have hn := τ.naturality (((U.ι X.stage).commShiftIso n).hom.app X.obj)
  rw [← reassoc_of% hn] at h
  exact (cancel_epi (J.map (((U.ι X.stage).commShiftIso n).hom.app X.obj))).1 h

end ShiftRestriction

end PairTransformations

private theorem map_conjugate_smul {R C D : Type*} [Semiring R]
    [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear R D] (J : C ⥤ D) [J.Linear R]
    {A B : C} {A' B' : D} (a : A' ⟶ J.obj A) (b : J.obj B ⟶ B')
    (r : R) (f : A ⟶ B) :
    a ≫ J.map (r • f) ≫ b = r • (a ≫ J.map f ≫ b) := by
  rw [J.map_smul, Linear.smul_comp, Linear.comp_smul]

private theorem map_unit_cancel {C D : Type*} [Category C] [Category D]
    (J : C ⥤ D) {A B Z : C} {W : D} (a : W ⟶ J.obj B)
    (b : A ≅ B) (c : B ⟶ Z) :
    (a ≫ J.map b.inv) ≫ J.map (b.hom ≫ c) = a ≫ J.map c := by
  rw [Category.assoc, ← J.map_comp, Iso.inv_hom_id_assoc]

private theorem composite_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (J J' : C ⥤ C) (K K' : D ⥤ D)
    (L L' : E ⥤ E) (hJ : J = J') (hK : K = K') (hL : L = L')
    (uJ : J' ≅ 𝟭 C) (uK : K' ≅ 𝟭 D) (uL : L' ≅ 𝟭 E)
    (bF : F ⋙ K ≅ J ⋙ F) (bG : G ⋙ L ≅ K ⋙ G) (X : C)
    (hF : HEq (bF.hom.app X)
      (uK.hom.app (F.obj X) ≫ F.map (uJ.inv.app X)))
    (hG : HEq (bG.hom.app (F.obj X))
      (uL.hom.app (G.obj (F.obj X)) ≫ G.map (uK.inv.app (F.obj X)))) :
    HEq (bG.hom.app (F.obj X) ≫ G.map (bF.hom.app X))
      (uL.hom.app (G.obj (F.obj X)) ≫ G.map (F.map (uJ.inv.app X))) := by
  cases hJ
  cases hK
  cases hL
  rw [eq_of_heq hF, eq_of_heq hG]
  exact heq_of_eq (map_unit_cancel G _ (uK.app (F.obj X)) _)

private theorem systemComposite_unit
    {I : Type*} [Preorder I]
    {C D E : I → Type*} [∀ i, Category (C i)]
    [∀ i, Category (D i)] [∀ i, Category (E i)]
    {U : StageSystem C} {W : StageSystem D} {Z : StageSystem E}
    (F : U.Morphism W) (G : W.Morphism Z) (i : I)
    (JC : C i ⥤ C i) (JD : D i ⥤ D i) (JE : E i ⥤ E i)
    (hC : U.T (le_refl i) = JC) (hD : W.T (le_refl i) = JD)
    (hE : Z.T (le_refl i) = JE)
    (uC : JC ≅ 𝟭 (C i)) (uD : JD ≅ 𝟭 (D i)) (uE : JE ≅ 𝟭 (E i))
    (X : C i)
    (hF : HEq ((F.β (le_refl i)).hom.app X)
      (uD.hom.app ((F.Φ i).obj X) ≫ (F.Φ i).map (uC.inv.app X)))
    (hG : HEq ((G.β (le_refl i)).hom.app ((F.Φ i).obj X))
      (uE.hom.app ((G.Φ i).obj ((F.Φ i).obj X)) ≫
        (G.Φ i).map (uD.inv.app ((F.Φ i).obj X)))) :
    HEq (((F.comp G).β (le_refl i)).hom.app X)
      (uE.hom.app (((F.comp G).Φ i).obj X) ≫
        ((F.comp G).Φ i).map (uC.inv.app X)) := by
  rw [StageSystem.Morphism.comp_β_hom_app]
  exact composite_unit (F.Φ i) (G.Φ i) _ _ _ _ _ _ hC hD hE uC uD uE
    (F.β (le_refl i)) (G.β (le_refl i)) X hF hG

private theorem framework_shift_obj
    {Y : Scheme.{u}} (n : ℤ) (E : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :
    (shiftFunctor (generalAlgebraicallyClosedConstructibleCategory l Ω Y) n).obj ⟨E, K⟩ =
      (GeneralAlgebraicallyClosedCoefficients.inclusion E :
        GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤ _).obj (K⟦n⟧) :=
  (GeneralAlgebraicallyClosedCoefficients.shift_existsUnique
    (l := l) (Ω := Ω) (Y := Y)).exists.choose_spec.2.1 n ⟨E, K⟩

private theorem framework_inclusion_shift_hom
    {Y : Scheme.{u}} (n : ℤ) (E : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :
    ((GeneralAlgebraicallyClosedCoefficients.inclusion E :
        GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤ _).commShiftIso n).hom.app K =
      eqToHom (framework_shift_obj n E K).symm := by
  have h := (GeneralAlgebraicallyClosedCoefficients.shift_existsUnique
    (l := l) (Ω := Ω) (Y := Y)).exists.choose_spec.2.2.2.choose_spec n E K
  have he := (conj_eqToHom_iff_heq _ _ rfl (framework_shift_obj n E K)).2 h
  simp only [eqToHom_refl, Category.id_comp] at he
  exact he.trans (Category.id_comp _)

private theorem framework_inclusion_shift_inv
    {Y : Scheme.{u}} (n : ℤ) (E : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :
    ((GeneralAlgebraicallyClosedCoefficients.inclusion E :
        GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤ _).commShiftIso n).inv.app K =
      eqToHom (framework_shift_obj n E K) := by
  apply (cancel_epi (((GeneralAlgebraicallyClosedCoefficients.inclusion E :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤ _).commShiftIso n).hom.app K)).1
  rw [Iso.hom_inv_id_app, framework_inclusion_shift_hom]
  simp

@[instance_reducible] private def frameworkCanonicalShift (F : SfFrameworkFamily l Ω T S) :
    F.system.functor.CommShift ℤ :=
  pairCommShift F.system (fun {_ _} h ↦ F.scalar_shift h)

private theorem frameworkCanonicalShift_spec (F : SfFrameworkFamily l Ω T S) :
    letI := frameworkCanonicalShift F
    ∀ (n : ℤ) (E : Padic.FiniteCoefficientFields l Ω)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
      HEq ((F.system.functor.commShiftIso n).hom.app ⟨E, K⟩)
        ((GeneralAlgebraicallyClosedCoefficients.inclusion E :
          GeneralAlgebraicallyClosedCoefficients.Stage l Ω S E ⥤ _).map
            (((F.system.Φ E).commShiftIso n).hom.app K)) := by
  intro n E K
  change HEq ((pairShiftIso F.system (fun {_ _} h ↦ F.scalar_shift h) n).hom.app ⟨E, K⟩) _
  rw [pairShiftIso_hom_app, framework_inclusion_shift_inv,
    framework_inclusion_shift_hom, eqToHom_map]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

private theorem commShift_ext
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {J : C ⥤ D} (s t : J.CommShift ℤ)
    (h : ∀ n : ℤ, Functor.commShiftIso J (self := s) n =
      Functor.commShiftIso J (self := t) n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

private theorem framework_mkHom_add
    {Y : Scheme.{u}} {A B : generalAlgebraicallyClosedConstructibleCategory l Ω Y}
    (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f g : A.toStage hA ⟶ B.toStage hB) :
    StageSystem.PairCategory.mkHom L hA hB (f + g) =
      StageSystem.PairCategory.mkHom L hA hB f +
        StageSystem.PairCategory.mkHom L hA hB g := by
  rw [StageSystem.mkHom_eq_isoToStage hA hB (f + g),
    StageSystem.mkHom_eq_isoToStage hA hB f,
    StageSystem.mkHom_eq_isoToStage hA hB g]
  have := GeneralAlgebraicallyClosedCoefficients.inclusion_additive
    (l := l) (Ω := Ω) (Y := Y) L
  simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

private theorem frameworkFunctor_additive (F : SfFrameworkFamily l Ω T S) :
    F.system.functor.Additive := by
  constructor
  intro A B f g
  obtain ⟨L, _, hA, hB, u, rfl⟩ :=
    StageSystem.PairCategory.exists_le_mkHom_eq f A.stage
  obtain ⟨M, hLM, hA', hB', v, rfl⟩ :=
    StageSystem.PairCategory.exists_le_mkHom_eq g L
  rw [← StageSystem.PairCategory.mkHom_tr hLM u]
  rw [← framework_mkHom_add, F.system.functor_map_mkHom,
    F.system.functor_map_mkHom, F.system.functor_map_mkHom]
  simp only [StageSystem.Morphism.mapAt, Functor.map_add,
    Preadditive.comp_add, Preadditive.add_comp]
  exact framework_mkHom_add M _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
private theorem frameworkFunctor_linear (F : SfFrameworkFamily l Ω T S) :
    F.system.functor.Linear Ω := by
  constructor
  intro A B f α
  rw [(intrinsicQbarLinear_existsUnique l Ω T).exists.choose_spec A B α f,
    (intrinsicQbarLinear_existsUnique l Ω S).exists.choose_spec _ _ α
      (F.system.functor.map f)]
  induction f using StageSystem.PairCategory.hom_induction with
  | h L hA hB f =>
    let N := Padic.finiteCoefficientCompositum l Ω L (StageSystem.qbarScalarField l Ω α)
    let hLN : L ≤ N := ((Padic.finiteCoefficientFields_properties l Ω).1 L
      (StageSystem.qbarScalarField l Ω α)).1
    let hαN : StageSystem.qbarScalarField l Ω α ≤ N :=
      ((Padic.finiteCoefficientFields_properties l Ω).1 L
        (StageSystem.qbarScalarField l Ω α)).2
    have hα : α ∈ N.val := hαN (StageSystem.qbarScalarField_mem l Ω α)
    dsimp only [intrinsicQbarScalarAction]
    rw [StageSystem.qbarScalarHom_mkHom _ _ _ _ α L hA hB f N hLN hα,
      F.system.functor_map_mkHom, F.system.functor_map_mkHom]
    have hs := StageSystem.qbarScalarHom_mkHom l Ω
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω S)
      (intrinsicQbarScalarCompatible l Ω S) α
      (X := F.system.functor.obj A) (Y := F.system.functor.obj B)
      L hA hB (F.system.mapAt f) N hLN hα
    refine Eq.trans ?_ hs.symm
    congr 1
    rw [F.system.tr_mapAt]
    exact map_conjugate_smul (F.system.Φ N)
      ((F.system.β (hA.trans hLN)).hom.app A.obj)
      ((F.system.β (hB.trans hLN)).inv.app B.obj) (⟨α, hα⟩ : N.val) _

set_option linter.unusedVariables false in
/-- The descended shift comparison is uniquely fixed by the finite components.
Source: algebraically closed coefficient paragraph, extracted descent interface
(blueprint: lem-sf-framework-common-stage-descent).

Proof: steps 5--6. Include the finite shift component at the object's own field,
using the multiplication units in the stage inclusion. Expand a shifted arbitrary
representative using both transition shift comparisons. Substitute the scalar
shift square at each endpoint and naturality of the finite shift comparison.
The middle factors cancel, proving naturality on every arrow. Finite zero and
addition shift equations descend at each pair, giving a coherent CommShift.
All objects are stage pairs, so the component formula fixes the structure uniquely. -/
theorem sfFrameworkCommonStageShift_existsUnique (F : SfFrameworkFamily l Ω T S) :
    ∃! c : F.system.functor.CommShift ℤ,
      (fun [commInst : F.system.functor.CommShift ℤ] ↦
        ∀ (n : ℤ) (E : Padic.FiniteCoefficientFields l Ω)
          (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
          HEq ((F.system.functor.commShiftIso n).hom.app ⟨E, K⟩)
            ((GeneralAlgebraicallyClosedCoefficients.inclusion E :
              GeneralAlgebraicallyClosedCoefficients.Stage l Ω S E ⥤ _).map
                (((F.system.Φ E).commShiftIso n).hom.app K))) (commInst := c) := by
  refine ⟨frameworkCanonicalShift F, frameworkCanonicalShift_spec F, ?_⟩
  intro c hc
  apply commShift_ext
  intro n
  apply Iso.ext
  ext A
  exact eq_of_heq ((hc n A.stage A.obj).trans
    ((frameworkCanonicalShift_spec F) n A.stage A.obj).symm)

/-- The specified descended shift, uniquely normalized by the finite-stage comparison.
Source: algebraically closed coefficient paragraph, extracted descent interface
(blueprint: lem-sf-framework-common-stage-descent). -/
noncomputable instance sfFrameworkCommonStageCommShift (F : SfFrameworkFamily l Ω T S) :
    F.system.functor.CommShift ℤ :=
  (sfFrameworkCommonStageShift_existsUnique F).exists.choose

private theorem framework_chosenShift_eq (F : SfFrameworkFamily l Ω T S) :
    sfFrameworkCommonStageCommShift F = frameworkCanonicalShift F := by
  exact (sfFrameworkCommonStageShift_existsUnique F).unique
    (sfFrameworkCommonStageShift_existsUnique F).exists.choose_spec
    (frameworkCanonicalShift_spec F)

private theorem framework_restriction_shift (F : SfFrameworkFamily l Ω T S)
    (E : Padic.FiniteCoefficientFields l Ω) :
    NatTrans.CommShift (F.system.ιCompFunctorIso E).hom ℤ := by
  rw [framework_chosenShift_eq F]
  exact pairRestrictionShift F.system (fun {_ _} h ↦ F.scalar_shift h) E

private theorem frameworkFunctor_exact (F : SfFrameworkFamily l Ω T S) :
    F.system.functor.IsTriangulated := by
  constructor
  intro U hU
  obtain ⟨E, V, hV, ⟨e⟩⟩ :=
    (GeneralAlgebraicallyClosedCoefficients.distinguished_iff U).1 hU
  have := framework_restriction_shift F E
  have : ((GeneralAlgebraicallyClosedCoefficients.inclusion E :
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E ⥤ _) ⋙
        F.system.functor).IsTriangulated :=
    Functor.isTriangulated_of_iso (F.system.ιCompFunctorIso E).symm
  exact isomorphic_distinguished _
    (((GeneralAlgebraicallyClosedCoefficients.inclusion E :
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E ⥤ _) ⋙
        F.system.functor).map_distinguished V hV) _
    (F.system.functor.mapTriangle.mapIso e ≪≫
      (Functor.mapTriangleCompIso
        (GeneralAlgebraicallyClosedCoefficients.inclusion E :
          GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E ⥤ _)
          F.system.functor).symm.app V)

/-- Exact linear framework descent with the prescribed object and representative formulas.
Source: algebraically closed coefficient paragraph, extracted descent interface
(blueprint: lem-sf-framework-common-stage-descent).

Proof: steps 1--7. A common-stage arrow is transported by conjugation with the two
scalar associators. Substitute F.system.coh at its endpoints and use naturality
of beta: mapping transport equals transporting beta-source followed by Phi of
v followed by inverse beta-target. Thus the formula respects eventual equality
and is independent of representatives and overfields. At one common field it
preserves identities, sums and composites by cancelling adjacent beta factors.
For a scalar in Omega enlarge the stage to contain it; finite-stage linearity
proves Omega-linearity. The unit square identifies the restriction to stage E
with Phi_E followed by inclusion. Steps 5--6 give the shift above. A distinguished
triangle is isomorphic to an included distinguished finite triangle. Applying
Phi at that stage preserves the whole triangle, including its connecting arrow;
its inclusion is distinguished, proving exactness. -/
theorem sfFrameworkCommonStageDescent
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p) (F : SfFrameworkFamily l Ω T S) :
    F.system.functor.Additive ∧ F.system.functor.Linear Ω ∧
      F.system.functor.IsTriangulated ∧
      (∀ A : generalAlgebraicallyClosedConstructibleCategory l Ω T,
        F.system.functor.obj A = ⟨A.stage, (F.system.Φ A.stage).obj A.obj⟩) ∧
      (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T)
        (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
        (f : A.toStage hA ⟶ B.toStage hB),
        F.system.functor.map (StageSystem.PairCategory.mkHom L hA hB f) =
          StageSystem.PairCategory.mkHom
            (X := F.system.functor.obj A) (Y := F.system.functor.obj B) L hA hB
            ((F.system.β hA).hom.app A.obj ≫ (F.system.Φ L).map f ≫
              (F.system.β hB).inv.app B.obj)) ∧
      (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T)
        (L M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
        (h : L ≤ M) (f : A.toStage hA ⟶ B.toStage hB),
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω S).tr h (F.system.mapAt f) =
          F.system.mapAt
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).tr h f)) := by
  refine ⟨frameworkFunctor_additive F, frameworkFunctor_linear F, frameworkFunctor_exact F,
    F.system.functor_obj, ?_, ?_⟩
  · intro A B L hA hB f
    exact F.system.functor_map_mkHom hA hB f
  · intro A B L M hA hB h f
    exact F.system.tr_mapAt h f

/-- Compatible transformations descend with their finite components, preserving shifts,
invertibility, identities, vertical composition and equations.
Source: algebraically closed coefficient and Weil-structures paragraphs
(blueprint: lem-sf-framework-common-stage-descent).

Proof: steps 8--9. At (E,K) include tau_E,K. At a larger stage the scalar square
rewrites this component as inverse gamma followed by tau_L followed by beta.
Finite naturality then proves naturality on an arbitrary represented arrow.
The actual descNatTrans has exactly these components. Inclusion preserves
identities and composites, so these and every componentwise equation descend.
For invertibility, rearrange the scalar square for the inverse components;
the inverse family descends and the two composite equations give the inverse.
For shifts include the finite shift square. The unit and transition shift
normalizations identify inclusion of a shifted arrow with the shifted inclusion;
substitution of the specified descended shift components gives the shift square. -/
theorem sfFrameworkCommonStageTransformations
    (F G H : SfFrameworkFamily l Ω T S)
    (τ τ' : StageSystem.Morphism.Hom F.system G.system)
    (η : StageSystem.Morphism.Hom G.system H.system) :
    (∀ A : generalAlgebraicallyClosedConstructibleCategory l Ω T,
      (StageSystem.Morphism.descNatTrans τ).app A =
        (GeneralAlgebraicallyClosedCoefficients.inclusion A.stage :
          GeneralAlgebraicallyClosedCoefficients.Stage l Ω S A.stage ⥤ _).map
            ((τ.τ A.stage).app A.obj)) ∧
      ((∀ E, IsIso (τ.τ E)) → IsIso (StageSystem.Morphism.descNatTrans τ)) ∧
      ((∀ E, NatTrans.CommShift (τ.τ E) ℤ) →
        NatTrans.CommShift (StageSystem.Morphism.descNatTrans τ) ℤ) ∧
      StageSystem.Morphism.descNatTrans (StageSystem.Morphism.Hom.id F.system) =
        𝟙 F.system.functor ∧
      StageSystem.Morphism.descNatTrans (τ.comp η) =
        StageSystem.Morphism.descNatTrans τ ≫ StageSystem.Morphism.descNatTrans η ∧
      ((∀ E, τ.τ E = τ'.τ E) →
        StageSystem.Morphism.descNatTrans τ = StageSystem.Morphism.descNatTrans τ') := by
  refine ⟨StageSystem.Morphism.descNatTrans_app τ,
    StageSystem.Morphism.isIso_descNatTrans τ, ?_,
    StageSystem.Morphism.descNatTrans_id F.system,
    StageSystem.Morphism.descNatTrans_comp τ η, ?_⟩
  · intro hτ
    apply pairNatTrans_shift (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    intro E
    have := hτ E
    have := framework_restriction_shift F E
    have := framework_restriction_shift G E
    have he : Functor.whiskerLeft
        (GeneralAlgebraicallyClosedCoefficients.inclusion E :
          GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E ⥤ _)
        (StageSystem.Morphism.descNatTrans τ) =
      (F.system.ιCompFunctorIso E).hom ≫
        Functor.whiskerRight (τ.τ E)
          (GeneralAlgebraicallyClosedCoefficients.inclusion E :
            GeneralAlgebraicallyClosedCoefficients.Stage l Ω S E ⥤ _) ≫
          (G.system.ιCompFunctorIso E).inv := by
      ext K
      simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
        StageSystem.Morphism.ιCompFunctorIso_hom_app,
        StageSystem.Morphism.ιCompFunctorIso_inv_app, Category.id_comp, Category.comp_id]
      rfl
    rw [he]
    infer_instance
  · intro hτ
    ext A
    exact congrArg
      ((GeneralAlgebraicallyClosedCoefficients.inclusion A.stage :
        GeneralAlgebraicallyClosedCoefficients.Stage l Ω S A.stage ⥤ _).map)
      (congrArg (fun t ↦ t.app A.obj) (hτ A.stage))

/-- The actual composite finite functor has its ordinary composite shift comparison.
Source: algebraically closed coefficient paragraph, composition of families
(blueprint: lem-sf-framework-common-stage-descent). -/
instance sfFrameworkCompositeFiniteShift
    (F : SfFrameworkFamily l Ω T S) (G : SfFrameworkFamily l Ω S V)
    (E : Padic.FiniteCoefficientFields l Ω) :
    ((F.system.comp G.system).Φ E).CommShift ℤ :=
  inferInstanceAs ((F.system.Φ E ⋙ G.system.Φ E).CommShift ℤ)

/-- The composite family has the scalar-shift square and multiplication-unit square.
Its exactness and linearity are the ordinary composite instances at each finite field.
Source: algebraically closed coefficient paragraph, composition of families
(blueprint: lem-sf-framework-common-stage-descent).

Proof: step 10. The comparison is xi at Phi followed by Xi applied to beta.
Substitute the two unit equations. For shifts use the shift square of xi,
naturality of xi on the finite Phi shift comparison, naturality of the Xi
shift comparison on beta, and the shift square of beta. For the tower use
the two original tower equations and naturality of xi on beta; this is
precisely the coherence already in StageSystem.Morphism.comp. -/
theorem sfFrameworkComposite_compatible
    (F : SfFrameworkFamily l Ω T S) (G : SfFrameworkFamily l Ω S V) :
    (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      NatTrans.CommShift ((F.system.comp G.system).β h).hom ℤ) ∧
      sfFrameworkUnitCompatible l Ω T V (F.system.comp G.system) := by
  constructor
  · intro E L h
    exact pairComposite_shift F.system G.system
      (fun {_ _} h ↦ F.scalar_shift h) (fun {_ _} h ↦ G.scalar_shift h) h
  · intro E K
    exact systemComposite_unit F.system G.system E _ _ _
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω T).exists.choose_spec.1
        E E le_rfl)
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω S).exists.choose_spec.1
        E E le_rfl)
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω V).exists.choose_spec.1
        E E le_rfl)
      (GeneralAlgebraicallyClosedCoefficients.unitor l Ω T E)
      (GeneralAlgebraicallyClosedCoefficients.unitor l Ω S E)
      (GeneralAlgebraicallyClosedCoefficients.unitor l Ω V E)
      K (F.unit E K) (G.unit E ((F.system.Φ E).obj K))

/-- Composition of the given families, with the actual whiskered scalar comparisons.
Source: algebraically closed coefficient paragraph, composition of families
(blueprint: lem-sf-framework-common-stage-descent). -/
def SfFrameworkFamily.comp (F : SfFrameworkFamily l Ω T S) (G : SfFrameworkFamily l Ω S V) :
    SfFrameworkFamily l Ω T V where
  system := F.system.comp G.system
  shift E := inferInstanceAs ((F.system.Φ E ⋙ G.system.Φ E).CommShift ℤ)
  additive E := inferInstanceAs ((F.system.Φ E ⋙ G.system.Φ E).Additive)
  linear E := inferInstanceAs ((F.system.Φ E ⋙ G.system.Φ E).Linear E.val)
  exact E := inferInstanceAs ((F.system.Φ E ⋙ G.system.Φ E).IsTriangulated)
  scalar_shift := (sfFrameworkComposite_compatible F G).1
  unit := (sfFrameworkComposite_compatible F G).2

/-- The descended composite uses the normalized shift of the actual composite family.
Source: algebraically closed coefficient paragraph, composition of families
(blueprint: lem-sf-framework-common-stage-descent). -/
instance sfFrameworkCompositePairShift
    (F : SfFrameworkFamily l Ω T S) (G : SfFrameworkFamily l Ω S V) :
    (F.system.comp G.system).functor.CommShift ℤ :=
  sfFrameworkCommonStageCommShift (F.comp G)

set_option backward.isDefEq.respectTransparency.types false in
/-- Descent respects composition, its actual scalar comparisons and its specified shifts.
The comparison is the existing identity-component functorCompIso.
Source: algebraically closed coefficient paragraph, composition of families
(blueprint: lem-sf-framework-common-stage-descent).

Proof: steps 10--11. Expand the two representative formulas. Functoriality of Xi
combines the two inverse target factors and the two source factors into the
whiskered composite comparison delta. This is exactly the representative formula
for the composite family. Both object maps are (E, Xi_E Phi_E K), giving the
canonical identity-component functorCompIso. Include the finite composite shift
chi followed by Xi(phi); these are the shift components on both sides, so this
comparison commutes with shifts. Components of compatible transformations are
finite-stage classes, and hence identify under the same comparison. -/
theorem sfFrameworkCommonStageComposition
    (F : SfFrameworkFamily l Ω T S) (G : SfFrameworkFamily l Ω S V) :
    (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
      HEq (((F.comp G).system.β h).hom.app K)
        ((G.system.β h).hom.app ((F.system.Φ E).obj K) ≫
          (G.system.Φ L).map ((F.system.β h).hom.app K))) ∧
      NatTrans.CommShift (StageSystem.Morphism.functorCompIso F.system G.system).hom ℤ ∧
      (∀ A : generalAlgebraicallyClosedConstructibleCategory l Ω T,
        (StageSystem.Morphism.functorCompIso F.system G.system).hom.app A =
          𝟙 ((G.system.functor).obj (F.system.functor.obj A))) ∧
      (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T) (f : A ⟶ B),
        HEq ((F.comp G).system.functor.map f)
          (G.system.functor.map (F.system.functor.map f))) := by
  refine ⟨?_, ?_, StageSystem.Morphism.functorCompIso_hom_app F.system G.system, ?_⟩
  · intro E L h K
    exact heq_of_eq (StageSystem.Morphism.comp_β_hom_app F.system G.system h K)
  · apply pairNatTrans_shift (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    intro E
    have := framework_restriction_shift F E
    have := framework_restriction_shift G E
    have := framework_restriction_shift (F.comp G) E
    let c :
        (GeneralAlgebraicallyClosedCoefficients.inclusion E :
          GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E ⥤ _) ⋙
            (F.system.comp G.system).functor ≅
        (GeneralAlgebraicallyClosedCoefficients.inclusion E :
          GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E ⥤ _) ⋙
            (F.system.functor ⋙ G.system.functor) :=
      (F.comp G).system.ιCompFunctorIso E ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (G.system.ιCompFunctorIso E).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (F.system.ιCompFunctorIso E).symm _ ≪≫
        Functor.associator _ _ _
    have he : Functor.whiskerLeft
        (GeneralAlgebraicallyClosedCoefficients.inclusion E :
          GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E ⥤ _)
        (StageSystem.Morphism.functorCompIso F.system G.system).hom = c.hom := by
      ext K
      simp only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        StageSystem.Morphism.ιCompFunctorIso_hom_app,
        StageSystem.Morphism.ιCompFunctorIso_inv_app,
        StageSystem.Morphism.functorCompIso_hom_app]
      erw [CategoryTheory.Functor.map_id]
      let Z : generalAlgebraicallyClosedConstructibleCategory l Ω V :=
        ⟨E, (G.system.Φ E).obj ((F.system.Φ E).obj K)⟩
      change 𝟙 Z = 𝟙 Z ≫ 𝟙 Z ≫ 𝟙 Z ≫ 𝟙 Z ≫ 𝟙 Z ≫ 𝟙 Z
      simp only [Category.id_comp]
    rw [he]
    dsimp only [c]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom]
    infer_instance
  · intro A B f
    exact heq_of_eq (StageSystem.Morphism.functor_comp_map F.system G.system f)

end WeilConjectures
