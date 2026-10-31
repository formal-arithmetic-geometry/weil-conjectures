/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.SmoothPurity.Sf.SfRationalLocalizationOrthogonality
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.SmoothPurity.Sf.SfQbarLocalizationExactDescent
import WeilConjectures.SmoothPurity.Sf.SfQbarLocalizationFiniteCoherence
import all WeilConjectures.SmoothPurity.Sf.SfCommonStageDirectImage

/-! # Localization on the raw common-stage coefficient categories

Source: main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, algebraically closed stage
(blueprint: lem-sf-qbar-localization-common-stage).

The records package the asserted descent and its Hom comparison. They introduce
neither another coefficient category nor a Karoubi envelope. The open compactification
is (j,id_X). Closed direct image uses the normalized ordinary direct-image functor
and the adjunction mate of the pullback comparison.

## Main definitions and statement

* `SfQbarLocalizationExactAction`: exactness and shift/unit coherence.
* `SfQbarLocalizationHomComparison`: the explicitly transported cross-stage Hom system.
* `SfQbarLocalizationDescent`: the descended functors, adjunction maps and triangles.
* `sfQbarLocalizationCommonStage`: their existence for complementary immersions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] sfIntegralConstructible FrobeniusExchange.models
  sfRationalTriangulationDatum
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)


variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Exactness and the scalar-unit, scalar-associator and shift equations for one
specified morphism of the existing coefficient systems. The associator equation is
`system.coh`; the displayed unit equation uses the actual scalar multiplication unit.
Source: algebraically closed-stage paragraph, descent of exact functors
(blueprint: lem-sf-qbar-localization-common-stage). -/
structure SfQbarLocalizationExactAction {V W : Scheme.{u}}
    (system : (stageSystem l Ω V).Morphism (stageSystem l Ω W)) where
  finiteShift : ∀ E, (system.Φ E).CommShift ℤ
  finiteAdditive : ∀ E, (system.Φ E).Additive
  finiteExact : ∀ E, letI := finiteShift E; (system.Φ E).IsTriangulated
  shift : system.functor.CommShift ℤ
  additive : system.functor.Additive
  exact : letI := shift; system.functor.IsTriangulated
  beta_shift : ∀ {E L : Index l Ω} (h : E ≤ L),
    letI := finiteShift E
    letI := finiteShift L
    NatTrans.CommShift (system.β h).hom ℤ
  inclusion_shift : ∀ E,
    letI := finiteShift E
    letI := shift
    NatTrans.CommShift (system.ιCompFunctorIso E).hom ℤ
  unit : ∀ (E : Index l Ω) (K : Stage l Ω V E),
    (system.β (le_refl E)).hom.app K ≫
        (system.Φ E).map ((operationStageTransitionIso l Ω V E E le_rfl).hom.app K ≫
          (unitor l Ω V E).hom.app K) =
      (operationStageTransitionIso l Ω W E E le_rfl).hom.app ((system.Φ E).obj K) ≫
        (unitor l Ω W E).hom.app ((system.Φ E).obj K)

private theorem localizationExactAction {V W : Scheme.{u}}
    (F : (stageSystem l Ω V).Morphism (stageSystem l Ω W))
    (h : SfLocalizationFiniteExact l Ω F) :
    ∃ A : SfQbarLocalizationExactAction l Ω F, A.finiteShift = h.shift := by
  obtain ⟨s, a, e, i⟩ := sfLocalizationExactDescent l Ω F h
  exact ⟨{
    finiteShift := h.shift
    finiteAdditive := h.additive
    finiteExact := h.exact
    shift := s
    additive := a
    exact := e
    beta_shift := h.beta_shift
    inclusion_shift := i
    unit := h.unit }, rfl⟩


@[irreducible] private def localizationStageAdjunction
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {C' : I → Type*} [∀ i, Category (C' i)]
    {S : StageSystem C} {T : StageSystem C'}
    (L : S.Morphism T) (R : T.Morphism S) (a : ∀ i, L.Φ i ⊣ R.Φ i)
    (η : StageSystem.Morphism.Hom (StageSystem.Morphism.id S) (L.comp R))
    (ε : StageSystem.Morphism.Hom (R.comp L) (StageSystem.Morphism.id T))
    (hη : ∀ i, η.τ i = (a i).unit) (hε : ∀ i, ε.τ i = (a i).counit) :
    L.functor ⊣ R.functor :=
  descendStageAdjunction L R a η ε hη hε


private theorem localizationStageAdjunction_unit_app
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {C' : I → Type*} [∀ i, Category (C' i)]
    {S : StageSystem C} {T : StageSystem C'}
    (L : S.Morphism T) (R : T.Morphism S) (a : ∀ i, L.Φ i ⊣ R.Φ i)
    (η : StageSystem.Morphism.Hom (StageSystem.Morphism.id S) (L.comp R))
    (ε : StageSystem.Morphism.Hom (R.comp L) (StageSystem.Morphism.id T))
    (hη : ∀ i, η.τ i = (a i).unit) (hε : ∀ i, ε.τ i = (a i).counit)
    (X : S.PairCategory) :
    (localizationStageAdjunction L R a η ε hη hε).unit.app X =
      (S.ι X.stage).map ((a X.stage).unit.app X.obj) := by
  simp only [localizationStageAdjunction, descendStageAdjunction,
    NatTrans.comp_app, StageSystem.Morphism.descNatTrans_app, hη,
    StageSystem.Morphism.functorIdIso_inv_app,
    StageSystem.Morphism.functorCompIso_hom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

private theorem localizationStageAdjunction_counit_app
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {C' : I → Type*} [∀ i, Category (C' i)]
    {S : StageSystem C} {T : StageSystem C'}
    (L : S.Morphism T) (R : T.Morphism S) (a : ∀ i, L.Φ i ⊣ R.Φ i)
    (η : StageSystem.Morphism.Hom (StageSystem.Morphism.id S) (L.comp R))
    (ε : StageSystem.Morphism.Hom (R.comp L) (StageSystem.Morphism.id T))
    (hη : ∀ i, η.τ i = (a i).unit) (hε : ∀ i, ε.τ i = (a i).counit)
    (X : T.PairCategory) :
    (localizationStageAdjunction L R a η ε hη hε).counit.app X =
      (T.ι X.stage).map ((a X.stage).counit.app X.obj) := by
  simp only [localizationStageAdjunction, descendStageAdjunction,
    NatTrans.comp_app, StageSystem.Morphism.descNatTrans_app, hε,
    StageSystem.Morphism.functorIdIso_hom_app,
    StageSystem.Morphism.functorCompIso_inv_app]
  exact (Category.id_comp _).trans (Category.comp_id _)


private theorem localizationRestrictedUnitShift
    {C₀ D₀ C D : Type*} [Category C₀] [Category D₀] [Category C] [Category D]
    [HasShift C₀ ℤ] [HasShift D₀ ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (L₀ : C₀ ⥤ D₀) (R₀ : D₀ ⥤ C₀) (L : C ⥤ D) (R : D ⥤ C)
    [L₀.CommShift ℤ] [R₀.CommShift ℤ] [L.CommShift ℤ] [R.CommShift ℤ]
    (q : C₀ ⥤ C) (r : D₀ ⥤ D) [q.CommShift ℤ] [r.CommShift ℤ]
    (eL : q ⋙ L ≅ L₀ ⋙ r) (eR : r ⋙ R ≅ R₀ ⋙ q)
    [NatTrans.CommShift eL.hom ℤ] [NatTrans.CommShift eR.hom ℤ]
    (a : L₀ ⊣ R₀) [a.CommShift ℤ] (η : 𝟭 C ⟶ L ⋙ R)
    (hη : Functor.whiskerLeft q η =
      q.rightUnitor.hom ≫ q.leftUnitor.inv ≫ Functor.whiskerRight a.unit q ≫
        ((Functor.associator q L R).symm ≪≫
          Functor.isoWhiskerRight eL R ≪≫ Functor.associator L₀ r R ≪≫
          Functor.isoWhiskerLeft L₀ eR ≪≫
          (Functor.associator L₀ R₀ q).symm).inv) :
    NatTrans.CommShift (Functor.whiskerLeft q η) ℤ := by
  rw [hη]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv]
  infer_instance

private theorem localizationUnitShiftDetected
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] (η : F ⟶ G)
    {I : Type*} {B : I → Type*} [∀ i, Category (B i)] [∀ i, HasShift (B i) ℤ]
    (q : ∀ i, B i ⥤ C) [∀ i, (q i).CommShift ℤ]
    (hq : ∀ X : C, ∃ (i : I) (Y : B i), (q i).obj Y = X)
    (hη : ∀ i, NatTrans.CommShift (Functor.whiskerLeft (q i) η) ℤ) :
    NatTrans.CommShift η ℤ := by
  constructor
  intro n
  ext X
  obtain ⟨i, Y, rfl⟩ := hq X
  have := hη i
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft (q i) η) n Y
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  erw [← η.naturality_assoc (((q i).commShiftIso n).hom.app Y)] at h
  exact (cancel_epi (F.map (((q i).commShiftIso n).hom.app Y))).1 h

-- The dependent stage identities require `erw` after simplifying the comparison maps.
set_option linter.flexible false in
private theorem localizationAdjunctionShift {V W : Scheme.{u}}
    (L : (stageSystem l Ω V).Morphism (stageSystem l Ω W))
    (R : (stageSystem l Ω W).Morphism (stageSystem l Ω V))
    (a : ∀ E, L.Φ E ⊣ R.Φ E)
    (η : StageSystem.Morphism.Hom (StageSystem.Morphism.id _) (L.comp R))
    (ε : StageSystem.Morphism.Hom (R.comp L) (StageSystem.Morphism.id _))
    (hη : ∀ E, η.τ E = (a E).unit) (hε : ∀ E, ε.τ E = (a E).counit)
    (EL : SfQbarLocalizationExactAction l Ω L)
    (ER : SfQbarLocalizationExactAction l Ω R)
    (ha : ∀ E, letI := EL.finiteShift E; letI := ER.finiteShift E;
      (a E).CommShift ℤ) :
    let := EL.shift
    let := ER.shift
    (localizationStageAdjunction L R a η ε hη hε).CommShift ℤ := by
  let := EL.shift
  let := ER.shift
  let A := localizationStageAdjunction L R a η ε hη hε
  apply Adjunction.CommShift.mk' A ℤ
  have hi (E : Index l Ω) :
      NatTrans.CommShift (Functor.whiskerLeft (inclusion (Y := V) E) A.unit) ℤ := by
    let := EL.finiteShift E
    let := ER.finiteShift E
    have := ha E
    have := EL.inclusion_shift E
    have := ER.inclusion_shift E
    let q := inclusion (l := l) (Ω := Ω) (Y := V) E
    let δ : q ⋙ (L.functor ⋙ R.functor) ≅ (L.Φ E ⋙ R.Φ E) ⋙ q :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (L.ιCompFunctorIso E) R.functor ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (L.Φ E) (R.ιCompFunctorIso E) ≪≫
        (Functor.associator _ _ _).symm
    have he : Functor.whiskerLeft q A.unit =
        q.rightUnitor.hom ≫ q.leftUnitor.inv ≫
          Functor.whiskerRight (a E).unit q ≫ δ.inv := by
      ext K
      simp [A, localizationStageAdjunction, descendStageAdjunction, δ, q,
        StageSystem.Morphism.descNatTrans_app, hη,
        StageSystem.Morphism.ιCompFunctorIso_inv_app]
      erw [Category.id_comp, Category.comp_id,
        CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
      rfl
    exact localizationRestrictedUnitShift (L.Φ E) (R.Φ E) L.functor R.functor
      q (inclusion (Y := W) E) (L.ιCompFunctorIso E) (R.ιCompFunctorIso E)
      (a E) A.unit he
  exact localizationUnitShiftDetected (𝟭 (Pair l Ω V)) (L.functor ⋙ R.functor)
    A.unit (fun E ↦ inclusion (Y := V) E)
    (fun K ↦ ⟨K.stage, K.obj, rfl⟩) hi


section HomComparison
variable {X U Z : Scheme.{u}}
  (J : (stageSystem l Ω U).Morphism (stageSystem l Ω X))
  (I : (stageSystem l Ω Z).Morphism (stageSystem l Ω X))
  (N : Pair l Ω U) (M : Pair l Ω Z) (m : ℤ)

/-- The literal pair representing j_!N[m], before the inclusion's shift comparison.
Source: displayed cross-stage Hom comparison
(blueprint: lem-sf-qbar-localization-common-stage). -/
def sfQbarLocalizationShiftedPair : Pair l Ω X :=
  ⟨N.stage, ((J.Φ N.stage).obj N.obj)⟦m⟧⟩

/-- Its canonical identification with the shifted common-stage object.
Source: displayed cross-stage Hom comparison
(blueprint: lem-sf-qbar-localization-common-stage). -/
def sfQbarLocalizationShiftedIso :
    sfQbarLocalizationShiftedPair l Ω J N m ≅ (J.functor.obj N)⟦m⟧ :=
  ((inclusion (Y := X) N.stage).commShiftIso m).app ((J.Φ N.stage).obj N.obj)

/-- The common fields contain the original fields of N and M, independently.
Source: displayed cross-stage Hom comparison
(blueprint: lem-sf-qbar-localization-common-stage). -/
abbrev SfQbarLocalizationCommon :=
  Common (sfQbarLocalizationShiftedPair l Ω J N m) (I.functor.obj M)

/-- The operation-shifted Hom group at L, exactly the group in the node's display.
Source: displayed cross-stage Hom comparison
(blueprint: lem-sf-qbar-localization-common-stage). -/
abbrev SfQbarLocalizationStageHom (L : SfQbarLocalizationCommon l Ω J I N M m) :=
  (((J.Φ L.val).obj (N.toStage L.property.1))⟦m⟧ ⟶
    (I.Φ L.val).obj (M.toStage L.property.2))

set_option backward.isDefEq.respectTransparency false in
/-- Scalar shift followed by the prescribed open-operation comparison.
Source: proof step 7, the isomorphism a_L
(blueprint: lem-sf-qbar-localization-common-stage). -/
def sfQbarLocalizationSourceIso (L : SfQbarLocalizationCommon l Ω J I N M m) :
    (sfQbarLocalizationShiftedPair l Ω J N m).toStage L.property.1 ≅
      ((J.Φ L.val).obj (N.toStage L.property.1))⟦m⟧ :=
  ((stageTransition l Ω X N.stage L.val L.property.1).commShiftIso m).app
      ((J.Φ N.stage).obj N.obj) ≪≫
    (shiftFunctor (Stage l Ω X L.val) m).mapIso ((J.β L.property.1).app N.obj)

/-- The prescribed closed-operation scalar comparison b_L.
Source: proof step 7, the isomorphism b_L
(blueprint: lem-sf-qbar-localization-common-stage). -/
def sfQbarLocalizationTargetIso (L : SfQbarLocalizationCommon l Ω J I N M m) :
    (I.functor.obj M).toStage L.property.2 ≅ (I.Φ L.val).obj (M.toStage L.property.2) :=
  (I.β L.property.2).app M.obj

/-- Conjugate a raw stage Hom by a_L inverse and b_L. Both compositions are
Mathlib's additive composition maps, so no new additive structure is chosen.
Source: proof step 7 (blueprint: lem-sf-qbar-localization-common-stage). -/
def sfQbarLocalizationToOperation (L : SfQbarLocalizationCommon l Ω J I N M m) :
    StageHom (sfQbarLocalizationShiftedPair l Ω J N m) (I.functor.obj M) L →+
      SfQbarLocalizationStageHom l Ω J I N M m L :=
  (Preadditive.rightComp _ (sfQbarLocalizationTargetIso l Ω J I N M m L).hom).comp
    (Preadditive.leftComp _ (sfQbarLocalizationSourceIso l Ω J I N M m L).inv)

/-- The inverse conjugation, using the same operation comparisons.
Source: proof step 7 (blueprint: lem-sf-qbar-localization-common-stage). -/
def sfQbarLocalizationToRaw (L : SfQbarLocalizationCommon l Ω J I N M m) :
    SfQbarLocalizationStageHom l Ω J I N M m L →+
      StageHom (sfQbarLocalizationShiftedPair l Ω J N m) (I.functor.obj M) L :=
  (Preadditive.rightComp _ (sfQbarLocalizationTargetIso l Ω J I N M m L).inv).comp
    (Preadditive.leftComp _ (sfQbarLocalizationSourceIso l Ω J I N M m L).hom)

/-- Extend scalars with the scalar associators, conjugating by the canonical
operation and shift comparisons at the two ends. This is the displayed system's
transition, including when neither original field represents the arrow.
Source: proof step 7 (blueprint: lem-sf-qbar-localization-common-stage). -/
def sfQbarLocalizationHomTransition (L P : SfQbarLocalizationCommon l Ω J I N M m)
    (h : L ≤ P) :
    SfQbarLocalizationStageHom l Ω J I N M m L →+
      SfQbarLocalizationStageHom l Ω J I N M m P :=
  (sfQbarLocalizationToOperation l Ω J I N M m P).comp
    ((transportHom (sfQbarLocalizationShiftedPair l Ω J N m) (I.functor.obj M) L P h).comp
      (sfQbarLocalizationToRaw l Ω J I N M m L))

/-- The actual abelian-group direct limit of the displayed operation-shifted groups.
Source: displayed cross-stage Hom comparison
(blueprint: lem-sf-qbar-localization-common-stage). -/
abbrev SfQbarLocalizationHomColimit :=
  AddCommGroup.DirectLimit (SfQbarLocalizationStageHom l Ω J I N M m)
    (sfQbarLocalizationHomTransition l Ω J I N M m)

/-- The comparison is specified on every representative, not just original-field
arrows. All groups in the diagram, its colimit and the common-stage Hom are zero.
Source: displayed comparison and proof steps 7--8
(blueprint: lem-sf-qbar-localization-common-stage). -/
structure SfQbarLocalizationHomComparison where
  system : DirectedSystem (SfQbarLocalizationStageHom l Ω J I N M m)
    (fun {L P} h ↦ sfQbarLocalizationHomTransition l Ω J I N M m L P h)
  coordinates : ((J.functor.obj N)⟦m⟧ ⟶ I.functor.obj M) ≃+
    SfQbarLocalizationHomColimit l Ω J I N M m
  representative (L : SfQbarLocalizationCommon l Ω J I N M m)
      (f : StageHom (sfQbarLocalizationShiftedPair l Ω J N m) (I.functor.obj M) L) :
    coordinates ((sfQbarLocalizationShiftedIso l Ω J N m).inv ≫
      ofHom (sfQbarLocalizationShiftedPair l Ω J N m) (I.functor.obj M)
        L.val L.property.1 L.property.2 f) =
      AddCommGroup.DirectLimit.of (SfQbarLocalizationStageHom l Ω J I N M m)
        (sfQbarLocalizationHomTransition l Ω J I N M m) L
        (sfQbarLocalizationToOperation l Ω J I N M m L f)
  finite_zero : ∀ L : SfQbarLocalizationCommon l Ω J I N M m,
    Subsingleton (SfQbarLocalizationStageHom l Ω J I N M m L)
  colimit_zero : Subsingleton (SfQbarLocalizationHomColimit l Ω J I N M m)
  hom_zero : Subsingleton ((J.functor.obj N)⟦m⟧ ⟶ I.functor.obj M)
private theorem localizationHomComparison
    (hzero : ∀ (E : Index l Ω) (A : Stage l Ω U E) (B : Stage l Ω Z E),
      Subsingleton (((J.Φ E).obj A)⟦m⟧ ⟶ (I.Φ E).obj B)) :
    Nonempty (SfQbarLocalizationHomComparison l Ω J I N M m) := by
  classical
  let A := sfQbarLocalizationShiftedPair l Ω J N m
  let B := I.functor.obj M
  have finiteZero (L : SfQbarLocalizationCommon l Ω J I N M m) :
      Subsingleton (SfQbarLocalizationStageHom l Ω J I N M m L) :=
    hzero L.val (N.toStage L.property.1) (M.toStage L.property.2)
  have rawZero (L : Common A B) : Subsingleton (StageHom A B L) := by
    have := finiteZero L
    exact (Iso.homCongr (sfQbarLocalizationSourceIso l Ω J I N M m L)
      (sfQbarLocalizationTargetIso l Ω J I N M m L)).injective.subsingleton
  have rawHomZero : Subsingleton (A ⟶ B) := by
    have : Subsingleton (ColimitHom A B) := by
      refine ⟨fun x y ↦ ?_⟩
      have hz (z : ColimitHom A B) : z = 0 := by
        induction z using AddCommGroup.DirectLimit.induction_on with
        | _ L f =>
          rw [(rawZero L).elim f 0, map_zero]
          rfl
      exact (hz x).trans (hz y).symm
    exact (homCoordinates A B).injective.subsingleton
  have homZero : Subsingleton ((J.functor.obj N)⟦m⟧ ⟶ I.functor.obj M) := by
    have := rawHomZero
    exact (Iso.homCongr (sfQbarLocalizationShiftedIso l Ω J N m).symm
      (Iso.refl B)).injective.subsingleton
  have colimitZero : Subsingleton (SfQbarLocalizationHomColimit l Ω J I N M m) := by
    have : ∀ L : SfQbarLocalizationCommon l Ω J I N M m,
        Subsingleton (SfQbarLocalizationStageHom l Ω J I N M m L) := finiteZero
    have hz (x : SfQbarLocalizationHomColimit l Ω J I N M m) : x = 0 := by
      induction x using AddCommGroup.DirectLimit.induction_on with
      | _ L f => rw [Subsingleton.elim f 0, map_zero]
    exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  have := homZero
  have := colimitZero
  refine ⟨{
    system := ?_, coordinates := ?_, representative := ?_,
    finite_zero := finiteZero, colimit_zero := colimitZero, hom_zero := homZero }⟩
  · have : ∀ L : SfQbarLocalizationCommon l Ω J I N M m,
        Subsingleton (SfQbarLocalizationStageHom l Ω J I N M m L) := finiteZero
    constructor <;> intros <;> exact Subsingleton.elim _ _
  · exact {
      toFun := fun _ ↦ 0
      invFun := fun _ ↦ 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _
      map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
  · intro L f
    exact Subsingleton.elim _ _

end HomComparison

section Descent
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Z U : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
  (i : Z ⟶ X) (j : U ⟶ X) [i.IsOver (Spec (.of D.k))] [j.IsOver (Spec (.of D.k))]
  [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ z : Z, Invertible (l : Z.residueField z)]
  [∀ t : U, Invertible (l : U.residueField t)]

/-- The precise localization-descent conclusion on the existing raw categories.
The normalized compact-support action at (j,id_X) is extension by zero.
The closed action is ordinary direct image, with scalar comparison fixed as the
adjunction mate of the inverse pullback comparison. Units and counits are compatible
families and the descended maps are their actual finite-stage classes. Each finite
adjunction and shift is pinned to the normalized rational localization package; the
closed action uses that package's ordinary direct image on the nose.
Source: algebraically closed-stage paragraph and proof steps 1--8
(blueprint: lem-sf-qbar-localization-common-stage). -/
structure SfQbarLocalizationDescent where
  finiteLocalization : ∀ E : Index l Ω,
    SfRationalLocalizationOrthogonality l (Coefficient.{u} l Ω E) D i j
  openAction : SfCompactSupportCoefficientAction l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) Ω (Compactification.ofIsOpenImmersion j)
  closedAction : (stageSystem l Ω Z).Morphism (stageSystem l Ω X)
  closedAction_finite : ∀ E, closedAction.Φ E =
    (finiteLocalization E).closedRationalImage
  openPull : (stageSystem l Ω X).Morphism (stageSystem l Ω U)
  closedPull : (stageSystem l Ω X).Morphism (stageSystem l Ω Z)
  openPull_finite : ∀ E, openPull.Φ E = rationalDerivedPullback l (Coefficient.{u} l Ω E) j
  closedPull_finite : ∀ E, closedPull.Φ E = rationalDerivedPullback l (Coefficient.{u} l Ω E) i
  openPull_beta : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    HEq ((openPull.β h).app K) (commonStagePullbackComparison l Ω j ⟨E, K⟩ L h)
  closedPull_beta : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    HEq ((closedPull.β h).app K) (commonStagePullbackComparison l Ω i ⟨E, K⟩ L h)
  openPull_desc : openPull.functor = commonStageDerivedPullback l Ω j
  closedPull_desc : closedPull.functor = commonStageDerivedPullback l Ω i
  openExact : SfQbarLocalizationExactAction l Ω openAction.system
  closedExact : SfQbarLocalizationExactAction l Ω closedAction
  openPullExact : SfQbarLocalizationExactAction l Ω openPull
  closedPullExact : SfQbarLocalizationExactAction l Ω closedPull
  finiteOpenAdjunction : ∀ E, openAction.system.Φ E ⊣ openPull.Φ E
  finiteClosedAdjunction : ∀ E, closedPull.Φ E ⊣ closedAction.Φ E
  finiteOpenAdjunction_normalization : ∀ E,
    HEq (finiteOpenAdjunction E) (finiteLocalization E).openRationalAdjunction
  finiteClosedAdjunction_normalization : ∀ E,
    HEq (finiteClosedAdjunction E) (finiteLocalization E).closedRationalAdjunction
  closedAction_beta : ∀ (E L : Index l Ω) (h : E ≤ L),
    (closedAction.β h).hom =
      (mateEquiv (finiteClosedAdjunction E) (finiteClosedAdjunction L)
        (TwoSquare.mk _ _ _ _ (closedPull.β h).inv)).natTrans
  openShift_finite : ∀ E,
    HEq (openExact.finiteShift E) (finiteLocalization E).openPush.rationalShift
  closedShift_finite : ∀ E,
    HEq (closedExact.finiteShift E) (finiteLocalization E).closedPush.rationalShift
  openPullShift_finite : ∀ E,
    HEq (openPullExact.finiteShift E) (finiteLocalization E).openPull.rationalShift
  closedPullShift_finite : ∀ E,
    HEq (closedPullExact.finiteShift E) (finiteLocalization E).closedPull.rationalShift
  finiteOpenAdjunction_shift : ∀ E,
    letI := openExact.finiteShift E
    letI := openPullExact.finiteShift E
    (finiteOpenAdjunction E).CommShift ℤ
  finiteClosedAdjunction_shift : ∀ E,
    letI := closedPullExact.finiteShift E
    letI := closedExact.finiteShift E
    (finiteClosedAdjunction E).CommShift ℤ
  openUnit : StageSystem.Morphism.Hom (StageSystem.Morphism.id (stageSystem l Ω U))
    (openAction.system.comp openPull)
  openCounit : StageSystem.Morphism.Hom (openPull.comp openAction.system)
    (StageSystem.Morphism.id (stageSystem l Ω X))
  closedUnit : StageSystem.Morphism.Hom (StageSystem.Morphism.id (stageSystem l Ω X))
    (closedPull.comp closedAction)
  closedCounit : StageSystem.Morphism.Hom (closedAction.comp closedPull)
    (StageSystem.Morphism.id (stageSystem l Ω Z))
  openUnit_finite : ∀ E, openUnit.τ E = (finiteOpenAdjunction E).unit
  openCounit_finite : ∀ E, openCounit.τ E = (finiteOpenAdjunction E).counit
  closedUnit_finite : ∀ E, closedUnit.τ E = (finiteClosedAdjunction E).unit
  closedCounit_finite : ∀ E, closedCounit.τ E = (finiteClosedAdjunction E).counit
  openAdjunction : openAction.system.functor ⊣ openPull.functor
  closedAdjunction : closedPull.functor ⊣ closedAction.functor
  openAdjunction_shift :
    letI := openExact.shift
    letI := openPullExact.shift
    openAdjunction.CommShift ℤ
  closedAdjunction_shift :
    letI := closedPullExact.shift
    letI := closedExact.shift
    closedAdjunction.CommShift ℤ
  openUnit_desc : ∀ N : Pair l Ω U, HEq (openAdjunction.unit.app N)
    ((inclusion N.stage).map ((finiteOpenAdjunction N.stage).unit.app N.obj))
  openCounit_desc : ∀ K : Pair l Ω X, HEq (openAdjunction.counit.app K)
    ((inclusion K.stage).map ((finiteOpenAdjunction K.stage).counit.app K.obj))
  closedUnit_desc : ∀ K : Pair l Ω X, HEq (closedAdjunction.unit.app K)
    ((inclusion K.stage).map ((finiteClosedAdjunction K.stage).unit.app K.obj))
  closedCounit_desc : ∀ M : Pair l Ω Z, HEq (closedAdjunction.counit.app M)
    ((inclusion M.stage).map ((finiteClosedAdjunction M.stage).counit.app M.obj))
  triangle_image (E : Index l Ω) (K : Stage l Ω X E)
      (δ : (closedAction.Φ E).obj ((closedPull.Φ E).obj K) ⟶
        ((openAction.system.Φ E).obj ((openPull.Φ E).obj K))⟦(1 : ℤ)⟧)
      (hδ : Triangle.mk ((finiteOpenAdjunction E).counit.app K)
        ((finiteClosedAdjunction E).unit.app K) δ ∈ distTriang (Stage l Ω X E)) :
    Triangle.mk (openAdjunction.counit.app ((inclusion E).obj K))
      (closedAdjunction.unit.app ((inclusion E).obj K))
      ((inclusion E).map δ ≫ ((inclusion E).commShiftIso (1 : ℤ)).hom.app
        ((openAction.system.Φ E).obj ((openPull.Φ E).obj K))) ∈ distTriang (Pair l Ω X)
  objects : ∀ K : Pair l Ω X, ∃ (E : Index l Ω) (KE : Stage l Ω X E),
    K = (inclusion E).obj KE
  homComparison : ∀ (N : Pair l Ω U) (M : Pair l Ω Z) (m : ℤ),
    SfQbarLocalizationHomComparison l Ω openAction.system closedAction N M m

end Descent

private theorem localizationPullbackEquality {V W : Scheme.{u}} (f : V ⟶ W)
    [∀ x : V, Invertible (l : V.residueField x)]
    [∀ y : W, Invertible (l : W.residueField y)]
    (F : (stageSystem l Ω W).Morphism (stageSystem l Ω V))
    (hΦ : ∀ E, F.Φ E = rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
    (hβ : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω W E),
      HEq ((F.β h).app K) (commonStagePullbackComparison l Ω f ⟨E, K⟩ L h)) :
    F.functor = commonStageDerivedPullback l Ω f := by
  apply (commonStageDerivedPullback_existsUnique l Ω f).unique
    (y₁ := F.functor)
  · rcases F with ⟨Φ, β, coh⟩
    have hΦ' : Φ = fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f :=
      funext hΦ
    subst Φ
    constructor
    · intro P
      rfl
    · intro P Q L hP hQ k
      apply heq_of_eq
      change StageSystem.PairCategory.mkHom
        (X := commonStagePullbackObject l Ω f P)
        (Y := commonStagePullbackObject l Ω f Q) L hP hQ
        ((β hP).hom.app P.obj ≫
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).map k ≫
          (β hQ).inv.app Q.obj) = _
      have hp := congrArg Iso.hom (eq_of_heq (hβ P.stage L hP P.obj))
      have hq := congrArg Iso.inv (eq_of_heq (hβ Q.stage L hQ Q.obj))
      dsimp only [Iso.app_hom, Iso.app_inv] at hp hq
      rw [hp, hq]
      rfl
  · exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec

private theorem localizationProofIndexedEq {A B : Sort*} {P : A → Prop}
    (f : (a : A) → P a → B) {a b : A} (h : a = b) (ha : P a) (hb : P b) :
    f a ha = f b hb := by
  subst b
  rfl

private theorem localizationOverEquality {B V W : Scheme.{u}}
    [W.Over B] (f : V ⟶ W) (a b : V.Over B)
    (ha : @Scheme.Hom.IsOver V W f B a inferInstance)
    (hb : @Scheme.Hom.IsOver V W f B b inferInstance) : a = b := by
  cases a with
  | ofHom x =>
    cases b with
    | ofHom y =>
      congr 1
      exact ha.comp_over.symm.trans hb.comp_over

private theorem finiteOrthogonality
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Z U : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of D.k))] [QuasiCompact j]
    (H : SfRationalLocalizationOrthogonality l E D i j)
    (A : sfRationalConstructibleCategory l E U) (B : sfRationalConstructibleCategory l E Z)
    (m : ℤ) :
    Subsingleton (((sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl)
      (Compactification.ofIsOpenImmersion j) E).obj A)⟦m⟧ ⟶
        H.closedRationalImage.obj B) := by
  have hU : H.openOver = (inferInstance : U.Over (Spec (.of D.k))) :=
    localizationOverEquality j _ _ H.openIsOver inferInstance
  let P (a : U.Over (Spec (.of D.k))) : Prop :=
    letI := a
    LocallyOfFiniteType (U ↘ Spec (.of D.k)) ∧
      QuasiCompact (U ↘ Spec (.of D.k)) ∧ j.IsOver (Spec (.of D.k))
  let g (a : U.Over (Spec (.of D.k))) (h : P a) :
      sfRationalConstructibleCategory l E U ⥤ sfRationalConstructibleCategory l E X := by
    letI := a
    let := h.1
    let := h.2.1
    let := h.2.2
    exact sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl)
      (Compactification.ofIsOpenImmersion j) E
  have pa : P H.openOver := ⟨H.openFiniteType, H.openQuasiCompact, H.openIsOver⟩
  have pb : P (inferInstance : U.Over (Spec (.of D.k))) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hg := localizationProofIndexedEq g hU pa pb
  have hh := (H.orthogonality A B m).1
  change Subsingleton (((g _ pa).obj A)⟦m⟧ ⟶ H.closedRationalImage.obj B) at hh
  rw [hg] at hh
  exact hh

private theorem localizationAssemble
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Z U : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    (i : Z ⟶ X) (j : U ⟶ X) [i.IsOver (Spec (.of D.k))] [j.IsOver (Spec (.of D.k))]
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ t : U, Invertible (l : U.residueField t)]
    (F : SfQbarLocalizationFiniteData l Ω D hl i j) :
    Nonempty (SfQbarLocalizationDescent l Ω D hl i j) := by
  classical
  obtain ⟨EO, hEO⟩ := localizationExactAction l Ω F.openAction.system F.openExact
  obtain ⟨EC, hEC⟩ := localizationExactAction l Ω F.closedAction F.closedExact
  obtain ⟨EP, hEP⟩ := localizationExactAction l Ω F.openPull F.openPullExact
  obtain ⟨EQ, hEQ⟩ := localizationExactAction l Ω F.closedPull F.closedPullExact
  let Aopen := localizationStageAdjunction F.openAction.system F.openPull
    F.finiteOpenAdjunction F.openUnit F.openCounit F.openUnit_finite F.openCounit_finite
  let Aclosed := localizationStageAdjunction F.closedPull F.closedAction
    F.finiteClosedAdjunction F.closedUnit F.closedCounit
    F.closedUnit_finite F.closedCounit_finite
  refine ⟨{
    finiteLocalization := F.finiteLocalization, openAction := F.openAction,
    closedAction := F.closedAction, closedAction_finite := F.closedAction_finite,
    openPull := F.openPull, closedPull := F.closedPull,
    openPull_finite := F.openPull_finite, closedPull_finite := F.closedPull_finite,
    openPull_beta := F.openPull_beta, closedPull_beta := F.closedPull_beta,
    openPull_desc := localizationPullbackEquality l Ω j F.openPull
      F.openPull_finite F.openPull_beta,
    closedPull_desc := localizationPullbackEquality l Ω i F.closedPull
      F.closedPull_finite F.closedPull_beta,
    openExact := EO, closedExact := EC, openPullExact := EP, closedPullExact := EQ,
    finiteOpenAdjunction := F.finiteOpenAdjunction,
    finiteClosedAdjunction := F.finiteClosedAdjunction,
    finiteOpenAdjunction_normalization := F.finiteOpenAdjunction_normalization,
    finiteClosedAdjunction_normalization := F.finiteClosedAdjunction_normalization,
    closedAction_beta := F.closedAction_beta,
    openShift_finite := by rw [hEO]; exact F.openShift_finite,
    closedShift_finite := by rw [hEC]; exact F.closedShift_finite,
    openPullShift_finite := by rw [hEP]; exact F.openPullShift_finite,
    closedPullShift_finite := by rw [hEQ]; exact F.closedPullShift_finite,
    finiteOpenAdjunction_shift := by
      rw [hEO, hEP]; exact F.finiteOpenAdjunction_shift,
    finiteClosedAdjunction_shift := by
      rw [hEQ, hEC]; exact F.finiteClosedAdjunction_shift,
    openUnit := F.openUnit, openCounit := F.openCounit,
    closedUnit := F.closedUnit, closedCounit := F.closedCounit,
    openUnit_finite := F.openUnit_finite, openCounit_finite := F.openCounit_finite,
    closedUnit_finite := F.closedUnit_finite, closedCounit_finite := F.closedCounit_finite,
    openAdjunction := Aopen, closedAdjunction := Aclosed,
    openAdjunction_shift := localizationAdjunctionShift l Ω
      F.openAction.system F.openPull F.finiteOpenAdjunction F.openUnit F.openCounit
      F.openUnit_finite F.openCounit_finite EO EP (by
        rw [hEO, hEP]; exact F.finiteOpenAdjunction_shift),
    closedAdjunction_shift := localizationAdjunctionShift l Ω
      F.closedPull F.closedAction F.finiteClosedAdjunction F.closedUnit F.closedCounit
      F.closedUnit_finite F.closedCounit_finite EQ EC (by
        rw [hEQ, hEC]; exact F.finiteClosedAdjunction_shift),
    openUnit_desc := ?_, openCounit_desc := ?_,
    closedUnit_desc := ?_, closedCounit_desc := ?_,
    triangle_image := ?_, objects := ?_, homComparison := ?_ }⟩
  · intro N
    exact heq_of_eq (localizationStageAdjunction_unit_app
      F.openAction.system F.openPull F.finiteOpenAdjunction F.openUnit F.openCounit
      F.openUnit_finite F.openCounit_finite N)
  · intro K
    exact heq_of_eq (localizationStageAdjunction_counit_app
      F.openAction.system F.openPull F.finiteOpenAdjunction F.openUnit F.openCounit
      F.openUnit_finite F.openCounit_finite K)
  · intro K
    exact heq_of_eq (localizationStageAdjunction_unit_app
      F.closedPull F.closedAction F.finiteClosedAdjunction F.closedUnit F.closedCounit
      F.closedUnit_finite F.closedCounit_finite K)
  · intro M
    exact heq_of_eq (localizationStageAdjunction_counit_app
      F.closedPull F.closedAction F.finiteClosedAdjunction F.closedUnit F.closedCounit
      F.closedUnit_finite F.closedCounit_finite M)
  · intro E K δ hδ
    dsimp only [Aopen, Aclosed]
    rw [localizationStageAdjunction_counit_app, localizationStageAdjunction_unit_app]
    exact (inclusion (Y := X) E).map_distinguished _ hδ
  · intro K
    exact ⟨K.stage, K.obj, rfl⟩
  · intro N M m
    apply Nonempty.some
    apply localizationHomComparison l Ω F.openAction.system F.closedAction N M m
    intro E A B
    rw [F.openAction.finite_eq, F.closedAction_finite]
    exact finiteOrthogonality l (Coefficient.{u} l Ω E) D hl i j
      (F.finiteLocalization E) A B m

/-- Residue-field invertibility obtained from the given characteristic hypothesis,
without adding geometric invertibility hypotheses to the localization statement.
Source: the global finite-field datum and the algebraically closed-stage paragraph
(blueprint: lem-sf-qbar-localization-common-stage). -/
@[instance_reducible] def sfQbarLocalizationResidueInvertible
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Scheme.{u}) (t : W ⟶ Spec (.of D.k)) (x : W) :
    Invertible (l : W.residueField x) :=
  let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ t.appTop ≫ W.Γevaluation x).hom
  (Eq.mp (congrArg IsUnit (map_natCast φ l))
    ((PurCompactSupport.coefficientPrimeUnit l D hl).map φ)).invertible

/-- Localization functors, adjunctions and conditional finite-stage triangle completions
 descend to the raw common-stage categories; the cross-stage Hom comparison is the
specified filtered colimit and every group in it vanishes.
Source: main-20261015, prop-sf-open-closed-triangle-all-stages.proof.md,
algebraically closed-stage paragraph (blueprint: lem-sf-qbar-localization-common-stage).

Proof in words, following the node's eight steps:
1. Use lem-sf-rational-localization-triangle-orthogonality at each finite field,
   for the given complementary immersions, to get the actual rational operations,
   their prescribed adjunction maps, exactness and all shifted Hom vanishings.
2. Use lem-fix-operation-reduction for the canonical scalar comparisons, taking
   (j,id_X) for extension by zero. For ordinary closed direct image use the
   adjunction mate of the inverse canonical pullback comparison. Scalar
   extension is exact by lem-weil-scalar-extension-exact-triangulated and its
   associator is lem-weil-scalar-extension-composition. The comparisons preserve
   units and counits. Cochain shifts change both differentials by the same sign,
   so the degree-zero comparisons commute with every integer shift.
3. Normalize repeated coefficients by their scalar unit. Apply
   lem-sbc-coherent-pair-functor-descent on these raw rational stage systems.
   Its map is beta at the source, the finite operation, then beta inverse at the
   target. Tower coherence proves independence of representatives and enlargement.
4. Descend the finite shift comparisons. Their naturality is checked on every
   common-field representative. Every distinguished triangle comes from a finite
   stage up to isomorphism, where each of the four functors is exact.
5. Descend the compatible finite units and counits. Their naturality holds on all
   representatives, and their triangle identities are the corresponding finite
   identities. This gives exactly the two asserted adjunctions and their maps.
6. The exact finite-stage inclusion takes a distinguished completion to a
   distinguished completion of these prescribed maps. Every object is a literal
   pair. Finitely many arrows and equality witnesses admit a common larger field.
7. Conjugate the raw Hom system by the open scalar/shift comparison a_L and
   the closed scalar comparison b_L. Tower coherence intertwines the transitions.
   The existing Hom coordinates give the displayed additive colimit isomorphism,
   specified here on every representative at every common finite overfield.
8. Each displayed finite-stage group is zero by rational localization at L.
   Every colimit element is represented at one such L, hence is zero. The Hom
   comparison gives vanishing even for arrows first represented at a larger field.
No integral lattice for arbitrary rational arrows, Karoubi completion, descent of
X from k to the finite field, or restriction on the sign of the shift is used. -/
theorem sfQbarLocalizationCommonStage
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    letI : Z.Over (Spec (.of D.k)) := ⟨i ≫ X ↘ Spec (.of D.k)⟩
    letI : U.Over (Spec (.of D.k)) := ⟨j ≫ X ↘ Spec (.of D.k)⟩
    letI : i.IsOver (Spec (.of D.k)) := ⟨rfl⟩
    letI : j.IsOver (Spec (.of D.k)) := ⟨rfl⟩
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ Spec (.of D.k))
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
      (X ↘ Spec (.of D.k))
    letI : IsNoetherian X := {}
    letI : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
    letI : TopologicalSpace.NoetherianSpace Z := i.isEmbedding.isInducing.noetherianSpace
    letI : QuasiCompact j := inferInstance
    letI : LocallyOfFiniteType (Z ↘ Spec (.of D.k)) := inferInstanceAs
      (LocallyOfFiniteType (i ≫ X ↘ Spec (.of D.k)))
    letI : QuasiCompact (Z ↘ Spec (.of D.k)) := inferInstance
    letI : LocallyOfFiniteType (U ↘ Spec (.of D.k)) := inferInstanceAs
      (LocallyOfFiniteType (j ≫ X ↘ Spec (.of D.k)))
    letI : QuasiCompact (U ↘ Spec (.of D.k)) := inferInstance
    letI : ∀ x : X, Invertible (l : X.residueField x) :=
      sfQbarLocalizationResidueInvertible l D hl X (X ↘ Spec (.of D.k))
    letI : ∀ z : Z, Invertible (l : Z.residueField z) :=
      sfQbarLocalizationResidueInvertible l D hl Z (Z ↘ Spec (.of D.k))
    letI : ∀ t : U, Invertible (l : U.residueField t) :=
      sfQbarLocalizationResidueInvertible l D hl U (U ↘ Spec (.of D.k))
    Nonempty (SfQbarLocalizationDescent l Ω D hl i j) := by
  classical
  let : Z.Over (Spec (.of D.k)) := ⟨i ≫ X ↘ Spec (.of D.k)⟩
  let : U.Over (Spec (.of D.k)) := ⟨j ≫ X ↘ Spec (.of D.k)⟩
  let : i.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  let : j.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of D.k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of D.k))
  let : AlgebraicGeometry.IsNoetherian X := {}
  let : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  let : TopologicalSpace.NoetherianSpace Z := i.isEmbedding.isInducing.noetherianSpace
  let : QuasiCompact j := inferInstance
  let : LocallyOfFiniteType (Z ↘ Spec (.of D.k)) := inferInstanceAs
    (LocallyOfFiniteType (i ≫ X ↘ Spec (.of D.k)))
  let : QuasiCompact (Z ↘ Spec (.of D.k)) := inferInstance
  let : LocallyOfFiniteType (U ↘ Spec (.of D.k)) := inferInstanceAs
    (LocallyOfFiniteType (j ≫ X ↘ Spec (.of D.k)))
  let : QuasiCompact (U ↘ Spec (.of D.k)) := inferInstance
  let : ∀ x : X, Invertible (l : X.residueField x) :=
    sfQbarLocalizationResidueInvertible l D hl X (X ↘ Spec (.of D.k))
  let : ∀ z : Z, Invertible (l : Z.residueField z) :=
    sfQbarLocalizationResidueInvertible l D hl Z (Z ↘ Spec (.of D.k))
  let : ∀ t : U, Invertible (l : U.residueField t) :=
    sfQbarLocalizationResidueInvertible l D hl U (U ↘ Spec (.of D.k))
  change Nonempty (SfQbarLocalizationDescent l Ω D hl i j)
  obtain ⟨F⟩ := sfQbarLocalizationFiniteCoherence l Ω D hl i j hij
  exact localizationAssemble l Ω D hl i j F
end WeilConjectures
