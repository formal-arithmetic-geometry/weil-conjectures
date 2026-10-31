/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.AlgebraicGeometry.SfConstructibleHeart
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.ConstructibleTruncations
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.SfIntegralStandardTruncations

/-! # Standard cohomology of the specified point realization

Source: Bhatt--Scholze, Propositions 6.8.11(3), 6.8.14 and Section 4.1;
the exact-sections, localization and coherence argument of the DAG
(blueprint: lem-a1-point-realization-standard-cohomology).

The ordinary target is viewed through its full embedding in D(E), and the
common-stage target through its fully faithful realization in D(Ω). Thus its
cohomological classes are the usual classes, without choosing a new target category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w u uC vC uB vB uA vA uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
namespace WeilConjectures

/-- The existing scalar functor with its ambient source and target made explicit.
Source: DAG statement, ordinary target scalar extension
(blueprint: lem-a1-point-realization-standard-cohomology). -/
def pointRealizationFieldTensor {F L : Type u} [Field F] [Field L] (ι : F →+* L) :
    DerivedCategory (ModuleCat.{u} F) ⥤ DerivedCategory (ModuleCat.{u} L) :=
  DerivedCategory.fieldDerivedScalarExtension ι

/-- The canonical truncation comparisons together with exactness and t-exactness.
The equations fix both comparisons by the truncation counit and unit.
Source: the DAG proof, Steps 2--4, using BBD 1.3.3
(blueprint: lem-a1-point-realization-standard-cohomology). -/
structure PointRealizationComparison
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    (t : TStructure C) (s : TStructure B) (F : C ⥤ B) where
  commShift : F.CommShift ℤ
  exact : (fun [_c : F.CommShift ℤ] ↦ F.IsTriangulated) (_c := commShift)
  tExact : F.IsTExact t s
  upper : ∀ j : ℤ, t.truncLE j ⋙ F ≅ F ⋙ s.truncLE j
  lower : ∀ j : ℤ, t.truncGE j ⋙ F ≅ F ⋙ s.truncGE j
  upper_counit : ∀ (j : ℤ) (K : C),
    (upper j).hom.app K ≫ (s.truncLEι j).app (F.obj K) =
      F.map ((t.truncLEι j).app K)
  lower_unit : ∀ (j : ℤ) (K : C),
    F.map ((t.truncGEπ j).app K) ≫ (lower j).hom.app K =
      (s.truncGEπ j).app (F.obj K)

/-- Compose the counit- and unit-characterized comparisons, then commute the shift.
This is the truncation-induced δ, rather than an arbitrary cohomology isomorphism.
Source: DAG proof, Step 4 (blueprint: lem-a1-point-realization-standard-cohomology). -/
def PointRealizationComparison.delta
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    {t : TStructure C} {s : TStructure B} {F : C ⥤ B}
    (P : PointRealizationComparison t s F) (j : ℤ) :
    constructibleTruncationCohomology t j ⋙ F ≅
      F ⋙ constructibleTruncationCohomology s j :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (P.commShift.commShiftIso j) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (P.lower j) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (P.upper j) _ ≪≫ Functor.associator _ _ _) _ ≪≫
    Functor.associator _ _ _

/-- The scalar/cohomology square, with all four specified comparisons and both
standard scalar/cohomology identifications written out.
Source: DAG proof, Step 6 (blueprint: lem-a1-point-realization-standard-cohomology). -/
def PointRealizationCohomologySquare
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A] [HasShift A ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {tC : TStructure C} {tB : TStructure B} {tA : TStructure A} {tD : TStructure D}
    {F : C ⥤ A} {G : B ⥤ D} {T : C ⥤ B} {U : A ⥤ D}
    (PF : PointRealizationComparison tC tA F) (PG : PointRealizationComparison tB tD G)
    (PT : PointRealizationComparison tC tB T) (PU : PointRealizationComparison tA tD U)
    (φ : T ⋙ G ≅ F ⋙ U) : Prop :=
  ∀ (j : ℤ) (K : C),
    G.map ((PT.delta j).hom.app K) ≫ (PG.delta j).hom.app (T.obj K) ≫
        (constructibleTruncationCohomology tD j).map (φ.hom.app K) =
      φ.hom.app ((constructibleTruncationCohomology tC j).obj K) ≫
        U.map ((PF.delta j).hom.app K) ≫ (PU.delta j).hom.app (F.obj K)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded finite point fibre viewed in its ordinary derived category.
Source: DAG statement, finite target (blueprint: lem-a1-point-realization-standard-cohomology). -/
abbrev pointRealizationAmbient :=
  pointRationalFibre D l hl E ⋙ (DerivedCategory.pointFiniteDimensional E).ι

/-- The standard t-structure on the rational source at s = Spec k.
Source: DAG statement, standard classes
(blueprint: lem-a1-point-realization-standard-cohomology). -/
abbrev pointRealizationSourceT :=
  sfRationalStandardTStructure l E (Spec (.of D.k)) D hl

/-- The scalar functor on the recorded rational stages, with the same proof parameter
as the recorded point scalar comparison.
Source: DAG statement, E ⊆ L (blueprint: lem-a1-point-realization-standard-cohomology). -/
abbrev pointRealizationScalar (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) :=
  sfRationalScalarExtension l E (Spec (.of D.k)) 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι

/-- The specified sections-tensor-completion φ, viewed through the full target embedding.
Source: DAG statement, scalar comparison
(blueprint: lem-a1-point-realization-standard-cohomology). -/
def pointRealizationScalarIso (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) :
    pointRealizationScalar D l E L ι ⋙ pointRealizationAmbient D l hl L ≅
      pointRealizationAmbient D l hl E ⋙ pointRealizationFieldTensor ι.toRingHom :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pointRationalFibreScalarIso D l hl E L ι) _ ≪≫
    Functor.associator _ _ _

/-- The usual exact-derived-functor comparisons, normalized to the existing shift
and good truncation maps. Only proof fields remain once these three data are fixed.
Source: DAG proof, Step 2, exact sections and exact coefficient tensor
(blueprint: lem-a1-point-realization-standard-cohomology).
Proof: exactness preserves kernels, images and cokernels, so preserves homology and
both standard halves. Termwise shift and cone commute with an additive exact functor.
The existing truncation comparisons are the factors of the truncation counit and unit.
Their defining equations give the two fields. All data fields are prescribed;
proof irrelevance then gives uniqueness. -/
theorem pointExactDerivedComparison_existsUnique
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ∃! P : PointRealizationComparison DerivedCategory.TStructure.t
        DerivedCategory.TStructure.t F.mapDerivedCategory,
      P.commShift = (inferInstance : F.mapDerivedCategory.CommShift ℤ) ∧
      (∀ j, P.upper j = F.mapDerivedCategoryTruncLEIso j) ∧
      (∀ j, P.lower j = F.mapDerivedCategoryTruncGEIso j) := by
  let P : PointRealizationComparison DerivedCategory.TStructure.t
      DerivedCategory.TStructure.t F.mapDerivedCategory :=
    { commShift := inferInstance
      exact := inferInstance
      tExact :=
        { isLE := fun X n _ ↦ F.isLE_mapDerivedCategory_obj X n
          isGE := fun X n _ ↦ F.isGE_mapDerivedCategory_obj X n }
      upper := F.mapDerivedCategoryTruncLEIso
      lower := F.mapDerivedCategoryTruncGEIso
      upper_counit := fun j K ↦ by
        let : DerivedCategory.TStructure.t.IsLE
            (F.mapDerivedCategory.obj ((DerivedCategory.TStructure.t.truncLE j).obj K)) j :=
          F.isLE_mapDerivedCategory_obj ((DerivedCategory.TStructure.t.truncLE j).obj K) j
        dsimp only [Functor.comp_obj]
        exact DerivedCategory.TStructure.t.liftTruncLE_ι _ _
      lower_unit := fun j K ↦ by
        apply (cancel_mono ((F.mapDerivedCategoryTruncGEIso j).inv.app K)).1
        dsimp only [Functor.comp_obj]
        erw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
        let : DerivedCategory.TStructure.t.IsGE
            (F.mapDerivedCategory.obj ((DerivedCategory.TStructure.t.truncGE j).obj K)) j :=
          F.isGE_mapDerivedCategory_obj ((DerivedCategory.TStructure.t.truncGE j).obj K) j
        exact (DerivedCategory.TStructure.t.π_descTruncGE _ _).symm }
  refine ⟨P, ⟨rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩, ?_⟩
  rintro ⟨c, e, t, upper, lower, hupper, hlower⟩ ⟨hc, hu, hl⟩
  dsimp only at hc hu hl
  cases hc
  have hu' : upper = F.mapDerivedCategoryTruncLEIso := funext hu
  have hl' : lower = F.mapDerivedCategoryTruncGEIso := funext hl
  cases hu'
  cases hl'
  rfl

/-- Canonical exact sections/tensor cohomology comparisons, with real prescribed data.
Source: DAG proof, Step 2 (blueprint: lem-a1-point-realization-standard-cohomology). -/
def pointExactDerivedComparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :=
  (pointExactDerivedComparison_existsUnique F).exists.choose

/-- Compose two already specified cohomology comparisons, including the associators.
Source: DAG proof, Steps 4 and 6
(blueprint: lem-a1-point-realization-standard-cohomology). -/
def pointCompositeCohomologyIso
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A] [HasShift A ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {tC : TStructure C} {tB : TStructure B} {tA : TStructure A}
    {F : C ⥤ B} {G : B ⥤ A}
    (PF : PointRealizationComparison tC tB F) (PG : PointRealizationComparison tB tA G)
    (j : ℤ) : constructibleTruncationCohomology tC j ⋙ (F ⋙ G) ≅
      (F ⋙ G) ⋙ constructibleTruncationCohomology tA j :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (PF.delta j) G ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (PG.delta j) ≪≫
    (Functor.associator _ _ _).symm

/-- The integral standard t-structure induced from the ambient module-sheaf category.
Its construction uses the existing closure under good truncations, without any
identification with inverse limits of levelwise truncations.
Source: DAG proof, Step 1 (blueprint: lem-a1-point-realization-standard-cohomology). -/
def pointRealizationIntegralT :
    TStructure (sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  letI := ObjectProperty.HasInducedTStructure.mk'
    (fun K hK n ↦ (sfIntegralStandardTruncations l E (Spec (.of D.k)) D hl ⟨K, hK⟩).2 n)
  (sfIntegralConstructible l E (Spec (.of D.k))).tStructure DerivedCategory.TStructure.t

/-- The normalization on integral representatives is a natural isomorphism, with
every component fixed to the normalization of the recorded point functor.
Source: DAG proof, Step 4 (blueprint: lem-a1-point-realization-standard-cohomology).
Proof: the size-descent counit and coefficient-down tensor comparison are natural.
The defining pure-tensor formula for the rational fibre restricts to the integral
sections functor on Q. Hence the recorded object normalizations are natural on
integral arrows. Their components are isomorphisms; fixing every component proves
uniqueness by extensionality. -/
theorem pointRealizationIntegralNormalization_existsUnique :
    ∃! e : sfRationalConstructibleLocalization l E (Spec (.of D.k)) ⋙
        pointRealizationAmbient D l hl E ⋙
          (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory ≅
      (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
        pointCompletedDerivedSections D.k l E ⋙ pointModuleDerivedRationalization l E,
      ∀ K, e.app K = pointRationalNormalization D l hl E
        ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K) := by
  classical
  let : HasDerivedCategory.{u} (ModuleCat.{u} E) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} E)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let : (pointFibreSizeLift E).IsEquivalence := pointFibreSizeLift_equivalence E
  let Q := sfRationalConstructibleLocalization l E (Spec (.of D.k))
  let R := pointRationalFibre D l hl E
  let I := pointIntegralRationalFibre D l hl E
  let ho (K) : R.obj (Q.obj K) = I.obj K :=
    (pointRationalFibre_existsUnique D l hl E).exists.choose_spec.1 (Q.obj K)
  let c : Q ⋙ R ≅ I := NatIso.ofComponents (fun K ↦ eqToIso (ho K)) (by
    intro K M f
    apply (DerivedCategory.pointFiniteDimensional E).ι.map_injective
    change (R.map (Q.map f)).hom ≫ (eqToHom (ho M)).hom =
      (eqToHom (ho K)).hom ≫ (I.map f).hom
    have hh := (pointRationalFibre_existsUnique D l hl E).exists.choose_spec.2 K M f 1
    have hh' : HEq (R.map (Q.map f)).hom (I.map f).hom := by
      dsimp only [R, I, Q, pointRationalFibre, sfRationalConstructibleLocalization,
        ScalarLocalization.localization] at hh ⊢
      simpa only [map_one, one_smul] using hh
    simp only [ObjectProperty.eqToHom_hom]
    exact eq_of_heq ((comp_eqToHom_heq _ _).trans
      (hh'.trans (eqToHom_comp_heq _ _).symm)))
  let P := (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).lift
    ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ pointFibreRationalAmbient D l E)
    (fun K ↦ ((pointFibre_sections_mem D l hl E 1 (by decide)).2 K).2)
  let e : sfRationalConstructibleLocalization l E (Spec (.of D.k)) ⋙
      pointRealizationAmbient D l hl E ⋙
        (Functor.mapDerivedCategory.{u, u + 2, u, u + 1, u + 1, u + 2}
          (ModuleCat.uliftFunctor.{u + 1, u} E)) ≅
      (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
        pointCompletedDerivedSections D.k l E ⋙ pointModuleDerivedRationalization l E :=
    Functor.isoWhiskerRight c
        ((DerivedCategory.pointFiniteDimensional E).ι ⋙
          (Functor.mapDerivedCategory.{u, u + 2, u, u + 1, u + 1, u + 2}
          (ModuleCat.uliftFunctor.{u + 1, u} E))) ≪≫
      Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft
        (DerivedCategory.pointFiniteDimensional E).ι (pointFibreLiftDownIso E).symm) ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft P (pointFibreSizeLift E).asEquivalence.counitIso)
        (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).ι)
        (Functor.mapDerivedCategory.{u + 1, u + 2, u + 1, u + 1, u + 2, u + 2}
          (pointFibreCoefficientDown E)) ≪≫
      Functor.isoWhiskerLeft (sfIntegralConstructible l E (Spec (.of D.k))).ι
        (pointFibreRationalDownIso D l E)
  refine ⟨e, ?_, ?_⟩
  · intro K
    rfl
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    exact congrArg Iso.hom (he' K)

/-- The canonical normalization on integral representatives, including the size lift.
Source: DAG statement, integral representative clause
(blueprint: lem-a1-point-realization-standard-cohomology). -/
def pointRealizationIntegralNormalization :=
  (pointRealizationIntegralNormalization_existsUnique D l hl E).exists.choose

variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The existing common-stage fibre, through its fully faithful ordinary realization.
Source: DAG statement, common-stage target
(blueprint: lem-a1-point-realization-standard-cohomology). -/
abbrev pointRealizationCommonAmbient :=
  pointQbarFibre D l hl Ω ⋙ DerivedCategory.pointFdQbarRealization l Ω

/-- The common-stage source's existing standard t-structure.
Source: DAG statement, common-stage halves
(blueprint: lem-a1-point-realization-standard-cohomology). -/
abbrev pointRealizationCommonT :=
  sfCommonStageStandardTStructure l (Spec (.of D.k)) Ω D hl

/-- Finite-stage realization includes the recorded Shrink coefficient equivalence.
Source: DAG proof, Step 8 (blueprint: lem-a1-point-realization-standard-cohomology). -/
def pointRealizationStageAmbient (A : AlgebraicallyClosedCoefficients.Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) A ⥤
      DerivedCategory (ModuleCat.{u} A.val) :=
  pointStageFibre D l hl Ω A ⋙ (DerivedCategory.pointFiniteDimensional A.val).ι

private theorem pointIdentityNormalizedIso_existsUnique
    {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
    (F G : C ⥤ B) (ho : ∀ K, F.obj K = G.obj K)
    (hm : ∀ (K M : C) (f : K ⟶ M), HEq (F.map f) (G.map f)) :
    ∃! e : F ≅ G, ∀ K, HEq (e.hom.app K) (𝟙 (G.obj K)) := by
  let e : F ≅ G := NatIso.ofComponents (fun K ↦ eqToIso (ho K)) (by
    intro K M f
    change F.map f ≫ eqToHom (ho M) = eqToHom (ho K) ≫ G.map f
    exact eq_of_heq ((comp_eqToHom_heq (F.map f) (ho M)).trans
      ((hm K M f).trans (eqToHom_comp_heq (G.map f) (ho K)).symm)))
  have he (K) : HEq (e.hom.app K) (𝟙 (G.obj K)) :=
    eqToHom_heq_id_cod (F.obj K) (G.obj K) (ho K)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((he' K).trans (he K).symm)

private theorem pointMap_heq
    {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
    (H : C ⥤ B) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f g) : HEq (H.map f) (H.map g) := by
  cases hx
  cases hy
  exact heq_of_eq (congrArg H.map (eq_of_heq h))

private theorem pointStageNormalization_generic
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type uC} [∀ i, Category.{vC} (C i)] (S : StageSystem C)
    {V : I → Type uA} [∀ i, Category.{vA} (V i)]
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]
    (F : ∀ i, C i ⥤ V i) (T : ∀ {i j : I}, i ≤ j → (V i ⥤ V j))
    (J : ∀ i, V i ⥤ B)
    (φ : ∀ {i j : I} (h : i ≤ j), S.T h ⋙ F j ≅ F i ⋙ T h)
    (ψ : ∀ {i j : I} (h : i ≤ j), T h ⋙ J j ≅ J i)
    (Q : S.PairCategory ⥤ B) (H : B ⥤ D)
    (ho : ∀ X, Q.obj X = (J X.stage).obj ((F X.stage).obj X.obj))
    (hm : ∀ (X Y : S.PairCategory) (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n)
      (f : X.toStage hX ⟶ Y.toStage hY),
      HEq (Q.map (StageSystem.PairCategory.mkHom n hX hY f))
        ((ψ hX).inv.app ((F X.stage).obj X.obj) ≫
          (J n).map ((φ hX).inv.app X.obj ≫ (F n).map f ≫
            (φ hY).hom.app Y.obj) ≫
          (ψ hY).hom.app ((F Y.stage).obj Y.obj))) (i : I) :
    ∃! e : S.ι i ⋙ Q ⋙ H ≅ (F i ⋙ J i) ⋙ H,
      ∀ K, HEq (e.hom.app K) (𝟙 (((F i ⋙ J i) ⋙ H).obj K)) := by
  apply pointIdentityNormalizedIso_existsUnique
  · intro K
    exact congrArg H.obj (ho ((S.ι i).obj K))
  · intro K M f
    have hh := hm ((S.ι i).obj K) ((S.ι i).obj M) i le_rfl le_rfl
      ((S.T (le_rfl : i ≤ i)).map f)
    have h1 := NatIso.naturality_1 (φ (le_rfl : i ≤ i)) f
    have h2 := NatIso.naturality_1 (ψ (le_rfl : i ≤ i)) ((F i).map f)
    dsimp only [Functor.comp_map] at h1 h2
    dsimp only [StageSystem.ι] at hh
    rw [h1, h2] at hh
    exact pointMap_heq H (ho ((S.ι i).obj K)) (ho ((S.ι i).obj M)) _ _ hh

section StageNormalization

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] pointStageFibre pointStageFibreScalarIso
  pointRationalFibre pointRationalFibreScalarIso DerivedCategory.pointFdQbarStageComp

/-- Restricting the common-stage fibre to one stage gives precisely its finite-stage
fibre followed by scalar extension to Ω. The identity normalization is on actual
realized objects, not a chosen isomorphism of unspecified functors.
Source: DAG proof, Step 8 (blueprint: lem-a1-point-realization-standard-cohomology).
Proof: the recorded Qbar fibre's object formula is the literal pair (A,F_A K).
Its map formula on same-stage representatives is conjugation by the normalized
scalar comparison. Naturality of that comparison cancels its inverse factors;
naturality of the target tensor tower then cancels the remaining conjugation.
After faithful realization these are exactly the scalar-extended finite-stage arrows.
Thus the object identity maps are natural, invertible, and uniquely prescribed. -/
theorem pointRealizationStageNormalization_existsUnique
    (A : AlgebraicallyClosedCoefficients.Index l Ω) :
    ∃! e : GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Spec (.of D.k)) A ⋙
          pointRealizationCommonAmbient D l hl Ω ≅
      pointRealizationStageAmbient D l hl Ω A ⋙
        pointRealizationFieldTensor A.val.subtype,
      ∀ K, HEq (e.hom.app K)
        (𝟙 ((pointRealizationFieldTensor A.val.subtype).obj
          ((pointRealizationStageAmbient D l hl Ω A).obj K))) := by
  apply pointStageNormalization_generic
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k)))
    (pointStageFibre D l hl Ω)
    (fun {_ _} h ↦ DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom)
    (DerivedCategory.pointFdQbarStage l Ω)
    (fun {_ _} h ↦ pointStageFibreScalarIso D l hl Ω _ _ h)
    (fun {_ _} h ↦ DerivedCategory.pointFdQbarStageComp l Ω h)
    (pointQbarFibre D l hl Ω) (DerivedCategory.pointFdQbarRealization l Ω)
  · exact (pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1
  · intro X Y n hX hY f
    exact (pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.2 X Y n hX hY f
end StageNormalization

/-- The normalized finite-stage restriction of the actual common-stage realization.
Source: DAG proof, Step 8 (blueprint: lem-a1-point-realization-standard-cohomology). -/
def pointRealizationStageNormalization (A : AlgebraicallyClosedCoefficients.Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Spec (.of D.k)) A ⋙
          pointRealizationCommonAmbient D l hl Ω ≅
      pointRealizationStageAmbient D l hl Ω A ⋙
        pointRealizationFieldTensor A.val.subtype :=
  (pointRealizationStageNormalization_existsUnique D l hl Ω A).exists.choose

/-- The scalar comparison's identity and tower equations, using the specified
completed-scalar source associator and the termwise tensor associator in the target.
Repeated fields are included.
Source: DAG proof, Step 7 (blueprint: lem-a1-point-realization-standard-cohomology). -/
def PointRealizationScalarCoherence : Prop :=
  (∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (K : sfRationalConstructibleCategory l F (Spec (.of D.k))),
    (pointRealizationScalarIso D l hl F F (AlgHom.id (Padic l) F)).hom.app K ≫
        (DerivedCategory.fieldScalarUnit F).hom.app
          ((pointRealizationAmbient D l hl F).obj K) =
      (pointRealizationAmbient D l hl F).map
        ((sfRationalScalarUnit l F (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K)) ∧
  ∀ (F L M : Type u) [Field F] [Field L] [Field M]
    [Algebra (Padic l) F] [Algebra (Padic l) L] [Algebra (Padic l) M]
    [FiniteDimensional (Padic l) F] [FiniteDimensional (Padic l) L]
    [FiniteDimensional (Padic l) M]
    (ι : F →ₐ[Padic l] L) (κ : L →ₐ[Padic l] M)
    (K : sfRationalConstructibleCategory l F (Spec (.of D.k))),
    (pointRealizationAmbient D l hl M).map
        ((sfRationalScalarComp l F L ι (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ).hom.app K) ≫
        (pointRealizationScalarIso D l hl F M (κ.comp ι)).hom.app K =
      (pointRealizationScalarIso D l hl L M κ).hom.app
          ((pointRealizationScalar D l F L ι).obj K) ≫
        (pointRealizationFieldTensor κ.toRingHom).map
          ((pointRealizationScalarIso D l hl F L ι).hom.app K) ≫
        (DerivedCategory.fieldScalarTower ι.toRingHom κ.toRingHom).hom.app
          ((pointRealizationAmbient D l hl F).obj K)

/-- The complete system of standard point-realization comparisons. Data fields are
maps with their canonical normalization; no choice is made from this structure.
The final existence theorem supplies exactly the clauses of the node.
Source: Bhatt--Scholze 6.8.11(3), 6.8.14 and the DAG proof, Steps 1--8
(blueprint: lem-a1-point-realization-standard-cohomology). -/
structure PointRealizationFiniteCohomologyData where
  finite : ∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F],
    PointRealizationComparison (pointRealizationSourceT D l hl F)
      DerivedCategory.TStructure.t (pointRealizationAmbient D l hl F)
  scalar : ∀ (F L : Type u) [Field F] [Field L]
    [Algebra (Padic l) F] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) F] [FiniteDimensional (Padic l) L]
    (ι : F →ₐ[Padic l] L),
    PointRealizationComparison (pointRealizationSourceT D l hl F)
      (pointRealizationSourceT D l hl L) (pointRealizationScalar D l F L ι)
  scalar_shift : ∀ (F L : Type u) [Field F] [Field L]
    [Algebra (Padic l) F] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) F] [FiniteDimensional (Padic l) L]
    (ι : F →ₐ[Padic l] L) (K : sfRationalConstructibleCategory l F (Spec (.of D.k))),
    HEq (((scalar F L ι).commShift.commShiftIso (1 : ℤ)).hom.app K)
      ((sfRationalConstructibleLocalization l L (Spec (.of D.k))).map
        (((GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique
          l F L ι (Spec (.of D.k))).exists.choose.commShiftIso (1 : ℤ)).hom.app K.obj))
  scalar_square : ∀ (F L : Type u) [Field F] [Field L]
    [Algebra (Padic l) F] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) F] [FiniteDimensional (Padic l) L]
    (ι : F →ₐ[Padic l] L),
    PointRealizationCohomologySquare (finite F) (finite L) (scalar F L ι)
      (pointExactDerivedComparison (ModuleCat.extendScalars.{u, u, u} ι.toRingHom))
      (pointRealizationScalarIso D l hl F L ι)
  scalar_coherence : PointRealizationScalarCoherence D l hl
  integral : ∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F],
    PointRealizationComparison (pointRealizationIntegralT D l hl F)
      DerivedCategory.TStructure.t (sfIntegralConstructible l F (Spec (.of D.k))).ι
  integral_shift : ∀ (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F],
    (integral F).commShift =
      (inferInstance : (sfIntegralConstructible l F (Spec (.of D.k))).ι.CommShift ℤ)
  localization : ∀ (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F],
    PointRealizationComparison (pointRealizationIntegralT D l hl F)
      (pointRealizationSourceT D l hl F)
      (sfRationalConstructibleLocalization l F (Spec (.of D.k)))
  localization_shift : ∀ (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F],
    (localization F).commShift = (inferInstance :
      (sfRationalConstructibleLocalization l F (Spec (.of D.k))).CommShift ℤ)
  integral_normalization : ∀ (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] (j : ℤ)
    (K : sfIntegralConstructibleCategory l F (Spec (.of D.k))),
    (pointRealizationAmbient D l hl F ⋙
        (ModuleCat.uliftFunctor.{u + 1, u} F).mapDerivedCategory).map
          (((localization F).delta j).hom.app K) ≫
        (pointCompositeCohomologyIso (finite F)
          (pointExactDerivedComparison (ModuleCat.uliftFunctor.{u + 1, u} F)) j).hom.app
            ((sfRationalConstructibleLocalization l F (Spec (.of D.k))).obj K) ≫
        (constructibleTruncationCohomology DerivedCategory.TStructure.t j).map
          ((pointRealizationIntegralNormalization D l hl F).hom.app K) =
      (pointRealizationIntegralNormalization D l hl F).hom.app
          ((constructibleTruncationCohomology (pointRealizationIntegralT D l hl F) j).obj K) ≫
        (pointCompletedDerivedSections D.k l F ⋙ pointModuleDerivedRationalization l F).map
          (((integral F).delta j).hom.app K) ≫
        (pointCompositeCohomologyIso
          (pointExactDerivedComparison (pointCompletedSections D.k l F))
          (pointExactDerivedComparison (pointModuleRationalization l F)) j).hom.app K.obj
  heart : ∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (K : sfRationalConstructibleCategory l F (Spec (.of D.k))),
    (pointRealizationSourceT D l hl F).heart K → ∀ j : ℤ, j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} F) j).obj
        ((pointRealizationAmbient D l hl F).obj K))

/-- Exact scalar extension on module complexes with the target sizes fixed explicitly.
Source: DAG proof, Steps 2 and 6 (blueprint: lem-a1-point-realization-standard-cohomology). -/
def pointFieldComparison {F L : Type u} [Field F] [Field L] (ι : F →+* L) :
    PointRealizationComparison
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} F))
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} L))
      (pointRealizationFieldTensor ι) :=
  pointExactDerivedComparison (ModuleCat.extendScalars.{u, u, u} ι)

/-- Tensor with Ω on ordinary complexes with the finite subfield specified.
Source: DAG proof, Step 8 (blueprint: lem-a1-point-realization-standard-cohomology). -/
def pointStageTargetComparison (A : AlgebraicallyClosedCoefficients.Index l Ω) :
    PointRealizationComparison
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} A.val))
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω))
      (pointRealizationFieldTensor (F := A.val) (L := Ω) A.val.subtype) :=
  pointFieldComparison (F := A.val) (L := Ω) A.val.subtype

/-- The finite-stage representative equation for the common-stage δ.
The formula is stated separately to keep elaboration of the data package small.
Source: DAG proof, Step 8 (blueprint: lem-a1-point-realization-standard-cohomology). -/
def PointRealizationCommonSquare (A : AlgebraicallyClosedCoefficients.Index l Ω)
    (Pstage : PointRealizationComparison
      (pointRealizationSourceT D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A))
      DerivedCategory.TStructure.t (pointRealizationStageAmbient D l hl Ω A))
    (Pcommon : PointRealizationComparison (pointRealizationCommonT D l hl Ω)
      DerivedCategory.TStructure.t (pointRealizationCommonAmbient D l hl Ω))
    (Pincl : PointRealizationComparison
      (pointRealizationSourceT D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A))
      (pointRealizationCommonT D l hl Ω)
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Spec (.of D.k)) A)) : Prop :=
  ∀ φ : GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Spec (.of D.k)) A ⋙
          pointRealizationCommonAmbient D l hl Ω ≅
      pointRealizationStageAmbient D l hl Ω A ⋙ pointRealizationFieldTensor A.val.subtype,
    (∀ K, HEq (φ.hom.app K)
      (𝟙 ((pointRealizationFieldTensor A.val.subtype).obj
        ((pointRealizationStageAmbient D l hl Ω A).obj K)))) →
    PointRealizationCohomologySquare
      (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) A)
      (B := generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
      (A := DerivedCategory (ModuleCat.{u} A.val))
      (D := DerivedCategory (ModuleCat.{u} Ω))
      (tC := pointRealizationSourceT D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A))
      (tB := pointRealizationCommonT D l hl Ω)
      (tA := DerivedCategory.TStructure.t (C := ModuleCat.{u} A.val))
      (tD := DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω))
      (F := pointRealizationStageAmbient D l hl Ω A)
      (G := pointRealizationCommonAmbient D l hl Ω)
      (T := GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Spec (.of D.k)) A)
      (U := pointRealizationFieldTensor A.val.subtype)
      Pstage Pcommon Pincl
        (pointStageTargetComparison l Ω A) φ

/-- The common-stage continuation of the finite, normalized cohomology system.
Source: DAG proof, Step 8 (blueprint: lem-a1-point-realization-standard-cohomology). -/
structure PointRealizationStandardCohomologyData extends
    PointRealizationFiniteCohomologyData D l hl where
  common : PointRealizationComparison (pointRealizationCommonT D l hl Ω)
    DerivedCategory.TStructure.t (pointRealizationCommonAmbient D l hl Ω)
  stage : ∀ A : AlgebraicallyClosedCoefficients.Index l Ω,
    PointRealizationComparison
      (pointRealizationSourceT D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A))
      DerivedCategory.TStructure.t (pointRealizationStageAmbient D l hl Ω A)
  stage_transport : ∀ (A : AlgebraicallyClosedCoefficients.Index l Ω) (j : ℤ),
    (stage A).delta j = pointCompositeCohomologyIso
      (finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A))
      (pointExactDerivedComparison
        (ModuleCat.extendScalars.{u, u, u} (Shrink.algEquiv.{u} (Padic l) A.val).toRingHom)) j
  inclusion : ∀ A : AlgebraicallyClosedCoefficients.Index l Ω,
    PointRealizationComparison
      (pointRealizationSourceT D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A))
      (pointRealizationCommonT D l hl Ω)
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Spec (.of D.k)) A)
  inclusion_shift : ∀ A : AlgebraicallyClosedCoefficients.Index l Ω,
    (inclusion A).commShift = (inferInstance :
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Spec (.of D.k)) A).CommShift ℤ)
  common_square : ∀ A : AlgebraicallyClosedCoefficients.Index l Ω,
    PointRealizationCommonSquare D l hl Ω A (stage A) common (inclusion A)
  common_heart : ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)),
    (pointRealizationCommonT D l hl Ω).heart K → ∀ j : ℤ, j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Ω) j).obj
        ((pointRealizationCommonAmbient D l hl Ω).obj K))

/-- The specified point realization is exact and t-exact, its truncation-induced
cohomology isomorphisms have the integral normalization, and the scalar squares
commute with identity, towers and passage to every common finite stage.
Source: Bhatt--Scholze, Propositions 6.8.11(3), 6.8.14, Section 4.1, with the
exact-sections/localization coherence argument in the DAG
(blueprint: lem-a1-point-realization-standard-cohomology).

Proof plan (the node's eight steps):
1. Spec k is noetherian of dimension zero and l is invertible. The integral
   stratified-perfect characterization identifies the integral category with that
   in the integral t-structure theorem. Good truncations restrict, and localization
   supplies the rational standard pair with its canonical truncation comparisons.
2. Point pro-etale sections are exact. Fraction-field tensor is exact, hence the
   exact-functor homology comparison identifies H^j with sections of H^j tensored
   with E. Tensor commutes with shifts and cones. Extending maps f/pi^n by
   pi^(-n) times their image gives the specified exact rational point fibre.
3. An object in either rational half has an integral representative in that half.
   Exact sections and tensor preserve its cohomology vanishing; this proves
   t-exactness at every integer bound, including the zero object.
4. The t-exact truncation comparison theorem supplies the unique counit- and
   unit-characterized upper/lower comparisons. Compose them with shift to give δ.
   Its composition assertion for Q and the point functor identifies δ on QK with
   the exact cycle/quotient comparison for sections followed by tensor. The
   integral_normalization equation records this with the actual size-lift counit.
   T-exactness sends every heart object to degree-zero cohomology.
5. Use precisely the scalar comparison built from the inverse completed-sections
   comparison, sections-tensor and the rational tensor beta. Naturality extends
   from integral maps to fractions. Completed scalar, sections tensor and beta
   commute with shifts, so this φ commutes with the specified shift structures.
6. Both scalar functors are t-exact. Naturality of the canonical truncation
   comparisons with respect to φ gives the scalar square. Compose its two
   truncation equations and the shift equation to obtain scalar_square for δ.
7. The point-sections scalar theorem gives the identity and tower equations of φ;
   rationalization retains them. Paste the two squares for L/E and M/L, and use
   these equations and the termwise tensor associator. Applying cohomology to the
   same tower equation proves identity normalization and composition of squares.
8. A common-stage triangle and each half have a finite-stage representative.
   The recorded point functor acts on arrows by φ conjugation. Exactness and
   t-exactness therefore descend. At each finite stage use δ already constructed;
   scalar_square and its tower equation make the maps and their inverses agree
   after every enlargement. Common-stage arrow naturality follows at a common
   field. The common_square equation records that descent through the faithful
   realization, and common_heart gives its degree-zero consequence. -/
theorem pointRealizationStandardCohomology :
    Nonempty (PointRealizationStandardCohomologyData D l hl Ω) := by
  sorry

end WeilConjectures
