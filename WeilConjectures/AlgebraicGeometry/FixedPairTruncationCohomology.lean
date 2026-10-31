/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedPairTruncationCohomologyCore
public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.SfCommonStageWeilCohomology
public import WeilConjectures.AlgebraicGeometry.ConstructibleTruncations
public import WeilConjectures.AlgebraicGeometry.IntegralPullbackCompletedComparison
public import WeilConjectures.SixFunctors.FrobeniusPointTransportNatural
public import WeilConjectures.AlgebraicGeometry.CoefficientCohomologyModules
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
import WeilConjectures.AlgebraicGeometry.AutomorphismConstructibleStageEquivalence
import WeilConjectures.AlgebraicGeometry.FieldWeilShriekShiftData
import WeilConjectures.AlgebraicGeometry.IsomorphismFieldTransport
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Truncations, triangles and cohomology of rational Weil pairs

Source: blueprint main-20261015, sec-poincare-duality/sk-lem-finite,
prop-weil-operations.proof.md, sentence 2 and the final cohomology assertion;
BBD, Proposition 1.3.3 and paragraph 1.3.4, printed pp. 29--30
(blueprint: lem-pod-fixed-pair-truncation-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v uC vC
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence HasDerivedCategory.standard
  Scheme.residueField
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Aut

attribute [local irreducible] FixedPairTruncationCohomologySpec
  FixedPairRationalShiftNormalization FixedPairCommonShiftNormalization

private theorem fixedPair_shift_square_of_heq
    {C : Type*} [Category C] {A B C₁ D E F : C}
    (f : A ⟶ B) (g : E ⟶ F) (p : B = C₁) (q : C₁ = F)
    (r : A = D) (s : D = E) (h : HEq f g) :
    f ≫ eqToHom p ≫ eqToHom q = eqToHom r ≫ eqToHom s ≫ g := by
  cases p
  cases q
  cases r
  cases s
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using eq_of_heq h

private theorem fixedPair_shift_square_of_components
    {C : Type*} [Category C] (S P : C ⥤ C) {A B U V W Z : C}
    (f : A ⟶ B) (a : B ⟶ S.obj U) (b : U ⟶ V)
    (c : A ⟶ P.obj W) (d : W ⟶ Z) (g : P.obj Z ⟶ S.obj V)
    {ha : B = S.obj U} {hb : U = V} {hc : A = P.obj W} {hd : W = Z}
    (ea : a = eqToHom ha) (eb : b = eqToHom hb)
    (ec : c = eqToHom hc) (ed : d = eqToHom hd) (h : HEq f g) :
    f ≫ a ≫ S.map b = c ≫ P.map d ≫ g := by
  rw [ea, eb, ec, ed, eqToHom_map, eqToHom_map]
  exact fixedPair_shift_square_of_heq _ _ _ _ _ _ h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem fixedPairTruncationCohomologySpec_of_tExact
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (t : TStructure C) (P : C ⥤ C) [P.CommShift ℤ]
    [P.IsTriangulated] [P.IsTExact t t] : FixedPairTruncationCohomologySpec t P := by
  unfold FixedPairTruncationCohomologySpec
  let cLE (m : ℤ) : t.truncLE m ⋙ P ≅ P ⋙ t.truncLE m :=
    P.eTruncLTIso t t (m + 1 : ℤ)
  let cGE (m : ℤ) : t.truncGE m ⋙ P ≅ P ⋙ t.truncGE m := P.eTruncGEIso t t m
  refine ⟨cLE, cGE, ?_, ?_, ?_, ?_⟩
  · intro m K
    exact ⟨P.eTruncLTIsoApp_hom_eTruncLTι_app t t (m + 1 : ℤ) K,
      P.eTruncGEπ_app_eTruncGEIsoApp_hom t t m K⟩
  · intro m
    exact ⟨rfl, rfl⟩
  · intro m K
    simp only [IsoAlgebra.mapOfNatIso_obj_str, Iso.trans_hom, Functor.mapIso_hom]
    constructor
    · rw [Category.assoc, (t.truncLEι m).naturality, Functor.id_map,
        ← Category.assoc]
      exact congrArg (fun z ↦ z ≫ K.str.hom)
        (P.eTruncLTIsoApp_hom_eTruncLTι_app t t (m + 1 : ℤ) K.carrier)
    · constructor
      · rw [← Category.assoc]
        erw [P.eTruncGEπ_app_eTruncGEIsoApp_hom t t m K.carrier]
        erw [TStructure.eTruncGEπ_coe]
        simpa only [Functor.id_map] using (t.truncGEπ m).naturality K.str.hom
      · change ((cGE (m + 1)).hom.app K.carrier ≫
            (t.truncGE (m + 1)).map K.str.hom) ≫
              (t.truncGEδLE m (m + 1) rfl).app K.carrier = _
        rw [Category.assoc, (t.truncGEδLE m (m + 1) rfl).naturality]
        simp only [Functor.comp_map]
        have hδ := P.eTruncGEδLT_comm t t (m + 1 : ℤ) K.carrier
        have hd : (t.truncGEδLE m (m + 1) rfl) = t.truncGEδLT (m + 1) := by
          ext X
          dsimp [TStructure.truncGEδLE, TStructure.truncLEIsoTruncLT,
            TStructure.truncLE]
          simp only [CategoryTheory.Functor.map_id, Category.comp_id]
        rw [hd, ← Category.assoc]
        erw [← hδ]
        simp only [Functor.map_comp, Category.assoc]
        rfl
  · intro i
    let H := (IsoAlgebra.mapOfNatIso (cLE i) ⋙ IsoAlgebra.mapOfNatIso (cGE i)) ⋙
      IsoAlgebra.mapOfNatIso (P.commShiftIso i)
    refine ⟨H, rfl, rfl, fun K ↦ ?_⟩
    change t.heart (((t.truncGELE i i).obj K.carrier)⟦i⟧)
    have := t.isLE_shift ((t.truncGELE i i).obj K.carrier) i i 0 (by omega)
    have := t.isGE_shift ((t.truncGELE i i).obj K.carrier) i i 0 (by omega)
    exact ⟨t.le_of_isLE _ _, t.ge_of_isGE _ _⟩



private theorem rationalClass_pullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : IsomorphismFieldTransportStage l E g hX hY)
    (b : Bool) (n : ℤ) (K : sfRationalConstructibleCategory l E Y)
    (hK : sfRationalStandardClass l E Y b n K) :
    sfRationalStandardClass l E X b n ((rationalDerivedPullback l E g).obj K) := by
  have := S.moduleAdditive
  have := S.moduleLimits
  have := S.moduleColimits
  obtain ⟨M, hM, ⟨e⟩⟩ := hK
  refine ⟨(constructibleIntegralPullback l E g).obj M, ?_,
    ⟨(rationalDerivedPullback l E g).mapIso e ≪≫
      eqToIso ((rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 _)⟩⟩
  intro i hi
  let G := AlgebraicGeometry.ProEtale.inverseImageIntegralModules l E g
  have hz := G.isZero_homologyFunctor_mapDerivedCategory_obj (hM i hi)
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (S.lambda.app M))


variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι in
private theorem fixedPairRationalShiftNormalization_of_roos
    (s : (sfWeilFrobeniusPullback D l hl Y₀ E).CommShift ℤ)
    (hs : letI := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
      automorphismStageRationalShiftNormalization l E (D.geometricFrobenius Y₀).hom s) :
    FixedPairRationalShiftNormalization D l hl Y₀ E s := by
  unfold FixedPairRationalShiftNormalization
  let := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  obtain ⟨c⟩ := IntegralCompletedComparison.integralPullback_completedComparison l E
    (D.geometricFrobenius Y₀).hom
    (automorphismConstructibleStage_units D l hl (D.geometricFiber Y₀)).1
    (automorphismConstructibleStage_units D l hl (D.geometricFiber Y₀)).1
  obtain ⟨d, ⟨a, b, ha, hb, hd⟩, hs⟩ := hs
  have hbc : b = c.derivedShift := (fieldIntegralPullShift_existsUnique l E
    (D.geometricFrobenius Y₀).hom).unique ⟨a, ha, hb⟩
      ⟨c.chainShift, c.chainShift_coordinates, c.derivedShift_descent⟩
  subst b
  let : (constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).CommShift ℤ := d
  let : (integralDerivedPullback l E (D.geometricFrobenius Y₀).hom).CommShift ℤ := c.derivedShift
  refine ⟨c, d, ?_, ?_⟩
  · intro K r
    have h := hd K r
    let ι := (sfIntegralConstructible l E (D.geometricFiber Y₀).left).ι
    have hι (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :
        (ι.commShiftIso r).hom.app M = 𝟙 _ := rfl
    dsimp only [ι] at hι
    rw [hι, hι]
    change ((Functor.commShiftIso (constructibleIntegralPullback l E
      (D.geometricFrobenius Y₀).hom) r).hom.app K).hom ≫ 𝟙 _ =
      (integralDerivedPullback l E (D.geometricFrobenius Y₀).hom).map (𝟙 _) ≫
        (Functor.commShiftIso (integralDerivedPullback l E
          (D.geometricFrobenius Y₀).hom) r).hom.app K.obj
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    exact eq_of_heq h
  · let : (constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).CommShift ℤ := d
    let : (sfWeilFrobeniusPullback D l hl Y₀ E).CommShift ℤ := s
    obtain ⟨β, hβ, hβs⟩ := hs.2
    refine ⟨β, ?_, hβs⟩
    intro K
    exact eq_of_heq ((hβ K).trans (eqToHom_heq_id_dom _ _
      ((rationalDerivedPullback_existsUnique l E
        (D.geometricFrobenius Y₀).hom).exists.choose_spec.2.1
        ((sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left).obj K))).symm)


attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

set_option linter.unusedVariables false in
/-- Truncation functors, the three equivariant triangle arrows and cohomology on
rational Weil pairs, with the signed Roos/localization shift.
Source: blueprint prop-weil-operations.proof.md, sentence 2; BBD 1.3.3--1.3.4
(blueprint: lem-pod-fixed-pair-truncation-cohomology).
Proof (node Steps 1--8 and 10): exact inverse-image transport along the geometric
Frobenius preserves both standard halves (prop-constructible-truncations and
lem-pod-semilinear-field-operation-lifts). The signed Roos shift descends and
localizes as specified by lem-a1-integral-pullback-completed-comparison. Apply
lem-pod-texact-truncation-comparison to obtain the unique comparisons normalized
by the counit and unit. IsoAlgebra.mapOfNatIso gives tau(theta) composed with c,
and maps arrows by tau; its functor laws are the underlying laws. Naturality of
the counit and unit proves equivariance of the first two triangle arrows.
Uniqueness of the whole truncation triangle, including the last arrow
(lem-weil-heart-short-exact-triangles(1)), gives its shift-compatible comparison.
Apply naturality at theta to get the displayed boundary equation. Compose upper
and lower truncations and the normalized i-shift to obtain H^i in the heart.
Apply this to truncated inputs for successive-truncation triangles; uniqueness
of adjoints identifies their absorbed truncations equivariantly. Forgetting
retains exactly the underlying functors and arrows. -/
theorem fixedPairRationalTruncationCohomology :
    ∃ s : (sfWeilFrobeniusPullback D l hl Y₀ E).CommShift ℤ,
      FixedPairRationalShiftNormalization D l hl Y₀ E s ∧
      (fun [shift : (sfWeilFrobeniusPullback D l hl Y₀ E).CommShift ℤ] ↦
        FixedPairTruncationCohomologySpec (fixedPairRationalTStructure D l hl Y₀ E)
          (sfWeilFrobeniusPullback D l hl Y₀ E)) (shift := s) := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  obtain ⟨C, _⟩ := integralPullbackComparisonRealization l E E (AlgHom.id (Padic l) E)
  have h := automorphismConstructibleStage_descended_shifts l (AlgebraicClosure (Padic l)) C
    (D.geometricFrobenius Y₀).hom (Iso.refl _) (Iso.refl _) (by simp)
  obtain ⟨s, sX, sY, hs, _, _, hex⟩ := h.1 E
  let : (sfWeilFrobeniusPullback D l hl Y₀ E).CommShift ℤ := s
  have : (sfWeilFrobeniusPullback D l hl Y₀ E).IsTriangulated := hex.1
  obtain ⟨iX, iY, hX, hY, hE, _, _⟩ :=
    isomorphismFieldTransport D l hl (AlgebraicClosure (Padic l))
      (D.geometricFrobenius Y₀).hom
  have hiX : iX = (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x) := Subsingleton.elim _ _
  have hiY : iY = (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x) := Subsingleton.elim _ _
  subst iX
  subst iY
  obtain ⟨S⟩ := (hE E).1
  let t := fixedPairRationalTStructure D l hl Y₀ E
  have hc : ∀ n : ℤ,
      t.le n = sfRationalStandardClass l E (D.geometricFiber Y₀).left true n ∧
      t.ge n = sfRationalStandardClass l E (D.geometricFiber Y₀).left false n :=
    (sfRationalStandardTStructure_existsUnique l E
      (D.geometricFiber Y₀).left D hl).exists.choose_spec.1
  have : (sfWeilFrobeniusPullback D l hl Y₀ E).IsTExact t t := by
    constructor
    · intro K n hK
      constructor
      rw [(hc n).1]
      exact rationalClass_pullback l E (D.geometricFrobenius Y₀).hom hX hY S true n K
        (by rw [← (hc n).1]; exact hK.le)
    · intro K n hK
      constructor
      rw [(hc n).2]
      exact rationalClass_pullback l E (D.geometricFrobenius Y₀).hom hX hY S false n K
        (by rw [← (hc n).2]; exact hK.ge)
  refine ⟨s, fixedPairRationalShiftNormalization_of_roos D l hl Y₀ E s hs, ?_⟩
  exact fixedPairTruncationCohomologySpec_of_tExact t (sfWeilFrobeniusPullback D l hl Y₀ E)

section

set_option allowUnsafeReducibility true in
attribute [local reducible] StageSystem.instCategoryPairCategory
  StageSystem.PairCategory.categoryStruct
attribute [local irreducible] rationalDerivedPullback constructibleIntegralPullback
set_option allowUnsafeReducibility true in
attribute [local reducible] sfWeilFrobeniusPullback sfCommonStageWeilFrobeniusPullback
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
  GeneralAlgebraicallyClosedCoefficients.stagePreadditive
  GeneralAlgebraicallyClosedCoefficients.stageTransition
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stagePreadditive
  GeneralAlgebraicallyClosedCoefficients.stageShift
attribute [local instance 5000] sfRationalConstructiblePretriangulated
  sfRationalConstructibleTriangulated sfRationalConstructibleShiftAdditive
  sfRationalConstructibleZero sfRationalConstructibleShift sfRationalLocalizationCommShift
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.preadditive
  GeneralAlgebraicallyClosedCoefficients.stagePretriangulated
  GeneralAlgebraicallyClosedCoefficients.transitionIso_commShift
  GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift
  GeneralAlgebraicallyClosedCoefficients.stageShiftAdditive
  GeneralAlgebraicallyClosedCoefficients.inclusion_exact
  GeneralAlgebraicallyClosedCoefficients.hasShift
  GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
  GeneralAlgebraicallyClosedCoefficients.shiftAdditive
  GeneralAlgebraicallyClosedCoefficients.zero_exists
  GeneralAlgebraicallyClosedCoefficients.pretriangulated
  GeneralAlgebraicallyClosedCoefficients.isTriangulated
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Pair
  GeneralAlgebraicallyClosedCoefficients.pairCategory
  generalAlgebraicallyClosedConstructibleCategory


attribute [local irreducible] ScalarLocalization.category in
set_option linter.unusedVariables false in
/-- The same truncations, triangle arrows and cohomology on the literal common-stage
category, including arrows only representable after extending the coefficient field.
Source: blueprint prop-weil-operations.proof.md, sentence 2 and common-stage convention
(blueprint: lem-pod-fixed-pair-truncation-cohomology).
Proof (node Steps 1--8 and 10): use the preceding rational construction at every
finite field. The normalized scalar pullback comparisons identify the integral
signed shifts and their localizations. Their tower coherence descends the shift
through the actual finite-stage inclusions. Use prop-constructible-truncations
and lem-pod-texact-truncation-comparison in the underlying common-stage category.
IsoAlgebra.mapOfNatIso supplies the functor formulas; truncation triangle
uniqueness in lem-weil-heart-short-exact-triangles includes the shifted boundary.
The composite of the two truncations and shift has its value in the standard
heart, and forgetting recovers its underlying cohomology functor. -/
theorem fixedPairCommonTruncationCohomology :
    ∃ (s : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
        (sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).CommShift ℤ)
      (q : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).CommShift ℤ),
      (∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
        FixedPairRationalShiftNormalization D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (s L)) ∧
      FixedPairCommonShiftNormalization D l hl Y₀ Ω s q ∧
      (fun [shift : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).CommShift ℤ] ↦
        FixedPairTruncationCohomologySpec (fixedPairCommonStageTStructure D l hl Y₀ Ω)
          (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω)) (shift := q) := by
  classical
  let := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  let E₀ := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
    (Classical.arbitrary (AlgebraicallyClosedCoefficients.Index l Ω))
  obtain ⟨C, _⟩ := integralPullbackComparisonRealization l E₀ E₀ (AlgHom.id (Padic l) E₀)
  have h := automorphismConstructibleStage_descended_shifts l Ω C
    (D.geometricFrobenius Y₀).hom (Iso.refl _) (Iso.refl _) (by simp)
  obtain ⟨q, qX, qY, hq, _, _, hex⟩ := h.2
  choose s hs hsq using hq
  clear h
  let : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).CommShift ℤ := q
  have : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).IsTriangulated := hex.1
  obtain ⟨iX, iY, hX, hY, _, _, S, R, _, ⟨T⟩, _⟩ :=
    isomorphismFieldTransport D l hl Ω (D.geometricFrobenius Y₀).hom
  have hiX : iX = (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x) := Subsingleton.elim _ _
  have hiY : iY = (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x) := Subsingleton.elim _ _
  subst iX
  subst iY
  refine ⟨s, q, fun L ↦ fixedPairRationalShiftNormalization_of_roos D l hl Y₀
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (s L) (hs L), ?_, ?_⟩
  · delta FixedPairCommonShiftNormalization
    intro L
    let J := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L
    let β : sfWeilFrobeniusPullback D l hl Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) ⋙ J ≅
        J ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω :=
      (T.stageComparison L).symm
    have hβinv (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
        (D.geometricFiber Y₀).left L) : β.inv.app K = eqToHom
          ((commonStageDerivedPullback_existsUnique.{u, v} l Ω
            (D.geometricFrobenius Y₀).hom).exists.choose_spec.1 (J.obj K)) := by
      exact eq_of_heq ((T.stage_comparison_formula L K).trans
        (eqToHom_heq_id_cod _ _ _).symm)
    refine ⟨β, hβinv, ?_⟩
    intro r K
    have hβ (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
        (D.geometricFiber Y₀).left L) : β.hom.app M = eqToHom
          ((commonStageDerivedPullback_existsUnique.{u, v} l Ω
            (D.geometricFrobenius Y₀).hom).exists.choose_spec.1 (J.obj M)).symm := by
      have he : β.symm.app M = eqToIso
          ((commonStageDerivedPullback_existsUnique.{u, v} l Ω
            (D.geometricFrobenius Y₀).hom).exists.choose_spec.1 (J.obj M)) :=
        Iso.ext (hβinv M)
      exact congrArg Iso.inv he
    have hcommon := (GeneralAlgebraicallyClosedCoefficients.shift_existsUnique
      (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left)).exists.choose_spec
    have hJ (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
        (D.geometricFiber Y₀).left L) : (J.commShiftIso r).hom.app M = eqToHom
          (hcommon.2.1 r (J.obj M)).symm := by
      exact eq_of_heq ((hcommon.2.2.2.choose_spec r L M).trans
        (eqToHom_heq_id_dom _ _ _).symm)
    dsimp only [J] at hJ
    let A := sfWeilFrobeniusPullback D l hl Y₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
    let P := sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω
    let eβ (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
        (D.geometricFiber Y₀).left L) : J.obj (A.obj M) = P.obj (J.obj M) :=
      ((commonStageDerivedPullback_existsUnique.{u, v} l Ω
        (D.geometricFrobenius Y₀).hom).exists.choose_spec.1 (J.obj M)).symm
    let eJ (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
        (D.geometricFiber Y₀).left L) :
        J.obj ((shiftFunctor _ r).obj M) = (shiftFunctor _ r).obj (J.obj M) :=
      (hcommon.2.1 r (J.obj M)).symm
    have hβ' (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
        (D.geometricFiber Y₀).left L) : β.hom.app M = eqToHom (eβ M) := hβ M
    have hJ' (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
        (D.geometricFiber Y₀).left L) :
        (J.commShiftIso r).hom.app M = eqToHom (eJ M) := hJ M
    have hshift := fixedPair_shift_square_of_components (shiftFunctor _ r) P
      (J.map ((Functor.commShiftIso A (self := s L) r).hom.app K))
      ((J.commShiftIso r).hom.app (A.obj K)) (β.hom.app K)
      (β.hom.app ((shiftFunctor _ r).obj K)) ((J.commShiftIso r).hom.app K)
      ((Functor.commShiftIso P (self := q) r).hom.app (J.obj K))
      (ha := eJ (A.obj K)) (hb := eβ K)
      (hc := eβ ((shiftFunctor _ r).obj K)) (hd := eJ K)
      (hJ' (A.obj K)) (hβ' K) (hβ' ((shiftFunctor _ r).obj K)) (hJ' K)
      (hsq L K r).symm
    exact hshift
  · let t := fixedPairCommonStageTStructure D l hl Y₀ Ω
    have hc : ∀ n : ℤ,
        t.le n = sfCommonStageStandardClass l (D.geometricFiber Y₀).left Ω true n ∧
        t.ge n = sfCommonStageStandardClass l (D.geometricFiber Y₀).left Ω false n :=
      (sfCommonStageStandardTStructure_existsUnique l (D.geometricFiber Y₀).left Ω D hl)
        |>.exists.choose_spec.1
    have hp (b : Bool) (n : ℤ)
        (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
        (hK : sfCommonStageStandardClass l (D.geometricFiber Y₀).left Ω b n K) :
        sfCommonStageStandardClass l (D.geometricFiber Y₀).left Ω b n
          ((sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).obj K) := by
      obtain ⟨L, M, hM, ⟨e⟩⟩ := hK
      refine ⟨L, (sfWeilFrobeniusPullback D l hl Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).obj M, ?_,
        ⟨(sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).mapIso e ≪≫
          (T.stageComparison L).app M⟩⟩
      exact rationalClass_pullback l _ (D.geometricFrobenius Y₀).hom hX hY (S L) b n M hM
    have : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).IsTExact t t := by
      constructor
      · intro K n hK
        constructor
        rw [(hc n).1]
        exact hp true n K (by rw [← (hc n).1]; exact hK.le)
      · intro K n hK
        constructor
        rw [(hc n).2]
        exact hp false n K (by rw [← (hc n).2]; exact hK.ge)
    exact fixedPairTruncationCohomologySpec_of_tExact t
      (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω)



end

/-- The actual rational Frobenius pullback on Spec k, using the existing derived
pullback and the inherited residue-field inverses.
Source: blueprint def-weil-frobenius-point-transport
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairRationalPointPullback :=
  letI := fun x ↦ frobeniusPointPrimeInvertible D l hl x
  rationalDerivedPullback l E (frobeniusPointIso D).hom

/-- The canonical point transport, with only the recorded pullback-object equality
inserted to identify its endpoint with the actual functor's value.
Source: Deligne Weil II (1.1.7), blueprint point-transport convention
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairRationalPointTransport
    (A : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (pointRationalFibre D l hl E).obj A ⟶
      (pointRationalFibre D l hl E).obj ((fixedPairRationalPointPullback D l hl E).obj A) :=
  frobeniusPointTransportRational D l hl E A ≫
    (pointRationalFibre D l hl E).map
      (eqToHom (frobeniusPointRationalPullbackEq D l hl E A).symm)

/-- Frobenius is point transport followed by the fibre of the given Weil structure.
Source: blueprint fixed-pair cohomology assertion; Deligne Weil II (1.1.7)
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairRationalPointFrobenius
    (A : IsoAlgebra (fixedPairRationalPointPullback D l hl E)) :
    End ((pointRationalFibre D l hl E).obj A.carrier) :=
  fixedPairRationalPointTransport D l hl E A.carrier ≫
    (pointRationalFibre D l hl E).map A.str.hom

/-- Point-fibre maps and their cohomology maps are Frobenius equivariant. This
applies in particular to ordinary or compact-support direct images whenever the
given bounded constructible image has its canonical Weil lift.
Source: blueprint prop-weil-operations.md, final assertion
(blueprint: lem-pod-fixed-pair-truncation-cohomology).
Proof (node Step 9): apply the fibre functor to u theta_A = theta_B P(u).
Functoriality gives the first equality. Naturality in clause (2) of
lem-weil-frobenius-point-transport-natural gives iota_A Fib(Pu) = Fib(u) iota_B,
including the recorded pullback-object identifications. This proves the second
equality. Apply the ordinary H^i functor of def-weil-abstract-derived-category,
restricted by coefficientFdCohomology, and its composition law. No direct image
on a larger domain, or triangulation on pairs, is used. -/
theorem fixedPairRationalPointCohomology
    (A B : IsoAlgebra (fixedPairRationalPointPullback D l hl E)) (f : A ⟶ B) :
    (fixedPairRationalPointFrobenius D l hl E A ≫
        (pointRationalFibre D l hl E).map f.hom.f =
      fixedPairRationalPointTransport D l hl E A.carrier ≫
        (pointRationalFibre D l hl E).map
          ((fixedPairRationalPointPullback D l hl E).map f.hom.f) ≫
        (pointRationalFibre D l hl E).map B.str.hom) ∧
    (fixedPairRationalPointTransport D l hl E A.carrier ≫
        (pointRationalFibre D l hl E).map
          ((fixedPairRationalPointPullback D l hl E).map f.hom.f) ≫
        (pointRationalFibre D l hl E).map B.str.hom =
      (pointRationalFibre D l hl E).map f.hom.f ≫
        fixedPairRationalPointFrobenius D l hl E B) ∧
    ∀ i : ℤ,
      (DerivedCategory.coefficientFdCohomology E i).map
          (fixedPairRationalPointFrobenius D l hl E A) ≫
        (DerivedCategory.coefficientFdCohomology E i).map
          ((pointRationalFibre D l hl E).map f.hom.f) =
      (DerivedCategory.coefficientFdCohomology E i).map
          ((pointRationalFibre D l hl E).map f.hom.f) ≫
        (DerivedCategory.coefficientFdCohomology E i).map
          (fixedPairRationalPointFrobenius D l hl E B) := by
  let F := pointRationalFibre D l hl E
  have h₁ : fixedPairRationalPointFrobenius D l hl E A ≫ F.map f.hom.f =
      fixedPairRationalPointTransport D l hl E A.carrier ≫
        F.map ((fixedPairRationalPointPullback D l hl E).map f.hom.f) ≫
          F.map B.str.hom := by
    dsimp only [fixedPairRationalPointFrobenius]
    simp only [IsoAlgebra.str_hom]
    rw [Category.assoc, ← F.map_comp, ← f.hom.h, F.map_comp]
  have hn : fixedPairRationalPointTransport D l hl E A.carrier ≫
      F.map ((fixedPairRationalPointPullback D l hl E).map f.hom.f) =
        F.map f.hom.f ≫ fixedPairRationalPointTransport D l hl E B.carrier := by
    have h := (frobeniusPointTransport_natural D l hl E).2.2.2.2.2.2.2.2.2.2.1
      A.carrier B.carrier f.hom.f
    have h' := congrArg (fun z ↦ z ≫ F.map
      (eqToHom (frobeniusPointRationalPullbackEq D l hl E B.carrier).symm)) h
    simpa [F, fixedPairRationalPointTransport, fixedPairRationalPointPullback,
      Functor.map_comp, Category.assoc] using h'.symm
  have h₂ : fixedPairRationalPointTransport D l hl E A.carrier ≫
      F.map ((fixedPairRationalPointPullback D l hl E).map f.hom.f) ≫
        F.map B.str.hom =
      F.map f.hom.f ≫ fixedPairRationalPointFrobenius D l hl E B := by
    rw [← Category.assoc, hn, Category.assoc]
    rfl
  refine ⟨h₁, h₂, fun i ↦ ?_⟩
  simpa only [Functor.map_comp] using
    congrArg (DerivedCategory.coefficientFdCohomology E i).map (h₁.trans h₂)

section PointCommonStage
variable (Ω' : Type u) [Field Ω'] [Algebra (Padic l) Ω'] [IsAlgClosure (Padic l) Ω']

/-- Actual common-stage point Frobenius pullback, retaining the coefficient stage.
Source: blueprint common-stage point transport
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairCommonPointPullback :=
  letI := fun x ↦ frobeniusPointPrimeInvertible D l hl x
  commonStageDerivedPullback l Ω' (frobeniusPointIso D).hom

/-- Canonical common-stage point transport, conjugated only by the existing
point-fibre and pullback-object identifications.
Source: blueprint point transport; Deligne Weil II (1.1.7)
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairCommonPointTransport
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω' (Spec (.of D.k))) :
    (pointQbarFibre D l hl Ω').obj A ⟶
      (pointQbarFibre D l hl Ω').obj ((fixedPairCommonPointPullback D l hl Ω').obj A) :=
  eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω' A) ≫
    frobeniusPointTransportQbar D l hl Ω' A ≫
    eqToHom (congrArg (pointQbarFibreObj D l hl Ω')
      (frobeniusPointQbarPullbackEq D l hl Ω' A).symm) ≫
    eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω'
      ((fixedPairCommonPointPullback D l hl Ω').obj A)).symm

/-- The common-stage Frobenius operator uses the given structure and canonical transport.
Source: blueprint fixed-pair cohomology assertion
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairCommonPointFrobenius
    (A : IsoAlgebra (fixedPairCommonPointPullback D l hl Ω')) :
    End ((pointQbarFibre D l hl Ω').obj A.carrier) :=
  fixedPairCommonPointTransport D l hl Ω' A.carrier ≫
    (pointQbarFibre D l hl Ω').map A.str.hom

/-- The full point-transport equation and its stagewise cohomology equation at Qbar.
It includes every arrow represented only over a larger common finite field, hence
also both supplied direct-image Weil lifts on their stated domains.
Source: blueprint prop-weil-operations.md, final assertion
(blueprint: lem-pod-fixed-pair-truncation-cohomology).
Proof (node Steps 9--10): the Weil-arrow equation gives the first equality after
applying pointQbarFibre. The actual common-stage naturality assertion of
lem-weil-frobenius-point-transport-natural(2), with its object identifications,
gives the second. Apply coefficientQbarCohomology of
 def-weil-coefficient-cohomology-modules: at stage E' it is H^i(-) tensor_E' Qbar,
and on an arbitrary common-stage representative it is the specified extended
linear map. Its functor laws give the final equation. Scalar-extension and tower
compatibility ensure the equality survives every further extension. -/
theorem fixedPairCommonPointCohomology
    (A B : IsoAlgebra (fixedPairCommonPointPullback D l hl Ω')) (f : A ⟶ B) :
    (fixedPairCommonPointFrobenius D l hl Ω' A ≫
        (pointQbarFibre D l hl Ω').map f.hom.f =
      fixedPairCommonPointTransport D l hl Ω' A.carrier ≫
        (pointQbarFibre D l hl Ω').map
          ((fixedPairCommonPointPullback D l hl Ω').map f.hom.f) ≫
        (pointQbarFibre D l hl Ω').map B.str.hom) ∧
    (fixedPairCommonPointTransport D l hl Ω' A.carrier ≫
        (pointQbarFibre D l hl Ω').map
          ((fixedPairCommonPointPullback D l hl Ω').map f.hom.f) ≫
        (pointQbarFibre D l hl Ω').map B.str.hom =
      (pointQbarFibre D l hl Ω').map f.hom.f ≫
        fixedPairCommonPointFrobenius D l hl Ω' B) ∧
    ∀ i : ℤ,
      (DerivedCategory.coefficientQbarCohomology l Ω' i).map
          (fixedPairCommonPointFrobenius D l hl Ω' A) ≫
        (DerivedCategory.coefficientQbarCohomology l Ω' i).map
          ((pointQbarFibre D l hl Ω').map f.hom.f) =
      (DerivedCategory.coefficientQbarCohomology l Ω' i).map
          ((pointQbarFibre D l hl Ω').map f.hom.f) ≫
        (DerivedCategory.coefficientQbarCohomology l Ω' i).map
          (fixedPairCommonPointFrobenius D l hl Ω' B) := by
  let F := pointQbarFibre D l hl Ω'
  have h₁ : fixedPairCommonPointFrobenius D l hl Ω' A ≫ F.map f.hom.f =
      fixedPairCommonPointTransport D l hl Ω' A.carrier ≫
        F.map ((fixedPairCommonPointPullback D l hl Ω').map f.hom.f) ≫
          F.map B.str.hom := by
    dsimp only [fixedPairCommonPointFrobenius]
    simp only [IsoAlgebra.str_hom]
    rw [Category.assoc, ← F.map_comp, ← f.hom.h, F.map_comp]
  have hn : fixedPairCommonPointTransport D l hl Ω' A.carrier ≫
      F.map ((fixedPairCommonPointPullback D l hl Ω').map f.hom.f) =
        F.map f.hom.f ≫ fixedPairCommonPointTransport D l hl Ω' B.carrier := by
    have h := (frobeniusPointTransport_natural D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω'
        (Classical.arbitrary (AlgebraicallyClosedCoefficients.Index l Ω')))).2.2.2.2.2.2.2.2.2.2.2.1
      Ω' A.carrier B.carrier f.hom.f
    have h' := congrArg (fun z ↦
      eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω' A.carrier) ≫ z ≫
        eqToHom (congrArg (pointQbarFibreObj D l hl Ω')
          (frobeniusPointQbarPullbackEq D l hl Ω' B.carrier).symm) ≫
        eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω'
          ((fixedPairCommonPointPullback D l hl Ω').obj B.carrier)).symm) h
    set_option backward.isDefEq.respectTransparency.types false in
      simpa [F, fixedPairCommonPointTransport, fixedPairCommonPointPullback,
        Category.assoc] using h'.symm
  have h₂ : fixedPairCommonPointTransport D l hl Ω' A.carrier ≫
      F.map ((fixedPairCommonPointPullback D l hl Ω').map f.hom.f) ≫
        F.map B.str.hom =
      F.map f.hom.f ≫ fixedPairCommonPointFrobenius D l hl Ω' B := by
    rw [← Category.assoc, hn, Category.assoc]
    rfl
  refine ⟨h₁, h₂, fun i ↦ ?_⟩
  simpa only [Functor.map_comp] using
    congrArg (DerivedCategory.coefficientQbarCohomology l Ω' i).map (h₁.trans h₂)

end PointCommonStage
end WeilConjectures
