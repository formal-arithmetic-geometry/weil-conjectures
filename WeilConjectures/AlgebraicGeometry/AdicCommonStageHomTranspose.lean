/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.DerivedAutomorphismHomEvaluation
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorIso
public import WeilConjectures.SixFunctors.RationalVerdier
import WeilConjectures.AlgebraicGeometry.RationalHomScalarTranspose
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleInternalHom
import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.NormalizedCommonEvaluationForStructure
import WeilConjectures.AlgebraicGeometry.CommonTensorBraidingNaturality

/-! # Common-stage evaluation transposition for permitted Hom pairs

Source: Bhatt--Scholze, Lemma 3.4.11, Proposition 6.8.14 and Remark 6.8.15;
the common-field representative argument of the DAG
(blueprint: lem-sf-adic-common-stage-hom-transpose).

The ambient E_T- and R_T-module categories in the node fix the coefficient convention;
the assertion concerns the recorded raw rational stages and their actual pair category.
The normalized partial closed structure and signed braidings are reused, not redefined.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient)

namespace WeilConjectures

attribute [local irreducible] commonStageDerivedTensor commonStageDerivedInternalHom
  podCommonClosed rationalDerivedTensor rationalDerivedInternalHom podRationalClosed
  commonStageTensorComparison commonStageHomComparison

private theorem inverseTranspose_evaluation
    {A : Type*} [Category A] [Preadditive A]
    {T : A × A ⥤ A} {J : ObjectProperty (Aᵒᵖ × A)} {H : J.FullSubcategory ⥤ A}
    (S : PodPartialClosed T J H) (L : A) (P : J.FullSubcategory) (a : L ⟶ H.obj P) :
    (S.transpose L P).symm a =
      T.map (Prod.mkHom a (𝟙 _)) ≫ S.evaluation P := by
  apply (S.transpose L P).injective
  rw [AddEquiv.apply_symm_apply, S.parameter_naturality]
  simp only [PodPartialClosed.evaluation, AddEquiv.apply_symm_apply, Category.comp_id]

private theorem integralConstructible_iff_legacy
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    sfIntegralConstructible l E X K ↔
      boundedConstructibleDerivedCompleteIntegral D l hl E X K := by
  constructor
  · rintro ⟨hc, a, b, hab, h⟩
    refine ⟨(sfDerivedComplete_iff_legacy l E X D hl K).mp hc, a, b, hab, ?_⟩
    intro n
    exact ⟨(h n).1, fun i hi ↦ (h n).2 hi⟩
  · rintro ⟨hc, a, b, hab, h⟩
    refine ⟨(sfDerivedComplete_iff_legacy l E X D hl K).mpr hc, a, b, hab, ?_⟩
    intro n
    exact ⟨(h n).1, fun i hi ↦ (h n).2 i hi⟩

private theorem rationalPair_permitted
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (M N : sfRationalConstructibleCategory l E X) :
    constructibleRationalHomPairs l E X (op M, N) := by
  have h := integral_constructible_internalHom D l hl E X M.obj.obj N.obj.obj
    ((integralConstructible_iff_legacy D l hl E X _).mp M.obj.property)
    ((integralConstructible_iff_legacy D l hl E X _).mp N.obj.property)
  exact (integralConstructible_iff_legacy D l hl E X _).mpr h.1

/-- Evaluation represents all tensor pairings on the common-stage Hom colimits.
The first clause equates the recorded compositum predicate with existence of a
finite-stage witness; thus no site-perfectness assumption or preferred witness is used.
The closed structure is fixed by its finite rational normalization. Its evaluation
has Hom first, i.e. it is the right evaluation in the node. Naturality is simultaneous
in the test object and both entries of the permitted pair. The last clauses specify
the signed swap and every finite scalar-transpose square for arbitrary targets.

Source: BS Lemma 3.4.11, Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-sf-adic-common-stage-hom-transpose).

Proof:
1. Integral constructible internal Hom is constructible in the present finite-type
geometry. Transfer the recorded integral predicate through the derived-completeness
comparison. Consequently every rational pair here is permitted. The compositum
of the entry fields supplies the forward finite witness; the reverse implication
uses constructibility at the specified compositum.
2. Reuse podCommonClosed_existsUnique and its finite-stage normalization. For any
partial closed structure, parameter naturality and injectivity of transpose identify
inverse transposition with tensoring an arrow by the identity followed by evaluation.
The inverse additive equivalence therefore proves the evaluation map bijective.
3. Apply normalizedCommonEvaluation_naturality to the pair arrow. Precompose this
equation with tensor(f followed by a, identity); functoriality gives the required
three-variable naturality formula. Apply commonTensorBraiding_naturality to the
identity and a, then postcompose with evaluation, for the signed-swap formula.
4. The finite scalar-transpose and signed-swap clauses are exactly
rationalHomScalar_transpose, applied to the given coefficient embedding. -/
theorem adicCommonStageHomTranspose
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] :
    (∀ M N : generalAlgebraicallyClosedConstructibleCategory l Ω X,
      commonStageHomPairs l Ω X (op M, N) ↔
        ∃ (E : Index l Ω) (hM : M.stage ≤ E) (hN : N.stage ≤ E),
          constructibleRationalHomPairs l (Coefficient.{u} l Ω E) X
            (op (M.toStage hM), N.toStage hN)) ∧
    (∃ S : PodPartialClosed
        (@commonStageDerivedTensor l _ Ω _ _ _ X (RationalVerdier.units D l hl X))
        (commonStageHomPairs l Ω X) (commonStageDerivedInternalHom l Ω X),
      @PodCommonTransposeNormalization l _ Ω _ _ _ X
        (RationalVerdier.units D l hl X) S ∧
      (∀ (L : generalAlgebraicallyClosedConstructibleCategory l Ω X)
        (P : (commonStageHomPairs l Ω X).FullSubcategory)
        (a : L ⟶ (commonStageDerivedInternalHom l Ω X).obj P),
        (S.transpose L P).symm a =
          (@commonStageDerivedTensor l _ Ω _ _ _ X (RationalVerdier.units D l hl X)).map
            (Prod.mkHom a (𝟙 P.obj.1.unop)) ≫ S.evaluation P) ∧
      (∀ (L : generalAlgebraicallyClosedConstructibleCategory l Ω X)
        (P : (commonStageHomPairs l Ω X).FullSubcategory),
        Function.Bijective (fun a : L ⟶ (commonStageDerivedInternalHom l Ω X).obj P ↦
          (@commonStageDerivedTensor l _ Ω _ _ _ X (RationalVerdier.units D l hl X)).map
            (Prod.mkHom a (𝟙 P.obj.1.unop)) ≫ S.evaluation P)) ∧
      (∀ (L L' : generalAlgebraicallyClosedConstructibleCategory l Ω X)
        (P Q : (commonStageHomPairs l Ω X).FullSubcategory)
        (f : L' ⟶ L) (g : P ⟶ Q)
        (a : L ⟶ (commonStageDerivedInternalHom l Ω X).obj P),
        (S.transpose L' Q).symm (f ≫ a ≫ (commonStageDerivedInternalHom l Ω X).map g) =
          (@commonStageDerivedTensor l _ Ω _ _ _ X (RationalVerdier.units D l hl X)).map
            (Prod.mkHom f g.hom.1.unop) ≫ (S.transpose L P).symm a ≫ g.hom.2) ∧
      (∀ (L : generalAlgebraicallyClosedConstructibleCategory l Ω X)
        (P : (commonStageHomPairs l Ω X).FullSubcategory)
        (a : L ⟶ (commonStageDerivedInternalHom l Ω X).obj P),
        ((@pullbackTensorCommonBraiding l _ Ω _ _ _ X
          (RationalVerdier.units D l hl X)) P.obj.1.unop L).hom ≫
            (S.transpose L P).symm a =
          (@commonStageDerivedTensor l _ Ω _ _ _ X (RationalVerdier.units D l hl X)).map
            (Prod.mkHom (𝟙 P.obj.1.unop) a) ≫
            ((@pullbackTensorCommonBraiding l _ Ω _ _ _ X
              (RationalVerdier.units D l hl X)) P.obj.1.unop
              ((commonStageDerivedInternalHom l Ω X).obj P)).hom ≫ S.evaluation P)) ∧
    (∀ (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
      (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
      (ι : E →ₐ[Padic l] F),
      (∀ (K L W : sfRationalConstructibleCategory l E X)
        (hL : constructibleRationalHomPairs l E X (op L, W))
        (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W),
        (@podRationalClosed l _ F _ _ _ X (RationalVerdier.units D l hl X)).transpose
            ((RationalVerdier.scalar l X E F ι).obj K)
            (rationalHomScalarPair l E F ι X ⟨(op L, W), hL⟩)
            ((@rationalTensorScalarComparison l _ E _ _ _ F _ _ _ ι X
              (RationalVerdier.units D l hl X)).inv.app (K, L) ≫
                (RationalVerdier.scalar l X E F ι).map b) =
          (RationalVerdier.scalar l X E F ι).map
            ((@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).transpose
              K ⟨(op L, W), hL⟩ b) ≫
            (rationalHomScalarComparison l E F ι X ⟨(op L, W), hL⟩).hom) ∧
      (∀ K L : sfRationalConstructibleCategory l E X,
        (@pullbackTensorRationalBraiding l _ F _ _ _ X
          (RationalVerdier.units D l hl X)
          ((RationalVerdier.scalar l X E F ι).obj L)
          ((RationalVerdier.scalar l X E F ι).obj K)).hom ≫
        (@rationalTensorScalarComparison l _ E _ _ _ F _ _ _ ι X
          (RationalVerdier.units D l hl X)).inv.app (K, L) =
        (@rationalTensorScalarComparison l _ E _ _ _ F _ _ _ ι X
          (RationalVerdier.units D l hl X)).inv.app (L, K) ≫
        (RationalVerdier.scalar l X E F ι).map
          ((@pullbackTensorRationalBraiding l _ E _ _ _ X
            (RationalVerdier.units D l hl X) L K).hom))) := by
  let := RationalVerdier.units D l hl X
  refine ⟨?_, ?_, ?_⟩
  · intro M N
    constructor
    · intro h
      exact ⟨Padic.finiteCoefficientCompositum l Ω M.stage N.stage,
        ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1,
        ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2, h⟩
    · intro _
      exact rationalPair_permitted D l hl _ X _ _
  · obtain ⟨S, hS, _⟩ :=
      @podCommonClosed_existsUnique l _ Ω _ _ _ X (RationalVerdier.units D l hl X)
    refine ⟨S, hS, inverseTranspose_evaluation S, ?_, ?_, ?_⟩
    · intro L P
      have he : (fun a ↦
          (commonStageDerivedTensor l Ω X).map (Prod.mkHom a (𝟙 P.obj.1.unop)) ≫
            S.evaluation P) = (S.transpose L P).symm := by
        funext a
        exact (inverseTranspose_evaluation S L P a).symm
      rw [he]
      exact (S.transpose L P).symm.bijective
    · intro L L' P Q f g a
      rw [inverseTranspose_evaluation, inverseTranspose_evaluation]
      have hn := (commonStageDerivedTensor l Ω X).map
        (Prod.mkHom (f ≫ a) (𝟙 Q.obj.1.unop)) ≫=
          normalizedCommonEvaluationForStructure_naturality l Ω X S hS P Q g
      simpa only [← Functor.map_comp_assoc, ← Functor.map_comp, CategoryTheory.prod_comp,
        Category.comp_id, Category.id_comp, Category.assoc] using hn
    · intro L P a
      rw [inverseTranspose_evaluation]
      have hn := commonTensorBraiding_naturality l Ω X
        P.obj.1.unop P.obj.1.unop L ((commonStageDerivedInternalHom l Ω X).obj P)
        (𝟙 P.obj.1.unop) a
      rw [← Category.assoc, ← hn, Category.assoc]
  · intro E _ _ _ F _ _ _ ι
    exact rationalHomScalar_transpose D l hl X E F ι

end WeilConjectures
