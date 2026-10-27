/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.Paper.IntegralOperationsPreserveConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.Paper.FiniteRationalDerivedOperations

import Sheaf.Paper.RationalPullbackStageCoherence
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import all Sheaf.Paper.RationalTensorStageCoherence
import all Sheaf.CategoryTheory.BilinearCoefficientDescent
import all Mathlib.Logic.Small.Defs


/-! # Derived pullback, tensor product, and internal Hom

Source: blueprint sec-smooth-purity/sk-def-sf-operations, order 1467;
Stacks Project, Tags 06YL, 06YV, 08J7 and 099N
(blueprint: def-weil-derived-pullback-tensor-hom).

The finite, integral and rational definitions are publicly re-exported from
`FiniteRationalDerivedOperations`; this file implements the common-stage part.

## Main definitions

- `finiteDerivedPullback`: exact intrinsic constant-coefficient inverse image.
- `finiteIntrinsicDerivedTensor`, `finiteIntrinsicDerivedInternalHom`: ambient operations.
- `finiteIntrinsicTensorModels`: K-flat tensor and ordinary evaluation normalization.
- `finiteIntrinsicReductionHom`: reduced evaluation's canonical closed transpose.
- `constructibleIntegralPullback`, `constructibleIntegralTensor`: actual restrictions.
- `constructibleIntegralHom`: ambient Hom restricted to permitted constructible pairs.
- `rationalDerivedPullback`, `rationalDerivedTensor`, `rationalDerivedInternalHom`:
  the uniquely specified linear and bilinear extensions with unchanged integral objects.
- `commonStageDerivedPullback`, `commonStageDerivedTensor`, `commonStageDerivedInternalHom`:
  operations on the recorded pair category, with normalized representative formulas.

Every common-stage comparison rationalizes the prescribed integral comparison.
No idempotent completion, arbitrary isomorphism, or extra coefficient flatness is used.
-/

-- The module has public declarations; avoid the costly final private-only style scan.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
-- The generated common-stage types make the section-variable linter expensive.
-- Every retained section parameter is present in the operation's public type.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v r s u₁ v₁ u₂ v₂

open Opposite TensorProduct

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

-- Keep the chosen derived localization model abstract during elaboration.
attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear

section PairDescent
variable {I : Type*} [Preorder I] [IsDirectedOrder I]
  {C : I → Type*} [∀ i, Category* (C i)]
  {D : I → Type*} [∀ i, Category* (D i)]
  (S : StageSystem C) (T : StageSystem D) (φ : ∀ i, C i ⥤ D i)

private abbrev pairFunctorObject (P : S.PairCategory) : T.PairCategory :=
  ⟨P.stage, (φ P.stage).obj P.obj⟩

private theorem pairDescent_with_components
    (b : ∀ {i j} (h : i ≤ j), φ i ⋙ T.T h ≅ S.T h ⋙ φ j)
    (hcoh : StageSystem.pairFunctorCoherent S T φ b)
    (c : ∀ (P : S.PairCategory) (M : I) (h : P.stage ≤ M),
      (pairFunctorObject S T φ P).toStage h ≅ (φ M).obj (P.toStage h))
    (hc : ∀ (P : S.PairCategory) (M : I) (h : P.stage ≤ M),
      HEq ((b h).hom.app P.obj) (c P M h).hom ∧
        HEq ((b h).inv.app P.obj) (c P M h).inv) :
    ∃! F : S.PairCategory ⥤ T.PairCategory,
      (∀ P, F.obj P = pairFunctorObject S T φ P) ∧
      (∀ (P Q : S.PairCategory) (M : I) (hP : P.stage ≤ M) (hQ : Q.stage ≤ M)
        (a : P.toStage hP ⟶ Q.toStage hQ),
        HEq (F.map (StageSystem.PairCategory.mkHom M hP hQ a))
          (StageSystem.PairCategory.mkHom
            (X := pairFunctorObject S T φ P) (Y := pairFunctorObject S T φ Q)
            M hP hQ ((c P M hP).hom ≫ (φ M).map a ≫ (c Q M hQ).inv))) := by
  have H := StageSystem.coefficientPairFunctor_exists S T φ b hcoh
  apply (existsUnique_congr (fun F ↦ ?_)).mp H
  constructor
  · rintro ⟨ho, hm⟩
    refine ⟨fun P ↦ ?_, fun P Q M hP hQ a ↦ ?_⟩
    · exact (ho P).trans (StageSystem.coefficientPairFunctorObject_eq S T φ P)
    · cases P with
      | mk i P =>
        cases Q with
        | mk j Q =>
          have hp := eq_of_heq (hc ⟨i, P⟩ M hP).1
          have hq := eq_of_heq (hc ⟨j, Q⟩ M hQ).2
          simpa only [hp, hq, StageSystem.coefficientPairFunctorObject,
            pairFunctorObject] using hm M hP hQ a
  · rintro ⟨ho, hm⟩
    refine ⟨fun P ↦ ?_, fun {P Q} M hP hQ a ↦ ?_⟩
    · exact (ho P).trans (StageSystem.coefficientPairFunctorObject_eq S T φ P).symm
    · cases P with
      | mk i P =>
        cases Q with
        | mk j Q =>
          have hp := eq_of_heq (hc ⟨i, P⟩ M hP).1
          have hq := eq_of_heq (hc ⟨j, Q⟩ M hQ).2
          simpa only [hp, hq, StageSystem.coefficientPairFunctorObject,
            pairFunctorObject] using hm ⟨i, P⟩ ⟨j, Q⟩ M hP hQ a

end PairDescent

/-! Private helpers of the former single module, kept here verbatim: the importers
`FiniteProductFieldCoefficientDescent` and `RationalRestrictionComparisonCoherence` use them
through `import all Sheaf.Paper.DerivedPullbackTensorHom`. -/

private theorem map_heq {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private def bilinearAdd {R : Type*} [CommSemiring R]
    {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (b : M →ₗ[R] N →ₗ[R] P) :
    M →+ N →+ P :=
  LinearMap.toAddMonoidHom'.comp b.toAddMonoidHom

private def bilinearPost {M N P Q : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    (b : M →+ N →+ P) (f : P →+ Q) : M →+ N →+ Q where
  toFun x := f.comp (b x)
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

private def bilinearPre {M N P M' N' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N']
    (b : M →+ N →+ P) (f : M' →+ M) (g : N' →+ N) : M' →+ N' →+ P where
  toFun x := (b (f x)).comp g
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

private theorem prod_hom_heq
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {X Y X' Y' : C} {Z T Z' T' : D}
    (hx : X = X') (hy : Y = Y') (hz : Z = Z') (ht : T = T')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Z ⟶ T} {g' : Z' ⟶ T'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (Prod.mkHom f g) (Prod.mkHom f' g') := by
  cases hx; cases hy; cases hz; cases ht
  cases hf; cases hg
  rfl

private theorem rawBilinearIso_existsUnique
    {R : Type r} [CommRing R] {S : Type s} [CommRing S]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear S D]
    (t : R) (b : S) (c : Localization.Away t → Localization.Away b)
    (U V : C × C ⥤ D) (e : U ≅ V)
    (F G : ScalarLocalization R C t × ScalarLocalization R C t ⥤
      ScalarLocalization S D b)
    (hF : ∀ K, F.obj K = ⟨U.obj (K.1.obj, K.2.obj)⟩)
    (hG : ∀ K, G.obj K = ⟨V.obj (K.1.obj, K.2.obj)⟩)
    (mF : ∀ (K K' L L' : ScalarLocalization R C t),
      ∃ β : (K ⟶ K') →+
        (L ⟶ L') →+ (F.obj (K, L) ⟶ F.obj (K', L')),
        (∀ f g, F.map (Prod.mkHom f g) = β f g) ∧
        ∀ (f : K.obj ⟶ K'.obj) (g : L.obj ⟶ L'.obj) (x y : Localization.Away t),
          HEq (β (x ⊗ₜ[R] f) (y ⊗ₜ[R] g))
            (c (x * y) ⊗ₜ[S] U.map (Prod.mkHom f g)))
    (mG : ∀ (K K' L L' : ScalarLocalization R C t),
      ∃ β : (K ⟶ K') →+
        (L ⟶ L') →+ (G.obj (K, L) ⟶ G.obj (K', L')),
        (∀ f g, G.map (Prod.mkHom f g) = β f g) ∧
        ∀ (f : K.obj ⟶ K'.obj) (g : L.obj ⟶ L'.obj) (x y : Localization.Away t),
          HEq (β (x ⊗ₜ[R] f) (y ⊗ₜ[R] g))
            (c (x * y) ⊗ₜ[S] V.map (Prod.mkHom f g))) :
    ∃! α : F ≅ G, ∀ K, HEq (α.hom.app K)
      ((ScalarLocalization.localization S D b).map (e.hom.app (K.1.obj, K.2.obj))) := by
  let Q := ScalarLocalization.localization S D b
  let a K := eqToIso (hF K) ≪≫ Q.mapIso (e.app (K.1.obj, K.2.obj)) ≪≫
    (eqToIso (hG K)).symm
  have ha K : HEq (a K).hom (Q.map (e.hom.app (K.1.obj, K.2.obj))) := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
      Functor.mapIso_hom]
    exact ((conj_eqToHom_iff_heq _ _ (hF K) (hG K)).1 rfl)
  have hn (K L : ScalarLocalization R C t × ScalarLocalization R C t)
      (f : K ⟶ L) : F.map f ≫ (a L).hom = (a K).hom ≫ G.map f := by
    obtain ⟨β, hβ, pβ⟩ := mF K.1 L.1 K.2 L.2
    obtain ⟨γ, hγ, pγ⟩ := mG K.1 L.1 K.2 L.2
    change F.map (Prod.mkHom f.1 f.2) ≫ _ = _ ≫ G.map (Prod.mkHom f.1 f.2)
    rw [hβ, hγ]
    generalize f.1 = f₁, f.2 = f₂
    induction f₁ using TensorProduct.induction_on with
    | zero => simp
    | tmul x f₁ =>
      induction f₂ using TensorProduct.induction_on with
      | zero => simp
      | tmul y f₂ =>
        have h₁ := heq_comp (hF K) (hF L) (hG L) (pβ f₁ f₂ x y) (ha L)
        have h₂ := heq_comp (hF K) (hG K) (hG L) (ha K) (pγ f₁ f₂ x y)
        apply eq_of_heq
        refine h₁.trans (HEq.trans ?_ h₂.symm)
        apply heq_of_eq
        change ScalarLocalization.composition S D b _ _ _
            (1 ⊗ₜ[S] e.hom.app (L.1.obj, L.2.obj))
            (c (x * y) ⊗ₜ[S] U.map (Prod.mkHom f₁ f₂)) =
          ScalarLocalization.composition S D b _ _ _
            (c (x * y) ⊗ₜ[S] V.map (Prod.mkHom f₁ f₂))
            (1 ⊗ₜ[S] e.hom.app (K.1.obj, K.2.obj))
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one,
          e.hom.naturality]
      | add x y hx hy => simp only [map_add, Preadditive.add_comp,
          Preadditive.comp_add, hx, hy]
    | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply,
        Preadditive.add_comp, Preadditive.comp_add, hx, hy]
  refine ⟨NatIso.ofComponents a (fun {K L} f ↦ hn K L f), ha, ?_⟩
  intro α hα
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hα K).trans (ha K).symm)


private theorem chosenUnique_spec {A : Sort*} {p : A → Prop} (h : ∃! a, p a)
    (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

private abbrev rationalTensor_spec (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :=
  chosenUnique_spec (rationalDerivedTensor_existsUnique l E W)
    (rationalDerivedTensor l E W) rfl

private theorem rationalScalar_obj (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u})
    (K : sfRationalConstructibleCategory l E W) :
    (sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K =
      ScalarLocalization.mk ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj K.obj) := by
  exact (sfRationalScalarExtension_existsUnique l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 K

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue

attribute [local irreducible] integralDerivedPullback integralCompletedTensor
  integralDerivedInternalHom sfRationalScalarExtension
  completedIntegralCoefficientSheafUnrestricted integralScalarExtension integralOrdinaryScalar

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor

section CommonStage
attribute [local irreducible] rationalDerivedInternalHom
  ScalarLocalization.composition StageSystem.PairCategory.mkHom
attribute [local irreducible] sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

attribute [local irreducible] rationalHomScalarComparison
  sfConstructibleIntegralScalarExtension sfIntegralScalarComp sfIntegralScalarUnit

/-- The recorded stage transition is the specified rational scalar functor.
The equality is part of the existing stage-system uniqueness specification.
Source: blueprint common-stage coefficient construction
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def operationStageTransitionIso (W : Scheme.{u})
    (E L : Index l Ω) (h : E ≤ L) :
    (stageSystem l Ω W).T h ≅ transition l Ω W E L h :=
  eqToIso ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h)

attribute [local irreducible] operationStageTransitionIso

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem


private theorem operationStageIntegralObject (W : Scheme.{u})
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : Index l Ω) (h : P.stage ≤ L) :
    (P.toStage h).obj =
      (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l Ω P.stage) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω P.stage L h) W).obj P.obj.obj := by
  change (((stageSystem l Ω W).T h).obj P.obj).obj = _
  have ht : (stageSystem l Ω W).T h = transition l Ω W P.stage L h := by
    simpa only [stageSystem] using
      (stageSystem_existsUnique l Ω W).exists.choose_spec.1 P.stage L h
  have hi := rationalScalar_obj l (Coefficient.{u} l Ω P.stage)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω P.stage L h) W P.obj
  exact (congrArg (fun F : Stage l Ω W P.stage ⥤ Stage l Ω W L ↦
    (F.obj P.obj).obj) ht).trans (congrArg ScalarLocalization.obj hi)

private noncomputable def operationStageIntegralAssociator (W : Scheme.{u})
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (M L : Index l Ω) (h : P.stage ≤ M) (k : M ≤ L) :
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime))
      (Coefficient.{u} l Ω M) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω M L k) W).obj (P.toStage h).obj ≅
      (P.toStage (h.trans k)).obj :=
  eqToIso (congrArg (fun K ↦ (sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (Coefficient.{u} l Ω M) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω M L k) W).obj K)
      (operationStageIntegralObject l Ω W P M h)) ≪≫
    (sfIntegralScalarComp l (Coefficient.{u} l Ω P.stage) (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω P.stage M h) W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω M L k)).app P.obj.obj ≪≫
    eqToIso (congrArg (fun ι ↦ (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime))
      (Coefficient.{u} l Ω P.stage) (Coefficient.{u} l Ω L) ι W).obj P.obj.obj)
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2
          P.stage M L h k)) ≪≫
    (eqToIso (operationStageIntegralObject l Ω W P L (h.trans k))).symm

attribute [local irreducible] operationStageIntegralAssociator

/-- Common-stage pullback retains the literal coefficient stage.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStagePullbackObject {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  ⟨P.stage, (rationalDerivedPullback l (Coefficient.{u} l Ω P.stage) f).obj P.obj⟩

section ComparisonElaboration
attribute [local irreducible] ObjectProperty.FullSubcategory.category

/-- The canonical pullback comparison includes the recorded transition identifications.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStagePullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : Index l Ω) (h : P.stage ≤ L) :
    (commonStagePullbackObject l Ω f P).toStage h ≅
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).obj (P.toStage h) :=
  (operationStageTransitionIso l Ω X P.stage L h).app
      (commonStagePullbackObject l Ω f P).obj ≪≫
    (rationalPullbackScalarComparison l (Coefficient.{u} l Ω P.stage)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω P.stage L h) f).app P.obj ≪≫
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).mapIso
      ((operationStageTransitionIso l Ω Y P.stage L h).app P.obj).symm

end ComparisonElaboration

attribute [local irreducible] commonStagePullbackComparison

section PullbackProofs

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
attribute [local irreducible] ScalarLocalization.category

/- The scalar comparisons form a coherent stage-system morphism.  The proof is
   the tower coherence calculation for the normalized rational pullback
   comparisons (blueprint: lem-weil-common-stage-pullback-comparison-data).
   The normalized scalar-extension tower calculation supplies the comparison
   components and their pairFunctorCoherent equation. -/
theorem commonStagePullback_comparison_data {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ b : ∀ {E L : Index l Ω} (h : E ≤ L),
      (rationalDerivedPullback l (Coefficient.{u} l Ω E) f) ⋙
          (stageSystem l Ω X).T h ≅
        (stageSystem l Ω Y).T h ⋙
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) f),
      (∀ {E L : Index l Ω} (h : E ≤ L)
        (P : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
        HEq ((b h).hom.app P)
          ((commonStagePullbackComparison l Ω f ⟨E, P⟩ L h).hom) ∧
        HEq ((b h).inv.app P)
          ((commonStagePullbackComparison l Ω f ⟨E, P⟩ L h).inv)) ∧
      (∀ {E L M : Index l Ω} (h : E ≤ L) (h' : L ≤ M)
        (P : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
        ((stageSystem l Ω X).T h').map ((b h).hom.app P) ≫
          (b h').hom.app (((stageSystem l Ω Y).T h).obj P) ≫
          (rationalDerivedPullback l (Coefficient.{u} l Ω M) f).map
            (((stageSystem l Ω Y).assoc h h').hom.app P) =
        (((stageSystem l Ω X).assoc h h').hom.app
            ((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).obj P) ≫
          (b (h.trans h')).hom.app P)) := by
  refine ⟨fun {_ _} h ↦ rationalPullbackStageComparison l Ω f h, ?_,
    rationalPullbackStageComparison_coherent l Ω f⟩
  intro E L h P
  have hi : (rationalPullbackStageComparison l Ω f h).app P =
      commonStagePullbackComparison l Ω f ⟨E, P⟩ L h := by
    apply Iso.ext
    unfold rationalPullbackStageComparison commonStagePullbackComparison
      operationStageTransitionIso
    simp only [Iso.app_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
      commonStagePullbackObject]
  exact ⟨heq_of_eq (congrArg Iso.hom hi), heq_of_eq (congrArg Iso.inv hi)⟩


/-- Descent from a fixed coherent pullback comparison family.
Source: the common-stage pullback paragraph of the blueprint.
(blueprint: lem-weil-common-stage-pullback-descent-from-data).
The proof applies the StageSystem coefficient-pair descent constructor and then
rewrites the descended representative formula using the supplied comparison
components. -/
theorem commonStagePullback_descent_from_data {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (b : ∀ {E L : Index l Ω} (h : E ≤ L),
      (rationalDerivedPullback l (Coefficient.{u} l Ω E) f) ⋙
          (stageSystem l Ω X).T h ≅
        (stageSystem l Ω Y).T h ⋙
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) f))
    (hb : ∀ {E L : Index l Ω} (h : E ≤ L)
        (P : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
        HEq ((b h).hom.app P)
          ((commonStagePullbackComparison l Ω f ⟨E, P⟩ L h).hom) ∧
        HEq ((b h).inv.app P)
          ((commonStagePullbackComparison l Ω f ⟨E, P⟩ L h).inv))
    (hcoh : ∀ {E L M : Index l Ω} (h : E ≤ L) (h' : L ≤ M)
        (P : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
        ((stageSystem l Ω X).T h').map ((b h).hom.app P) ≫
          (b h').hom.app (((stageSystem l Ω Y).T h).obj P) ≫
          (rationalDerivedPullback l (Coefficient.{u} l Ω M) f).map
            (((stageSystem l Ω Y).assoc h h').hom.app P) =
        (((stageSystem l Ω X).assoc h h').hom.app
            ((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).obj P) ≫
          (b (h.trans h')).hom.app P)) :
    ∃! F : generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω X,
      (∀ P, F.obj P = commonStagePullbackObject l Ω f P) ∧
      (∀ (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
        (L : Index l Ω) (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
        (a : P.toStage hP ⟶ Q.toStage hQ),
        HEq (F.map (X := P) (Y := Q) (ofHom P Q L hP hQ a))
          (ofHom (commonStagePullbackObject l Ω f P)
            (commonStagePullbackObject l Ω f Q) L hP hQ
            ((commonStagePullbackComparison l Ω f P L hP).hom ≫
              (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).map a ≫
              (commonStagePullbackComparison l Ω f Q L hQ).inv))) := by
  dsimp only [ofHom, StageHom, stageTransition, commonStagePullbackObject]
  have H := @pairDescent_with_components (Index l Ω) inferInstance inferInstance
    (Stage l Ω Y) (fun E ↦ stageCategory l Ω Y E)
    (Stage l Ω X) (fun E ↦ stageCategory l Ω X E)
    (stageSystem l Ω Y) (stageSystem l Ω X)
    (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f) b hcoh
    (fun P L h ↦ commonStagePullbackComparison l Ω f P L h)
    (by
      intro P L h
      cases P with
      | mk E P => exact hb h P)
  exact H

/-- Pullback on the actual pair-category quotient has the prescribed representative action.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: use the normalized rationalPullbackScalarComparison for every coefficient
inclusion. The strict generator formulas commute with a tower of coefficient
maps; multiplication and associativity of tensors give the scalar associators.
Both Roos coordinates preserve these equalities. Thus the comparisons satisfy
the coherent pair-functor descent equation. Conjugating a representative by the
source comparison and inverse target comparison is independent of enlargement
and eventual equality. Composition cancels the middle comparisons; identity
representatives give identities. Every arrow has a representative, so the object
and representative formulas uniquely determine the functor. -/
theorem commonStageDerivedPullback_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! F : generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω X,
      (∀ P, F.obj P = commonStagePullbackObject l Ω f P) ∧
      (∀ (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
        (L : Index l Ω) (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
        (a : P.toStage hP ⟶ Q.toStage hQ),
        HEq (F.map (X := P) (Y := Q) (ofHom P Q L hP hQ a))
          (ofHom (commonStagePullbackObject l Ω f P)
            (commonStagePullbackObject l Ω f Q) L hP hQ
            ((commonStagePullbackComparison l Ω f P L hP).hom ≫
              (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).map a ≫
              (commonStagePullbackComparison l Ω f Q L hQ).inv))) := by
  exact (commonStagePullback_comparison_data l Ω f).elim
    (fun b hb ↦ commonStagePullback_descent_from_data l Ω f b hb.1 hb.2)

end PullbackProofs

/-- Canonical common-stage pullback, with no new coefficient objects or retracts.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageDerivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :=
  (commonStageDerivedPullback_existsUnique l Ω f).exists.choose

/-- The literal tensor object is formed at the finite coefficient compositum.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageTensorObject (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    generalAlgebraicallyClosedConstructibleCategory l Ω W :=
  ⟨Padic.finiteCoefficientCompositum l Ω P.stage Q.stage,
    (rationalDerivedTensor l (Coefficient.{u} l Ω
      (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage)) W).obj
      (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1,
        Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2)⟩

section ComparisonElaboration
attribute [local irreducible] ObjectProperty.FullSubcategory.category

/-- The tensor comparison at a common stage includes the scalar associators of both inputs.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageTensorComparison (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : Index l Ω) (h : (commonStageTensorObject l Ω W P Q).stage ≤ L) :
    (commonStageTensorObject l Ω W P Q).toStage h ≅
      (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).obj
        (P.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h),
          Q.toStage
            (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h)) :=
  (operationStageTransitionIso l Ω W _ L h).app
      (commonStageTensorObject l Ω W P Q).obj ≪≫
    (rationalTensorScalarComparison l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage))
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L h) W).app
      (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1,
        Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2) ≪≫
    (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).mapIso
      (Iso.prod
        (((operationStageTransitionIso l Ω W _ L h).app
          (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
            P.stage Q.stage).1)).symm ≪≫
          ((stageSystem l Ω W).assoc
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1 h).app P.obj)
        (((operationStageTransitionIso l Ω W _ L h).app
          (Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
            P.stage Q.stage).2)).symm ≪≫
          ((stageSystem l Ω W).assoc
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2 h).app Q.obj))

end ComparisonElaboration

attribute [local irreducible] commonStageTensorComparison

section TensorDescentElaboration
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.pairCategory CategoryTheory.uniformProd
attribute [local semireducible] operationStageTransitionIso
attribute [local irreducible] ObjectProperty.FullSubcategory.category ScalarLocalization.category

/-- Common-stage tensor has the bilinear representative formula of the blueprint.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: extend both endpoints to their finite coefficient composita and use the
literal object formula. At a common larger stage, use commonStageTensorComparison
to identify their scalar extensions with the tensor of the extended inputs. The
normalized scalar tensor comparisons are natural, compatible with coefficient
towers and units: test their strict finite generator formulas and both Roos
coordinates. Thus the displayed conjugation respects eventual equality. At a
common stage, composition and identities follow from the rational tensor functor;
intermediate comparisons cancel. Directedness puts every pair of morphisms at
such a common stage, so the formula also gives uniqueness. -/
theorem commonStageDerivedTensor_existsUnique (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃! F : generalAlgebraicallyClosedConstructibleCategory l Ω W ×
        generalAlgebraicallyClosedConstructibleCategory l Ω W ⥤
          generalAlgebraicallyClosedConstructibleCategory l Ω W,
      (∀ P Q, F.obj (P, Q) = commonStageTensorObject l Ω W P Q) ∧
      (∀ (P Q P' Q' : generalAlgebraicallyClosedConstructibleCategory l Ω W)
        (L : Index l Ω)
        (h : (commonStageTensorObject l Ω W P Q).stage ≤ L)
        (h' : (commonStageTensorObject l Ω W P' Q').stage ≤ L)
        (a : P.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h) ⟶
          P'.toStage
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).1.trans h'))
        (b : Q.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h) ⟶
          Q'.toStage
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).2.trans h')),
        HEq (F.map (X := (P, Q)) (Y := (P', Q')) (Prod.mkHom
          (ofHom P P' L
            (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h)
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).1.trans h') a)
          (ofHom Q Q' L
            (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h)
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).2.trans h') b)))
          (ofHom (commonStageTensorObject l Ω W P Q)
            (commonStageTensorObject l Ω W P' Q') L h h'
            ((commonStageTensorComparison l Ω W P Q L h).hom ≫
              (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).map (Prod.mkHom a b) ≫
              (commonStageTensorComparison l Ω W P' Q' L h').inv))) := by
  let S := stageSystem l Ω W
  let U : BilinearCoefficientDescent.Family S S S :=
    ⟨fun E ↦ rationalDerivedTensor l (Coefficient.{u} l Ω E) W,
      fun {_ _} h ↦ rationalTensorStageComparison l Ω W h,
      rationalTensorStageComparison_coherent l Ω W⟩
  let join := Padic.finiteCoefficientCompositum l Ω
  let left := fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1
  let right := fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2
  have hc (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω W)
      (L : Index l Ω) (h : join P.stage Q.stage ≤ L) :
      BilinearCoefficientDescent.endpoint U join left right (P, Q) h =
        commonStageTensorComparison l Ω W P Q L h := by
    unfold BilinearCoefficientDescent.endpoint
    change ((rationalTensorStageComparison l Ω W h).app
      (P.toStage (left P.stage Q.stage), Q.toStage (right P.stage Q.stage)) ≪≫
      (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).mapIso
        (Iso.prod ((S.assoc (left P.stage Q.stage) h).app P.obj)
          ((S.assoc (right P.stage Q.stage) h).app Q.obj))) = _
    delta rationalTensorStageComparison commonStageTensorComparison operationStageTransitionIso
    have hh := tensorStageComparison_endpoint
      (C := Stage l Ω W (join P.stage Q.stage)) (D := Stage l Ω W L)
      (rationalDerivedTensor l (Coefficient.{u} l Ω (join P.stage Q.stage)) W)
      (rationalDerivedTensor l (Coefficient.{u} l Ω L) W)
      (operationStageTransitionIso l Ω W _ L h)
      (rationalTensorScalarComparison l (Coefficient.{u} l Ω (join P.stage Q.stage))
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L h) W)
      (P.toStage (left P.stage Q.stage)) (Q.toStage (right P.stage Q.stage))
      ((S.assoc (left P.stage Q.stage) h).app P.obj)
      ((S.assoc (right P.stage Q.stage) h).app Q.obj)
    exact hh
  exact tensorDescent_with_components S U join left right
    (fun P Q L h ↦ commonStageTensorComparison l Ω W P Q L h) hc

end TensorDescentElaboration

/-- The canonical common-stage tensor functor on the existing pair category.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageDerivedTensor (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :=
  (commonStageDerivedTensor_existsUnique l Ω W).exists.choose

/-- The permitted common-stage Hom pairs: extend both entries to their compositum,
then require exactly the integral-Hom constructibility predicate there.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageHomPairs (W : Scheme.{u}) :
    ObjectProperty ((generalAlgebraicallyClosedConstructibleCategory l Ω W)ᵒᵖ ×
      generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  fun P ↦ constructibleRationalHomPairs l
    (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω P.1.unop.stage P.2.stage)) W
    (op (P.1.unop.toStage
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.1.unop.stage P.2.stage).1),
      P.2.toStage
        ((Padic.finiteCoefficientFields_properties l Ω).1 P.1.unop.stage P.2.stage).2)

/-- The literal permitted rational pair at the compositum, with no choice of lift.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageHomRationalPair (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :
    (constructibleRationalHomPairs l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω
        P.obj.1.unop.stage P.obj.2.stage)) W).FullSubcategory :=
  ⟨(op (P.obj.1.unop.toStage
      ((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1),
    P.obj.2.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2), P.property⟩

/-- Common-stage internal Hom is the literal pair at the coefficient compositum.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageHomObject (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :
    generalAlgebraicallyClosedConstructibleCategory l Ω W :=
  ⟨Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage,
    (rationalDerivedInternalHom l (Coefficient.{u} l Ω
      (Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage)) W).obj
        (commonStageHomRationalPair l Ω W P)⟩

/-- A permitted compositum pair remains permitted at every larger finite stage.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: rationalHomScalarPair_permitted first extends the permitted integral pair.
The two integral scalar associators identify its entries with the entries extended
directly from their original stages. Internal Hom uses the inverse first
associator and the second associator. Its underlying integral isomorphism preserves
constructibility. Thus the displayed predicate holds before rationalization,
including identity inclusions and every further stage. -/
theorem commonStageHomPairAtStage_permitted (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    constructibleRationalHomPairs l (Coefficient.{u} l Ω L) W
      (op (P.obj.1.unop.toStage
        (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).1.trans h)),
        P.obj.2.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).2.trans h)) := by
  let M := Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage
  have hM := (Padic.finiteCoefficientFields_properties l Ω).1
    P.obj.1.unop.stage P.obj.2.stage
  let A := Coefficient.{u} l Ω M
  let B := Coefficient.{u} l Ω L
  let e₁ := operationStageIntegralAssociator l Ω W P.obj.1.unop M L hM.1 h
  let e₂ := operationStageIntegralAssociator l Ω W P.obj.2 M L hM.2 h
  have hP := integralHomScalarPair_permitted l A B
    (coefficientInclusion l Ω M L h) W
      (integralPairOfRationalHomPair l A W (commonStageHomRationalPair l Ω W P))
  let e := (integralDerivedInternalHom l B W).mapIso
    (Iso.prod ((sfIntegralConstructible l B W).ι.mapIso e₁).symm.op
      ((sfIntegralConstructible l B W).ι.mapIso e₂))
  exact (sfIntegralConstructible l B W).prop_of_iso e hP

/-- The permitted pair at a larger stage, using the actual scalar extensions.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageHomPairAtStage (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    (constructibleRationalHomPairs l (Coefficient.{u} l Ω L) W).FullSubcategory :=
  ⟨(op (P.obj.1.unop.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h)),
    P.obj.2.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2.trans h)),
    commonStageHomPairAtStage_permitted l Ω W P L h⟩


section ComparisonElaboration
attribute [local irreducible] ObjectProperty.FullSubcategory.category

/-- The Hom comparison includes the inverse first-variable scalar associator.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageHomComparison (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    (commonStageHomObject l Ω W P).toStage h ≅
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).obj
        (commonStageHomPairAtStage l Ω W P L h) :=
  (operationStageTransitionIso l Ω W _ L h).app
      (commonStageHomObject l Ω W P).obj ≪≫
    rationalHomScalarComparison l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω
        P.obj.1.unop.stage P.obj.2.stage))
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L h) W
        (commonStageHomRationalPair l Ω W P) ≪≫
    (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).mapIso
      (ObjectProperty.isoMk _ (Iso.prod
        (((operationStageTransitionIso l Ω W _ L h).app
            (P.obj.1.unop.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
              P.obj.1.unop.stage P.obj.2.stage).1)).symm ≪≫
          ((stageSystem l Ω W).assoc ((Padic.finiteCoefficientFields_properties l Ω).1
            P.obj.1.unop.stage P.obj.2.stage).1 h).app P.obj.1.unop.obj).symm.op
        (((operationStageTransitionIso l Ω W _ L h).app
            (P.obj.2.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
              P.obj.1.unop.stage P.obj.2.stage).2)).symm ≪≫
          ((stageSystem l Ω W).assoc ((Padic.finiteCoefficientFields_properties l Ω).1
            P.obj.1.unop.stage P.obj.2.stage).2 h).app P.obj.2.obj)))

end ComparisonElaboration

attribute [local irreducible] commonStageHomComparison

set_option allowUnsafeReducibility true in
attribute [local reducible] commonStageHomObject commonStageHomPairAtStage


/-- Common-stage internal Hom has precisely the contravariant representative formula.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: form the permitted rational Hom at each literal compositum. The permitted
pair remains permitted at every common stage by commonStageHomPairAtStage_permitted.
Use commonStageHomComparison to compare the scalar extension of each output with
the Hom of the extended inputs. Its ordinary comparison transposes extended
evaluation; the inverse comparison in its first argument gives exactly u.op in
the formula. Naturality and the normalized coefficient tower equations show that
conjugation respects further transport and eventual equality. At a common stage,
the rational Hom functor gives identity and composition; the middle comparisons
cancel. Directedness puts any two representatives at such a stage. Every arrow
has a representative, so these formulas determine the functor uniquely. -/
theorem commonStageDerivedInternalHom_existsUnique (W : Scheme.{u}) :
    ∃! F : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω W,
      (∀ P, F.obj P = commonStageHomObject.{u, v} l Ω W P) ∧
      (∀ (P Q : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
        (L : Index l Ω)
        (h : (StageSystem.PairCategory.stage.{v, u+2, u+2}
          (commonStageHomObject.{u, v} l Ω W P)) ≤ L)
        (h' : (StageSystem.PairCategory.stage.{v, u+2, u+2}
          (commonStageHomObject.{u, v} l Ω W Q)) ≤ L)
        (a : (commonStageHomPairAtStage.{u, v} l Ω W Q L h').obj.1.unop ⟶
          (commonStageHomPairAtStage.{u, v} l Ω W P L h).obj.1.unop)
        (b : (commonStageHomPairAtStage.{u, v} l Ω W P L h).obj.2 ⟶
          (commonStageHomPairAtStage.{u, v} l Ω W Q L h').obj.2),
        HEq (F.map (X := P) (Y := Q)
          (ObjectProperty.homMk (X := P) (Y := Q) (Prod.mkHom
            (StageSystem.PairCategory.mkHom.{v, u+2, u+2}
              (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω W)
              (S := stageSystem l Ω W) (X := Q.obj.1.unop) (Y := P.obj.1.unop) L
              (((Padic.finiteCoefficientFields_properties l Ω).1
                (StageSystem.PairCategory.stage.{v, u+2, u+2} Q.obj.1.unop)
                (StageSystem.PairCategory.stage.{v, u+2, u+2} Q.obj.2)).1.trans h')
              (((Padic.finiteCoefficientFields_properties l Ω).1
                (StageSystem.PairCategory.stage.{v, u+2, u+2} P.obj.1.unop)
                (StageSystem.PairCategory.stage.{v, u+2, u+2} P.obj.2)).1.trans h) a).op
            (StageSystem.PairCategory.mkHom.{v, u+2, u+2}
              (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω W)
              (S := stageSystem l Ω W) (X := P.obj.2) (Y := Q.obj.2) L
              (((Padic.finiteCoefficientFields_properties l Ω).1
                (StageSystem.PairCategory.stage.{v, u+2, u+2} P.obj.1.unop)
                (StageSystem.PairCategory.stage.{v, u+2, u+2} P.obj.2)).2.trans h)
              (((Padic.finiteCoefficientFields_properties l Ω).1
                (StageSystem.PairCategory.stage.{v, u+2, u+2} Q.obj.1.unop)
                (StageSystem.PairCategory.stage.{v, u+2, u+2} Q.obj.2)).2.trans h') b))))
          (StageSystem.PairCategory.mkHom.{v, u+2, u+2}
              (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω W)
              (S := stageSystem l Ω W)
              (X := commonStageHomObject.{u, v} l Ω W P)
              (Y := commonStageHomObject.{u, v} l Ω W Q) L h h'
            ((commonStageHomComparison.{u, v} l Ω W P L h).hom ≫
              (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).map
                (X := commonStageHomPairAtStage.{u, v} l Ω W P L h)
                (Y := commonStageHomPairAtStage.{u, v} l Ω W Q L h')
                (ObjectProperty.homMk
                  (X := commonStageHomPairAtStage.{u, v} l Ω W P L h)
                  (Y := commonStageHomPairAtStage.{u, v} l Ω W Q L h')
                  (Prod.mkHom a.op b)) ≫
              (commonStageHomComparison.{u, v} l Ω W Q L h').inv))) := by
  sorry

/-- The canonical common-stage internal Hom on precisely the permitted full subcategory.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageDerivedInternalHom (W : Scheme.{u}) :=
  (commonStageDerivedInternalHom_existsUnique l Ω W).exists.choose

end CommonStage
end WeilConjectures
