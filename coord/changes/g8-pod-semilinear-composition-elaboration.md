# Sheaf.Paper.SemilinearFieldOperationLifts composition proof context

## Reason

Repair the consumer timeout reported for returned head f5f20330e9b. The unchanged
consumer reaches the 120-second diagnostic cutoff both against the published
library and against G8's item. Its import header takes 4.5 seconds; the prefix
through rational composition takes 24.9 seconds, but the prefix including common
composition times out. Cached category and Hom wrappers, as used by the existing
DerivedPullbackTensorIso operation interface and its J4 elaboration repair, keep
the stage system and localized Hom implementations abstract during this proof.
The clean repaired module compiles in 25.5 seconds, without errors or warnings. The explicit map-domain and scalar annotations below retain the
existing localized formula; the scalar is in Localization.Away of the coefficient
uniformizer, exactly as in the recorded rational category. The private proof
unfolds only the named pullback definition when projecting its specification.

No public signature, universe, binder, definition body, import, docstring,
exported instance or attribute changes. Every public theorem proof stays
verbatim. The existing proof dependencies and all mathematical steps are retained.
The added attributes and options end with the new local section. No target or
mathematical meaning changes, and no new statement or hole is introduced.

## Old

The old private declaration, verbatim:

```lean
private theorem pod_rational_composition_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [_root_.Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (h : Z ⟶ X)
    {K L : sfRationalConstructibleCategory l E Y} (a : K ⟶ L) :
    (rationalDerivedPullback l E (h ≫ f)).map a ≫
        (pullbackTensorRationalComposition l E f h L).hom =
      (pullbackTensorRationalComposition l E f h K).hom ≫
        (rationalDerivedPullback l E h).map ((rationalDerivedPullback l E f).map a) := by
  have obj {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M : sfRationalConstructibleCategory l E W) :
      (rationalDerivedPullback l E g).obj M =
        ⟨(constructibleIntegralPullback l E g).obj M.obj⟩ :=
    (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 M
  have hom {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)] (M N) (b : M ⟶ N) (c) :=
    (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.2 M N b c
  have : (rationalDerivedPullback l E (h ≫ f)).Additive :=
    (rationalDerivedPullback_existsUnique l E (h ≫ f)).exists.choose_spec.1
  have : (rationalDerivedPullback l E f).Additive :=
    (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.1
  have : (rationalDerivedPullback l E h).Additive :=
    (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.1
  have compobj (M) : (rationalDerivedPullback l E h).obj
      ((rationalDerivedPullback l E f).obj M) =
      ⟨(constructibleIntegralPullback l E h).obj
        ((constructibleIntegralPullback l E f).obj M.obj)⟩ := by
    rw [obj, obj]
  have hc (M) := (pullbackTensorRationalComposition_existsUnique l E f h M).exists.choose_spec
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    have hm := (pod_map_heq (rationalDerivedPullback l E h) (obj f K) (obj f L)
      (hom f K.obj L.obj a c)).trans
        (hom h _ _ ((constructibleIntegralPullback l E f).map a) c)
    have hleft := heq_comp (obj (h ≫ f) K) (obj (h ≫ f) L) (compobj L)
      (hom (h ≫ f) K.obj L.obj a c) (hc L)
    have hright := heq_comp (obj (h ≫ f) K) (compobj K) (compobj L) (hc K) hm
    apply eq_of_heq
    refine hleft.trans (HEq.trans ?_ hright.symm)
    apply heq_of_eq
    change ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ (pullbackTensorIntegralComposition l E f h).hom.app L.obj)
        (c ⊗ₜ (constructibleIntegralPullback l E (h ≫ f)).map a) =
      ScalarLocalization.composition _ _ _ _ _ _
        (c ⊗ₜ (constructibleIntegralPullback l E h).map
          ((constructibleIntegralPullback l E f).map a))
        (1 ⊗ₜ (pullbackTensorIntegralComposition l E f h).hom.app K.obj)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
    exact congrArg (fun b ↦ c ⊗ₜ b)
      ((pullbackTensorIntegralComposition l E f h).hom.naturality a)
  | add a b ha hb =>
    change (rationalDerivedPullback l E (h ≫ f)).map (a + b : K ⟶ L) ≫ _ =
      _ ≫ (rationalDerivedPullback l E h).map
        ((rationalDerivedPullback l E f).map (a + b : K ⟶ L))
    rw [Functor.map_add, Functor.map_add, Functor.map_add,
      Preadditive.add_comp, Preadditive.comp_add, ha, hb]
```

The old context uses respectTransparency=false, with the existing pullback
barrier only after the rational proof. It has no category-wrapper cache section.

## New

Add sequential elaboration (`set_option Elab.async false`) and the following
local section before the two square-component definitions:

```lean
section CompositionElaboration
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] commonStagePullbackComparison rationalDerivedPullback
  commonStageDerivedPullback Scheme.residueField

attribute [local irreducible] rationalDerivedInternalHom commonStageDerivedInternalHom

-- Retain the category wrappers used by the common-stage operation interface.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

attribute [local irreducible] sfIntegralConstructible Linear.homModule
  ObjectProperty.FullSubcategory.category
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
```

After the rational proof, add local barriers for Preadditive.homGroup and
ScalarLocalization.category/linear, retaining the concrete tensor addition
while proving rational composition. The section ends after pod_actual_pullback_field_lifts, before the
existing D/l/hl/T0 variables, so the later transport specifications retain their
original proof context. Move the old pullback barrier into this section.

The same private declaration with explicit specification projections:

```lean
private theorem pod_rational_composition_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [_root_.Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (h : Z ⟶ X)
    {K L : sfRationalConstructibleCategory l E Y} (a : K ⟶ L) :
    (rationalDerivedPullback l E (h ≫ f)).map a ≫
        (pullbackTensorRationalComposition l E f h L).hom =
      (pullbackTensorRationalComposition l E f h K).hom ≫
        (rationalDerivedPullback l E h).map ((rationalDerivedPullback l E f).map a) := by
  have obj {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M : sfRationalConstructibleCategory l E W) :
      (rationalDerivedPullback l E g).obj M =
        ⟨(constructibleIntegralPullback l E g).obj M.obj⟩ :=
    by
      unfold rationalDerivedPullback
      exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 M
  have hom {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M N : sfIntegralConstructibleCategory l E W) (b : M ⟶ N)
      (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq ((rationalDerivedPullback l E g).map (X := ⟨M⟩) (Y := ⟨N⟩)
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] b))
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (constructibleIntegralPullback l E g).map b) := by
    unfold rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.2 M N b c
  have : (rationalDerivedPullback l E (h ≫ f)).Additive :=
    by
      unfold rationalDerivedPullback
      exact (rationalDerivedPullback_existsUnique l E (h ≫ f)).exists.choose_spec.1
  have : (rationalDerivedPullback l E f).Additive :=
    by
      unfold rationalDerivedPullback
      exact (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.1
  have : (rationalDerivedPullback l E h).Additive :=
    by
      unfold rationalDerivedPullback
      exact (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.1
  have compobj (M) : (rationalDerivedPullback l E h).obj
      ((rationalDerivedPullback l E f).obj M) =
      ⟨(constructibleIntegralPullback l E h).obj
        ((constructibleIntegralPullback l E f).obj M.obj)⟩ := by
    rw [obj, obj]
  have hc (M) := (pullbackTensorRationalComposition_existsUnique l E f h M).exists.choose_spec
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    have hm := (pod_map_heq (rationalDerivedPullback l E h) (obj f K) (obj f L)
      (hom f K.obj L.obj a c)).trans
        (hom h _ _ ((constructibleIntegralPullback l E f).map a) c)
    have hleft := heq_comp (obj (h ≫ f) K) (obj (h ≫ f) L) (compobj L)
      (hom (h ≫ f) K.obj L.obj a c) (hc L)
    have hright := heq_comp (obj (h ≫ f) K) (compobj K) (compobj L) (hc K) hm
    apply eq_of_heq
    refine hleft.trans (HEq.trans ?_ hright.symm)
    apply heq_of_eq
    change ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ (pullbackTensorIntegralComposition l E f h).hom.app L.obj)
        (c ⊗ₜ (constructibleIntegralPullback l E (h ≫ f)).map a) =
      ScalarLocalization.composition _ _ _ _ _ _
        (c ⊗ₜ (constructibleIntegralPullback l E h).map
          ((constructibleIntegralPullback l E f).map a))
        (1 ⊗ₜ (pullbackTensorIntegralComposition l E f h).hom.app K.obj)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
    exact congrArg (fun b ↦ c ⊗ₜ b)
      ((pullbackTensorIntegralComposition l E f h).hom.naturality a)
  | add a b ha hb =>
    change (rationalDerivedPullback l E (h ≫ f)).map (a + b : K ⟶ L) ≫ _ =
      _ ≫ (rationalDerivedPullback l E h).map
        ((rationalDerivedPullback l E f).map (a + b : K ⟶ L))
    rw [Functor.map_add, Functor.map_add, Functor.map_add,
      Preadditive.add_comp, Preadditive.comp_add, ha, hb]

```

## Users

The local elaboration context does not propagate to importers. The seven direct
importers listed here keep the same statements. The field shift module needs
only its separately recorded local elaboration repair.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Local proof elaboration repair; public interface unchanged. |
| Sheaf.Paper.CommonConstantUnitFrobenius | unclaimed | Unchanged public interface; no adaptation required. |
| Sheaf.Paper.CommonFrobeniusSquareNormalization | unclaimed | Unchanged public interface; no adaptation required. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed | Unchanged public interface; no adaptation required. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | unclaimed | Unchanged public interface; no adaptation required. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Local elaboration repair in g8-field-weil-shriek-sequential-elaboration.md; API unchanged. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Unchanged public interface; no adaptation required. |
| Sheaf.SixFunctors.CoefWeilExceptionalCompatibility | unclaimed | Unchanged public interface; no adaptation required. |

## Status

landed 20261027T233952-L-4145821 2026-10-27 (merge of deliver/G8/Sheaf.Paper.PodReindexingHomCoefficientDescent)
