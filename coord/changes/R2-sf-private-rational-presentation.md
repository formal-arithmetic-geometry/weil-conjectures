# sfRecollementRationalPresentation

## Reason

Factor the existing scalar-localized presentation through a generic private construction.
The concrete inherited Hom module structures cause repeated expensive definitional
comparisons in the tensor-induction naturality proofs. Checking the same construction
with abstract category and scalar instances avoids expanding those structures.
The object, functor, counit and unit formulas are unchanged. The generic construction
and its localization comparison have complete proofs and remain private.

## Old

```lean
private def sfRecollementRationalPresentation (X : Scheme.{u})
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
    [P.openTerm.Additive] [P.closedTerm.Additive]
    [P.openTerm.Linear (Padic.coefficientExtensionIntegers l E)]
    [P.closedTerm.Linear (Padic.coefficientExtensionIntegers l E)] :
    SfRecollementPresentation (sfRationalConstructibleCategory l E X) where
  openTerm := ScalarLocalization.map _ _ _ P.openTerm
  closedTerm := ScalarLocalization.map _ _ _ P.closedTerm
  counit :=
    { app := fun K ↦ (sfRationalConstructibleLocalization l E X).map (P.counit.app K.obj)
      naturality := by
        intro K L f
        dsimp only [Functor.id_map]
        induction f using TensorProduct.induction_on with
        | zero => simp
        | tmul a f =>
          change ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ _)
              (ScalarLocalization.mapHom _ _ _ P.openTerm _ _ (a ⊗ₜ f)) =
            ScalarLocalization.composition _ _ _ _ _ _ (a ⊗ₜ f) (1 ⊗ₜ _)
          simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul,
            ScalarLocalization.composition_tmul, one_mul, mul_one]
          exact congrArg (fun z ↦ a ⊗ₜ[Padic.coefficientExtensionIntegers l E] z)
            (P.counit.naturality f)
        | add f g hf hg =>
          change ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ _)
              (ScalarLocalization.mapHom _ _ _ P.openTerm _ _ (f + g)) =
            ScalarLocalization.composition _ _ _ _ _ _ (f + g) (1 ⊗ₜ _)
          simp only [map_add, LinearMap.add_apply]
          exact congrArg₂ (· + ·) hf hg }
  unit :=
    { app := fun K ↦ (sfRationalConstructibleLocalization l E X).map (P.unit.app K.obj)
      naturality := by
        intro K L f
        dsimp only [Functor.id_map]
        induction f using TensorProduct.induction_on with
        | zero => simp
        | tmul a f =>
          change ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ _)
              (a ⊗ₜ f) =
            ScalarLocalization.composition _ _ _ _ _ _
              (ScalarLocalization.mapHom _ _ _ P.closedTerm _ _ (a ⊗ₜ f)) (1 ⊗ₜ _)
          simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul,
            ScalarLocalization.composition_tmul, one_mul, mul_one]
          exact congrArg (fun z ↦ a ⊗ₜ[Padic.coefficientExtensionIntegers l E] z)
            (P.unit.naturality f)
        | add f g hf hg =>
          change ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ _) (f + g) =
            ScalarLocalization.composition _ _ _ _ _ _
              (ScalarLocalization.mapHom _ _ _ P.closedTerm _ _ (f + g)) (1 ⊗ₜ _)
          simp only [map_add, LinearMap.add_apply]
          exact congrArg₂ (· + ·) hf hg }
```

## New

```lean
private def sfRecollementRationalPresentation (X : Scheme.{u})
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
    [P.openTerm.Additive] [P.closedTerm.Additive]
    [P.openTerm.Linear (Padic.coefficientExtensionIntegers l E)]
    [P.closedTerm.Linear (Padic.coefficientExtensionIntegers l E)] :
    SfRecollementPresentation (sfRationalConstructibleCategory l E X) :=
  scalarRecollementPresentation (Padic.coefficientExtensionIntegers l E)
    (sfIntegralConstructibleCategory l E X) (Padic.coefficientExtensionUniformizer l E) P
```

The new private `scalarRecollementPresentation` contains the former record fields
verbatim except for replacing the concrete ring/category/prime by parameters.
Its naturality proofs are the same pure-tensor and additivity calculations.
`scalarLocalizationMapIso` supplies the identity-component comparison generically,
and the generic normalization theorem proves its two comparison equations.

## Users

`tools/downstream.py Sheaf.Paper.SfOpenClosedTriangleAllStages --uses
sfRecollementRationalPresentation` reports exactly the defining module (six uses).
The declaration is private, and no public statement or definition uses it in its
signature or data. The existing integral/rational existential theorem uses it only
inside its proof. Consequently no target meaning changes and no consumer adaptation
is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | R2 | Existing private proof helpers use the generic construction; all public signatures are preserved. |

## Status

landed 20261025T181010-L-4062049 2026-10-25 (merge of deliver/R2/Sheaf.Paper.SfOpenClosedTriangleAllStages)
