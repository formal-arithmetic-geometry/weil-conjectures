# WeilConjectures.completedTensor_map_smul_left

## Reason

The completed-tensor linearity proof needs local scalar actions on module Hom
spaces and notation for change of rings and tensor products. Preflight treats
changes to `open`, `variable` and local attributes as interface changes and
requires this record. All added helper declarations are private, scalar-action
instances are registered only locally in the namespace, and no public definition
or statement changes. The theorem retains the original invertibility binder.

## Old

```lean
open CategoryTheory Opposite AlgebraicGeometry
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]
```

```lean
theorem completedTensor_map_smul_left
    (M M' N N' : sfIntegralConstructibleCategory l E W) (f : M ⟶ M') (g : N ⟶ N')
    (c : Padic.coefficientExtensionIntegers l E) :
    (constructibleIntegralTensor l E W).map (Prod.mkHom (c • f) g) =
      c • (constructibleIntegralTensor l E W).map (Prod.mkHom f g)
```

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct
open scoped ChangeOfRings
attribute [local irreducible] unrestrictedIntegralReductionExistence HasDerivedCategory.standard
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
```

The invertibility variable is introduced immediately before the original theorem,
after the private helpers. Its theorem signature above is unchanged. The private
definitions `moduleLinear`, `finiteSheafLinear` and `finiteLinear` are registered
with `attribute [local instance]` and marked `@[instance_reducible]`; they
provide no global instance. The private
`sectionsLinear` definition has `@[instance_reducible]` so local instance synthesis
can use its explicitly constructed sectionwise module action. Public imports are
unchanged. No target definition or statement is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedTensorScalarLinearity | E7 | Own proof is completed; public theorem statement unchanged. |

The downstream query with `--uses completedTensor_map_smul_left` found only the
item itself. No consumer source requires an adaptation. The parent blueprint's
unfinished tensor-Hom transpose proof continues to use the identical theorem.

## Status

landed 20261021T171739-L-3123262 2026-10-21 (merge of deliver/E7/Sheaf.Paper.CompletedTensorScalarLinearity)
