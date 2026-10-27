# CategoryTheory.FiniteFilteredDerived.filteredFunctorGradedComparison

## Reason

The item proof adds proved private helpers. Some helpers do not require the
ambient `IsTriangulated` instance, so declaration-local `omit ... in` commands
avoid unused-section-variable warnings. The static visibility checker treats
these new scoping commands as a possible public-interface change and requires
this record. No original variable, namespace, open command, signature,
definition, attribute, or public import is changed.

## Old

There were no private helper declarations or helper-local `omit ... in`
commands in this module. Its original section context was:

```lean
variable {I : Type z} (C : I → Type u) [∀ i : I, Category.{v} (C i)]
  [∀ i : I, Abelian (C i)] [∀ i : I, HasDerivedCategory.{w} (C i)]
  (D : I → Type u') [∀ i : I, Category.{v'} (D i)]
  [∀ i : I, HasShift (D i) ℤ] [∀ i : I, Preadditive (D i)]
  [∀ i : I, HasZeroObject (D i)]
  [∀ (i : I) (n : ℤ), (shiftFunctor (D i) n).Additive]
  [∀ i : I, Pretriangulated (D i)] [∀ i : I, IsTriangulated (D i)]
  (P : ∀ i : I, Presentation (C := C i) (D := D i))
```

## New

The original context above and every original declaration signature and
non-theorem body remain verbatim. Each applicable new private helper has the
following declaration-local prefix:

```lean
omit [∀ i : I, IsTriangulated (D i)] in
```

It applies only to the immediately following private helper and has no effect
on the original public theorem's binders. Public definitions `Lift`,
`LiftsTransformation`, `identityLift`, and `composeLift` remain verbatim.
The original theorem statement was compared textually with the sandbox statement
and is identical. Only its proof is replaced.

## Users

`tools/downstream.py Sheaf.CategoryTheory.FilteredFunctorGradedComparison --uses
filteredFunctorGradedComparison` lists one downstream module and no external
named use of the theorem. The current claims contain no holder for that module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FilteredFunctorGradedComparison | Y9 | proved private helpers and completed theorem proof; original public interface unchanged |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | no adaptation; original public interface unchanged |

No target definition or statement changes, and no target statement review is
reopened by these private proof helpers. The two new supporting modules have
matching new DAG nodes and require no consumer adaptation.

## Status

landed 20261023T135758-L-2971959 2026-10-23 (merge of deliver/Y9/Sheaf.CategoryTheory.FilteredFunctorGradedComparison)
