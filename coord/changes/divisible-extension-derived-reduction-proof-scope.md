# Sheaf.Paper.DivisibleExtensionDerivedReduction proof-scope commands

## Reason

The proof adds a private helper theorem for finite colimits. Its `omit` command
and a scoped `set_option linter.unusedSectionVars false` command change the
module command environment, so stage-3 preflight requires this record.
Both commands apply to one theorem only. Existing signatures, definitions,
instances and public visibility remain unchanged.

## Old

Before the restriction exactness theorem there was no additional command:

```lean
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {Z R : Sheaf J CommRingCat.{r}} (q : Z ⟶ R)
```

## New

The same variables remain. Before the private helper the following command
omits the two unused section instances from its signature:

```lean
omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem scalarForget_preservesFiniteColimits (A : Sheaf J RingCat.{r}) :
    PreservesFiniteColimits (toSheaf.{r} A) := by
```

The proved helper uses sheafification and colimit preservation. Before the
unchanged public restriction-exactness signature, the following command
suppresses a linter diagnostic local to that theorem:

```lean
set_option linter.unusedSectionVars false in
```

The helper is private, and both scopes end at their respective theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.DivisibleExtensionDerivedReduction | C6 | Uses the private helper in the exactness proof. |
| Sheaf.Paper.GeoCartierExponentIndependence | Y9 | Same public declarations and instances; no adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | H4 | Same public declarations and instances; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | Y6 | Same public declarations and instances; no adaptation. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | T8 | Same public declarations and instances; no adaptation. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | T9 | Same public declarations and instances; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | G3 | Same public declarations and instances; no adaptation. |

`tools/downstream.py Sheaf.Paper.DivisibleExtensionDerivedReduction --uses
sheafScalarRestriction_exact` lists these six downstream modules and finds no
reference to that theorem outside the item itself. The commands are scoped to
one declaration and add no exported instance or notation. Public statements,
definitions and instance signatures are identical, so no downstream adaptation
is necessary.

## Status

landed 20261019T002518-L-2145246 2026-10-19 (merge of deliver/C6/Sheaf.Paper.DivisibleExtensionDerivedReduction)
