# AlgebraicGeometry.ringComplex_godement_cech

## Reason

Document proof-scope commands added for the completed assembly and private helpers.
No existing definition, declaration signature, public import, instance or persistent
attribute changes. The new modules supply a concrete ordered Čech fibre and two
strictly smaller proof obligations; their declarations have their own DAG nodes.

## Old

```lean
theorem ringComplex_godement_cech (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (RingSiteModules A)] (I : {I : Ideal A // I.FG}) :
    RingComplexHasCechModel A I.val (ringComplexGodement A I.val)
      (ringComplexGodementAugmentation A I.val) := by sorry
```

The original scope commands were `open CategoryTheory` and
`namespace AlgebraicGeometry`.

## New

```lean
theorem ringComplex_godement_cech (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (RingSiteModules A)] (I : {I : Ideal A // I.FG}) :
    RingComplexHasCechModel A I.val (ringComplexGodement A I.val)
      (ringComplexGodementAugmentation A I.val) := by
```

The body now assembles the augmented derived comparison. Scope commands add
`CategoryTheory.Limits Opposite` to the open namespaces, and `noncomputable section`
around the private constructions. These commands do not change exported declarations.
All added helpers are private and completely proved. All added imports of the item
are proof imports. The three new modules preserve the prescribed Godement object
and augmentation and construct the Čech fibre directly, with no hollow definition.
No consumer changes meaning and no target review is reopened.

## Users

`tools/downstream.py Sheaf.Paper.RingComplexGodementCech --uses
ringComplex_godement_cech` lists the item and RingComplexFunctorial as textual users
(the source search also finds the explanatory docstring in
FunctorialRingComplexCechComparison). Its import closure has 3771 downstream modules;
all see the same public interface, so none needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingComplexGodementCech | Y3 | Upper hole assembled from two smaller obligations. |
| Sheaf.Paper.RingComplexFunctorial | unclaimed | Same theorem signature and public imports; no adaptation. |
| Sheaf.Paper.FunctorialRingComplexCechComparison | V6 | Same theorem signature and public imports; no adaptation. |

## Status

landed 20261025T144342-L-1231608 2026-10-25 (merge of deliver/Y3/Sheaf.Paper.RingComplexGodementCech)
