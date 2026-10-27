# SemilinearClopenUnitProjector proof-local attributes

## Reason

The stage-3 static check requires this record for the additional `attribute`,
`variable`, and section commands. They support private proof helpers and control
elaboration of the exact-derived and coefficient comparison models. Every new
attribute is explicitly local. No existing public signature, definition body,
visibility, or public import changes, and no attribute persists in an importer.
The full file compiles without warnings in 57.8 seconds after replacing an
expensive simp calculation by an explicit inverse-uniqueness proof.

## Old

No proof-local attribute commands occur in the original item module. Its existing
public statements and definitions, including `clopenToDirect`, `clopenPi`, the
coefficient comparisons, and scalar comparisons, retain their text verbatim.

## New

The additional local attribute commands are:

```lean
attribute [local irreducible] exactAdj Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  Functor.rightDerivedFunctor
attribute [local irreducible] clopenToDirect
attribute [local irreducible] clopenCoefficientScalar
attribute [local instance] prodOpenContinuous baseChange_continuous
attribute [local instance] openRingTranspose_isIso
attribute [local irreducible] clopenCoefficientG
attribute [local irreducible] clopenCoefficientScalar clopenCoefficientG
```

`LocalizedMaps` is a new private-helper section with explicit category, abelian,
additive, exactness, and derived-category variables. It closes before the next
public declaration. The helpers never occur in existing public definition bodies
or signatures. The scalar and G barriers are repeated after `end Coefficients`
to cover the final theorem. `clopenCoefficientP_isIso` is proved before
`clopenCoefficientJInv_isIso` to use the former in the latter; both signatures and
visibility remain identical. The `Coefficients` section is the original section.
The additional import-all access and the complementary-component import are
private proof imports. The four removed private imports are listed in report.md.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector | R8 | Nine theorem proofs; private helpers and local attributes |

`tools/downstream.py Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector` reports
zero current Lean downstream modules. DAG parents may still need this statement;
the item and its Lean attachment are preserved. No consumer adaptations are
needed because every public signature, definition and public import is unchanged.

## Status

landed 20261024T020119-L-2550527 2026-10-24 (merge of deliver/R8/Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector)
