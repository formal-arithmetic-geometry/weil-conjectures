# relativeMV_resolved_roof_middle_mate_comparison: restore local reducibility command

## Reason

Restore the complete quarantined module for its assigned compile repair in
`coord/rework.tsv`. The archived local attribute command tries to mark
`AlgebraicGeometry.derivedPullback` irreducible even though its declaration now
uses `irreducible_def`. The full original reproduces the reported error at
line 26 through `lcompile.py` (48.8 seconds of compiler time).

Remove only `derivedPullback` from that local attribute command. It remains
globally irreducible; the other four local entries remain in place. Within the
existing proof, change four propositional `haveI` bindings to `have` and remove
one unused `Category.assoc` simp argument, as requested by the compiler's linters.
The theorem signature, docstrings, imports, comparison construction and proof
argument are preserved. No definition or target meaning changes.

The repaired full module compiles through `lcompile.py` in 48.2 seconds, exit
code 0, with no warnings. Its theorem signature and imports are textually
identical to the archive, and both versions contain zero `sorry`s.

## Old

```lean
attribute [local irreducible] derivedPullback Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit DerivedCategory.Qh RingedSpace.moduleDirectImage
```

## New

```lean
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit DerivedCategory.Qh RingedSpace.moduleDirectImage
```

## Users

`tools/downstream.py --allow-missing --uses` reports zero live downstream
modules and zero live uses of the theorem. The live Lean sources have no
direct importer of the quarantined module.
The archived direct consumer below applies the theorem with the same arguments;
the entire theorem signature is textually identical to the archive. The local
attribute command does not change the importing module's environment. No consumer
adaptation is necessary. All archived declarations and their dependencies remain
preserved; no file is withdrawn, and no source-library declaration is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofMiddleMateComparison | C1 | Restored full theorem and proof; remove redundant local attribute and five proof lint warnings. |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofOpenMateComparisons | unclaimed in local snapshot (quarantined) | Identical public theorem signature; no adaptation. |

## Status

landed 20261020T162537-L-3620166 2026-10-20 (merge of deliver/C1/Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofMiddleMateComparison)
