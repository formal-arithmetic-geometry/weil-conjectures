# Two-colimit private proof-helper restoration

## Reason

Restore the quarantined module named in `coord/rework.tsv`. Its original error was
`Unknown identifier factors`: the helper is private to `CondensedFiniteModelProofAPI`.
The restored archive also needs explicit graded-tensor instances when constructing the
exact-derived comparison, and its final scoped `set_option ... in` incorrectly scopes
an `end` command. The repair preserves all archived declaration signatures, proof routes,
definition bodies, and public imports. It changes no target meaning.

## Old

```lean
public import Sheaf.Paper.CondensedFiniteModelProofAPI
```

Private `algClDerivedIso` used `leftDerivedFunctorIsoMapDerivedCategory` without
providing the higher-order graded-tensor instances. The final commands were:

```lean
set_option linter.unusedSectionVars false in
end TwoColimit

end AlgebraicGeometry.ProEtale
```

## New

Keep the public import and add a private proof import:

```lean
import all Sheaf.Paper.CondensedFiniteModelProofAPI
```

Add proved private instances `moduleTensorFour`, `moduleTensorLeft`,
`moduleTensorRight`, `moduleTensorColimits`, `moduleTensorFlipColimits`, and
`moduleFlatResolution`, each by
`infer_instance`. The three graded-tensor wrappers are already used in
`Sheaf.Paper.CondensedFiniteModelExtensions`. The additional two wrappers package existing preservation of integer-indexed
colimits by left and right tensoring, as in `CondensedFlatCoefficientCalculus`.
The flat-resolution wrapper similarly caches the module-category instance. Add
private imports of `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`
and `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`.
These package existing instances for the higher-order arguments of the exact-derived comparison. Remove the dangling
scoped option before `end TwoColimit`. Set `autoImplicit false`, wrap the extracted-module
comment, and disable only the private-module linter, since this module deliberately
contains private support declarations. No existing declarations are removed.

## Users

`tools/downstream.py --allow-missing` lists the following consumers. A direct search
of live and quarantined sources also finds the archived `CoefficientFiniteDescentHom`
import. All archived public imports and signatures are retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | Archived public imports and all signatures preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Transitive consumer; no interface change. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Transitive consumer; no interface change. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Transitive consumer; no interface change. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Transitive consumer; no interface change. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Transitive consumer; no interface change. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Transitive consumer; no interface change. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | A2 | Restore and repair the assigned module. |

There is no node attached to this extracted private-only module; the original public
statements remain attached to the unchanged upstream module. No node attachment or
dependency is removed, and no unit route changes. Independent delivery review applies.

## Status

landed 20261021T140746-L-2739619 2026-10-21 (merge of deliver/A2/Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit)
