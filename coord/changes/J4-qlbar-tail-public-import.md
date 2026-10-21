# Sheaf.Paper.QlbarTailModuleColimit public imports

## Reason

Remove the unused public import of `Sheaf.Paper.FiniteSubextensionsDirected` while
proving the coefficient module colimit. Its five-part theorem is not needed by any
statement, definition or proof in this module. The existing directed-order instance on
`PadicAlgCl.FiniteIntermediateField` already provides common upper bounds. This also
removes an unnecessary sorry-bearing dependency from this module's import closure.
The original stage-2 review explicitly recorded that this public import was unused.

The proof-only imports of `Sheaf.Paper.CompletedCondensedCoefficients` and
`Sheaf.CategoryTheory.DirectedRingSheafModuleColimit` are removed for the reasons in the
report. The coefficient-colimit step of the unit route remains: the proof calls
`AlgebraicGeometry.ProEtale.isColimitPadicAlgClRingObjCocone` directly, with the actual
inclusion legs. This is the already proved abelian coefficient colimit underlying the
third comparison of `sk-prop-sfb-qlbar-colimit-x`; no different coefficient construction or
replacement of the unit's argument is involved.

## Old

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.FiniteSubextensionsDirected
```

## New

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.RingedSiteModules
```

All existing declaration signatures and both public abbreviation bodies are verbatim.
No definition changes its meaning. No target or downstream statement is altered.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QlbarTailModuleColimit | J4 | Removes unused re-export; proves the existing theorem. |

`python3 tools/downstream.py Sheaf.Paper.QlbarTailModuleColimit` reports
`0 module(s) downstream`. The shared Lean sources contain no importer of this module.
A whole-library
text search finds no use of `finiteSubextensions_directed` outside its defining module.
Consequently no consumer requires an adaptation. The DAG parents, including
`lem-sfb-qlbar-flat`, continue to have the same module-colimit statement available;
none of their declarations is changed or withdrawn. The module and its Lean attachment
are retained.

## Status

landed 20261021T101150-L-19788 2026-10-21 (merge of deliver/J4/Sheaf.Paper.QlbarTailModuleColimit)
