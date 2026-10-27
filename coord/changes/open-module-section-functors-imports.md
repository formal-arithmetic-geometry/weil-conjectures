# TopologicalSpace.Opens.open_module_section_functors: public import cleanup

## Reason

The theorem is now completely proved from the existing continuous pushforward API.
Neither module sheafification nor the project's general covering-site axioms occur
in the statements, definitions or proof. Remove their direct public imports.
The retained imports expose every declaration and instance used by this file.
No theorem signature, definition, attribute or visibility is changed.

## Old

```lean
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
```

## New

```lean
public import Mathlib.Topology.Sheaves.Module
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Sheaf.CategoryTheory.RingedSiteModules
```

## Users

`python3 tools/downstream.py Sheaf.Topology.OpenModuleSectionFunctors` reports
zero downstream Lean modules in the current source. No consumer adaptation is needed.
The parent DAG dependencies and the unit route are preserved: this item remains
available with exactly its previous declaration signatures. No target statement or
underlying definition changes meaning, so target statement review is not reopened.
`tools/import_prune_check.py` passes and the cleaned module compiles through
`lcompile.py` without warnings or errors.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Topology.OpenModuleSectionFunctors | W6 | Two unused direct public imports removed; theorem proved with unchanged signature; definitions unchanged. |

## Status

landed 20261023T135732-L-2966096 2026-10-23 (merge of deliver/W6/Sheaf.Topology.OpenModuleSectionFunctors)
