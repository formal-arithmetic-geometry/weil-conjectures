# GeometricStalkPerfect proof elaboration commands

## Reason

The proof-only import of the point-sections module exposes a standard, larger
module-derived-category instance. Its polymorphic site-smallness instance also
leaves an unwanted universe metavariable during geometric-point flatness inference.
For each of the four existing theorem commands, disable these two instances with
`attribute ... in`. The theorem proof explicitly supplies the small derived-category
instances when needed. The attribute changes end with the theorem command and do
not change imported instances for consumers. Additional options control elaboration
and the have/let linter in this file only. Preflight classifies these new top-level
commands as an interface change, so this record documents them for independent review.
No existing declaration signature or definition body changes.

## Old

The original module has only this option before its universe declaration:

```lean
set_option autoImplicit false
```

The four theorem commands have no preceding instance-attribute wrapper.

## New

```lean
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Immediately before the docstring of each of the four existing theorem commands:

```lean
attribute [-instance] WeilConjectures.pointReductionModuleDerived
  WeilConjectures.scalarReductionSiteSmall in
```

All theorem signatures and the complete `fieldGeometricStalkComplex` definition
remain verbatim. New helpers are private or belong to the two new Sheaf modules.

## Users

`tools/downstream.py Sheaf.Paper.GeometricStalkPerfect --uses` with each of the
four theorem names finds only their own declarations in this module. Its complete
import-consumer list has one module, also included below. No consumer adaptation is
needed: there is no exported instance or declaration change.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.GeometricStalkPerfect | T5 | Proof elaboration only; four bodies filled. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | R9 | Imports the module but mentions none of the four theorems; no effect. |

## Status

landed 20261021T143958-L-31526 2026-10-21 (merge of deliver/T5/Sheaf.Paper.GeometricStalkPerfect)
