# AlgebraicGeometry.ProEtale.reductionSiteCoefficientPasting

## Reason

Use the already stated mixed-endpoint coefficient/site square in the exceptional
chart proof. Its old import of ReductionExceptional creates a cycle through
ReductionExceptionalChart, whose proof now needs that square. All names in the
statement belong to ReductionExceptionalObjects or its public imports. This is the
objects interface extracted by K5 specifically to allow these proof dependencies.
The module was unclaimed in the current server claim records on 2026-10-28.
The matching node still cited `det-sp-reduction-exceptional` for the constructed
objects, although the 2026-10-25 extraction gives those objects their own node.
Keeping that old citation creates a DAG cycle through the exceptional theorem's
chart dependency. Correcting the citation is part of the same import repair.

## Old

```lean
public import Sheaf.SecSmoothPurity.ReductionExceptional
```

The node `lem-sp-reduction-site-coefficient-pasting` cites
`det-sp-reduction-exceptional` in its statement, `stmt_deps`, first proof step's
`uses`, and `proof_deps`, as the location of the intrinsic comparison family.

## New

```lean
public import Sheaf.SecSmoothPurity.ReductionExceptionalObjects
```

The node now cites `def-sp-reduction-exceptional-realization-objects` at those
four places, matching the actual extracted constructions. Its `statement_change`
records the old fields and audits every current citer, including the new descent
node. All uses remain valid because the mathematical assertion is identical.

The theorem, its visibility, Lean statement, proof and attributes are verbatim. No
construction or target meaning changes. The module no longer reexports the
exceptional comparison theorem and its proof dependencies.

## Users

`tools/downstream.py Sheaf.Paper.ReductionSiteCoefficientPasting --uses
reductionSiteCoefficientPasting` finds one user besides the declaration module.
The import scan finds the same single direct importer. There are 249 transitive
importers; all paths from them go through the direct importer below, which itself
publicly imports ReductionExceptional and therefore retains the earlier exports.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ReductionSiteCoefficientPasting | unclaimed | Import and matching definition-node citations corrected; Lean assertion unchanged. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed | Already imports ReductionExceptional publicly; its unchanged source compiled against the replacement import (36.4 s, exit 0). |
| Sheaf.SecSmoothPurity.ReductionExceptionalCounitDescent | F2, new | Uses the existing square to prove ordinary counit descent. |
| Sheaf.SecSmoothPurity.ReductionExceptionalChart | F2 | Uses the proved descent lemma; original statement unchanged. |

The existing citer `lem-pur-etale-affine-projection-coefficient-mate` still uses
the identical square. The new `lem-sp-reduction-counit-descent` uses the same square
to reflect the counit equation. Neither use requires the exceptional-isomorphism
theorem. No target statement or definition changes.

## Status

landed 20261027T205939-L-1636634 2026-10-27 (merge of deliver/F2/Sheaf.SecSmoothPurity.ReductionExceptionalChart)
