## What changed

Completed `CategoryTheory.coefficientBidualEvaluation_shift_one` in
`Sheaf.CategoryTheory.CoefficientBidualEvaluationShiftOne`, with its signature unchanged.
The proof retains the ordinary signed evaluation chain map and proves its identification
with the derived evaluation transpose. On K-flat representatives this follows from the
two existing normalized uncurrying equations, the Koszul symmetry equation and equality
on actual sheafified pure tensor generators. Naturality and K-flat replacement extend
the identification to all representatives.

The ordinary signed source shifts are supplied by `SignedDoubleHomCone.comparison`.
Their inverse projection formula, normalized derived descent and the categorical
transport of the negative double-shift composite are all proved privately. The public
proof unpacks the signed comparison once and passes its formulas to these helpers.
Essential surjectivity then gives the stated equation for every derived object.

Retained the public shift import. Private `import all` commands expose the existing
shift descent API and the existing bidual component API; the ordinary signed-comparison
module remains a private proof import. Updated the item's DAG proof, dependencies and
provenance. No public definition, target statement or source-library module changes.
There are no new modules or nodes. The unit's realized statements and proof steps stay
unchanged. The proof-context change record is
`coord/changes/P1-coefficient-bidual-evaluation-proof-context.md`.

Validation: the complete single module compiled cleanly through `lcompile.py` in
42.8 seconds. Its public theorem signature is byte-for-byte unchanged, it contains
zero `sorry` tokens, and all Lean lines are at most 100 characters. The sole direct
consumer, `Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility`, uses the
unchanged theorem and requires no adaptation.

## Proved and sorry left

Closed 1 of 1 holes: `CategoryTheory.coefficientBidualEvaluation_shift_one`
(node `lem-coef-bidual-evaluation-shift-one`). Added 0 holes; split off 0 statements.
There are no `sorry`s left in the delivered module or in its private helpers.
Existing lower library obligations used by the fixed derived Hom and K-flat replacement
are not claimed as proved by this delivery.

## No longer needed

No imports were removed.

Removed the unused private `ordinaryBidual_shift_one` existential packaging and
`generalOrdinaryBidualTransformation`; the actual ordinary chain construction,
naturality and componentwise shift calculation are retained. No existing public
signature or public import is removed. No library module is withdrawn.

The direct proof no longer needs the old separate dependencies
`lem-pur-hom-kflat-into-kinjective`, `lem-weil-pbc-kinjective-hom-derived`,
`lem-sc-derived-hom-tensor-total`, `lem-pur-rhom-well-defined`,
`lem-weil-pbc-site-derived-tensor-descent` and
`prop-pur-kinjective-resolutions-exist`. The fixed representative comparison already
handles the resolved Hom, and a K-flat quasi-isomorphism becomes an isomorphism after
localization. These nodes may remain transitive dependencies of the unchanged fixed
constructions; no global unreachability or module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The earlier module had already checked ordinary evaluation but left the fixed derived
representative identification unfinished. This delivery proves that identification
using the stated coefficient-specific normalization fields, including evaluation at
the identity of each localized site and the Koszul sign. It does not assume ordinary
Hom into the unresolved coefficient computes derived Hom.

An initial preflight refused a proposed import of the retired generic relative-bidual
triangle module. That route has been removed completely: the delivery now supplies the
coefficient-specific argument described above. The required proof-context change record
also repairs the initial command-change gate finding. There is no disputed statement,
new unfinished lemma or forced adaptation of another group's module. Mathlib searches
found cochain shift APIs but no theorem with the required normalized sheaf-Hom equation.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
