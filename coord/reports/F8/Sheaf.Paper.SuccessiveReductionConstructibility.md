## What changed

Repair of the return for branch head `1173900dfaa`: removed the private theorem
`AlgebraicGeometry.ProEtale.arbitrary_encoding_comparison`, whose statement duplicated
`AlgebraicGeometry.ProEtale.finiteEncoding_constructible`. Added the proof-only import
`import all Sheaf.Paper.IntegralCriterionReductions` and used its existing theorem at
all three comparison sites. The `all` modifier gives access to that private theorem.
No copy or alias of the duplicate remains.

Retained the complete proof of
`AlgebraicGeometry.ProEtale.successiveReduction_constructible_interval`, with its
statement unchanged. The strict DVR residue-kernel sequence gives a short exact
sequence over the successor quotient by full faithful scalar restriction. Its
distinguished triangle proves constructibility by extension closure and preserves
the specified cohomological interval by exactness. Normalized finite comparisons
transport both conclusions to the continuous coefficient presentation.

The current shared base lacks this item module and its node, and has no rework row
or quarantine archive for it. This packet restores the nonempty proved module and
its retained attached node; it does not withdraw either. Updated the node's proof
text to identify the reused comparison theorem. No other Lean module is edited.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.successiveReduction_constructible_interval`
(node `lem-pe-successive-reduction-constructibility`).

Zero `sorry` remains in the item module; zero holes added; zero split off.
Relative to the retained returned proof this repair closes zero further holes:
it removes the reported duplicate while preserving the complete successor proof.
Relative to the current base this is a restoration of a module with zero holes.
Existing dependency declarations are used as required by stage 3.

The repaired file compiled through `lcompile.py` with exit code 0 in 17.6 seconds.
`tools/import_direction.py may` confirms that `IntegralCriterionReductions` does
not reach this module, so its new private proof import introduces no import cycle.
The delivery command performs the current-base preflight and axiom checks.

## No longer needed

Removed the duplicate private theorem `arbitrary_encoding_comparison`, including
its encoding-family construction and independent proof. All three uses now invoke
the existing `finiteEncoding_constructible` directly. No module is withdrawn.

The generic `lem-pe-successive-quotient-linear-triangle`
(`Sheaf.Algebra.Homology.SuccessiveQuotientLinearTriangle`) is not needed by this
proof: the existing strict DVR residue-kernel sequence gives the specialized
construction. Its regular-resolution argument is unnecessary here;
`det-pe-derived-nakayama-resolution` is used for the proved discrete-topology helper.
The K-flat resolution and derived-change-of-rings inputs come through the strict
DVR theorem and its tower API, rather than separate invocations.

The initial direct dependencies `lem-weil-l-adic-extension-absolute-value`,
`lem-weil-l-adic-extension-integers-dvr`, and `lem-weil-valued-dvr-finite-quotients`
are supplied through the coefficient API. The earlier redundant direct import
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` remains removed: the
bounded constructible triangulated API publicly supplies it. No original public
import is removed and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The returned duplicate comparison was mathematically identical to the existing
private theorem in `IntegralCriterionReductions`. This repair follows the requested
reuse exactly. That module currently has an independent unfinished criterion proof
and no reverse import or DAG dependency on this successor node. Importing its
comparison helper does not use its unfinished criterion theorem.

The residue-kernel orientation
`0 → O/pi → O/pi^(n+2) → O/pi^(n+1) → 0` is directly available in the library,
whereas the initial plan used the opposite orientation. Fullness of restriction
along the completed projection follows from sectionwise surjectivity, retaining
the finite quotient action. The proof covers `n = 0` and reversed intervals `b < a`.
The unit route and the public successor statement remain unchanged.

The proof-scope change record is
`coord/changes/F8-successive-reduction-proof-scope.md`. No consumer requires
adaptation: the item is currently absent and there is no importer in the current
shared base. Absence of importers is not treated as a withdrawal request.

## New nodes

Restored the retained `lem-pe-successive-reduction-constructibility`, originally
created by G7 for the successor induction step of the integral criterion. Its
statement, source and Lean attachment remain unchanged. The proof and dependency
list describe the complete retained proof; the first step now records reuse of
the existing comparison helper. No new mathematical lemma or hole is introduced.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
