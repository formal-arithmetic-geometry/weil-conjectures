## What changed

Completed all three proofs in
`WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange`.

- `shriekBaseChange_refinementComparison`: completed the final pushforward-pasting and
  naturality calculation after the open cube and adjunction calculation.
- `lowerShriekBaseChange_eq`: explicitly base-changed refinements by pullback lifts, applied
  refinement compatibility to a common refinement, and used the existing `shriekIso` cocycle.
- `lowerShriekBaseChange_paste_vert`: constructed the base-changed compactification triangle,
  checked its cartesian faces by cancellation of pullback squares, proved compatibility of
  the triangle composition map, and transported it to the chosen compactifications.

Four fully proved private helpers express open cube compatibility, its adjoint exchange
identity, inverse open composition compatibility, and triangle composition compatibility.
They implement the existing interchange and mate-pasting steps, with no new public API.
The source triangle uses the chosen compactification of the second morphism directly;
no quasi-compactness assumption on that morphism is introduced.

Updated only `proof` and `proof_origin` of
`dag/nodes/sec-smooth-purity/thm-cbc-finite-torsion.json` to record this abstract realization.
Existing statements, definitions, and visibility are unchanged. Imports and proof
dependencies are unchanged. No other Lean module was adapted.
Preflight's conservative visibility check requires the change record
`coord/changes/F4-BaseChange-private-proof-helpers.md` for the section-local contexts of the
private helpers. The record documents their scope and the absence of downstream consumers.

## Proved and sorry left

Closed all three original holes:

- `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange_refinementComparison`.
- `AlgebraicGeometry.CompactSupportFormalism.lowerShriekBaseChange_eq`.
- `AlgebraicGeometry.CompactSupportFormalism.lowerShriekBaseChange_paste_vert`.

Zero holes remain in the delivered module. Zero holes were added or split off.

The complete module and the three `#print axioms` checks compiled with `lcompile.py`
without warnings in 15.7 seconds. Each of the three theorems depends only on
`propext`, `Classical.choice`, and `Quot.sound`; none depends on `sorryAx`.

## No longer needed

None. No imports were added or removed. The proof uses the existing abstract open and
pushforward pasting, adjunction, common-refinement, and comparison-cocycle APIs.
The coefficient-specific dependencies of the broad finite-torsion and exchange nodes
remain needed for their other clauses; this delivery proves their abstract formalism
identities and does not withdraw those specialized modules or nodes.

## Where the brief, the DAG or earlier work was wrong

The broad DAG nodes also describe coefficient-specific assertions, whereas this module's
three holes are generic formalism identities. Their specialized dependency statements cannot
establish an identity for arbitrary `CompactSupportFormalism`; the abstract pasting and
comparison declarations already imported by the module provide the appropriate route.
The private helper statements are elementary formal realizations of the existing interchange
and mate-pasting steps, not new mathematical assumptions. No mathematical statement was
changed, and the unit's compactification, interchange, and transport route is preserved.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
