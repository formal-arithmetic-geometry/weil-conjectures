## What changed

Kept the signature, structure, and public imports of
`Sheaf.Paper.DiagonalNonTorsionBaseChange` unchanged. Its theorem now constructs
residue-field invertibility by pulling back the given global unit and evaluating
it in the residue field, obtains the two normalized Cartesian adic comparisons
from `cartesianCoefficients`, and assembles the requested structure from completed
and scalar compatibility.

Added two proof imports and two modules, each with one named open theorem:
`DiagonalCompletedPullbackCompatibility` isolates geometric pullback of the
completed class and the three completed traces at Z_l;
`DiagonalScalarPullbackCompatibility` propagates a supplied Z_l comparison through
the existing scalar-compatible Families. The second statement has no base field,
derived reduction, completion, diagonal limit, or Reference hypotheses. Neither
new theorem restates the full non-torsion result. Both retain the actual endpoint
and mate normalizations. Their docstrings and nodes describe the whole-system
argument, including the positive Cartier generator and the nonconstant Kummer
transitions.

Updated the item's proof steps and dependencies to match the Lean assembly. No
existing declaration in another module, shared definition, or public interface
was changed.

Validation: `lcompile.py --all` compiled all three final modules successfully,
with no warnings. The two open theorem bodies are each exactly `by sorry`.
Checked all referenced node IDs, the verbatim Lean signature records, the
100-character line limit, and that only `proof`, `proof_deps`, and
`proof_origin` change in the existing node. The original theorem signature was
compared verbatim against the current source.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCoefficient_nonTorsionBaseChange`
(node `lem-diagonal-nontorsion-base-change`). Its assembly proof is complete.

Added two direct holes:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCoefficient_completedPullback`
  (`lem-diagonal-completed-pullback-compatibility`).
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCoefficient_scalarPullback`
  (`lem-diagonal-scalar-pullback-compatibility`).

This is a decomposition: one original hole closed, two lower holes added, net
minus one. The item's module contains zero remaining direct holes; the delivery
contains exactly two. No completed geometric or scalar compatibility proof is
claimed. The private theorem `residue_isUnit` proves residue-field invertibility by
`IsUnit.map`; selection of the normalized root data uses the published
`cartesianCoefficients` theorem directly. No data definition has a hole.

## No longer needed

No original public import was removed. No module is withdrawn or claimed pruned.
The new modules only need the reference/diagram and pullback interfaces, rather
than the uniformizer-quotient family interface.

The original direct proof dependencies
`det-prop-diagonal-tower-system`, `sk-lem-geo-cartier`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`det-pe-topos-functoriality-inverse-image`,
`lem-weil-pbc-proetale-abelian-closed-support`, `det-prop-diagonal-tower-limit`,
`sk-lem-geo-p1-cohomology`, `det-prop-diagonal-tower-trace`,
`det-prop-sfb-qlbar-colimit-x-pullback`, `sk-prop-sfb-qlbar-colimit-x`,
`det-lem-bounded-continuity-direct-image`, and
`lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` are now dependencies of
the appropriate new step, not direct dependencies of the assembly theorem.
They are still needed by those steps and are not mathematical pruning.
`sk-prop-sfb-cartesian-coefficients` remains a direct dependency for the two
actual root comparisons, and is also used by the lower steps.

## Where the brief, the DAG or earlier work was wrong

The assigned module has a quarantine/rework record. Its current source was
restored in `lean/` before copying; the quarantine archive is preserved and is
not a withdrawal request.

The published dependency statements provide systems, limits, splittings and
coefficient comparisons, but do not themselves state the complete normalized
geometric/completion square or its propagation through the scalar diagrams.
These are the two explicit remaining obligations. Compatibility of a completed
derived arrow is obtained from the entire system and its natural comparison,
not by asserting that its separate reductions detect all derived morphisms.
The current blueprint paragraph (3) contains these geometric and scalar stages;
there are no separately numbered (3a)--(3c) paragraphs in that source file.

Checked the proposed statements on empty schemes, identity base change, and the
bottom finite field. The constructions still apply: there are no residue points
to check on an empty scheme, the identity comparisons retain their unit
normalizations, and the bottom-field integral stage uses the actual specified
coefficient map rather than identifying its ring definitionally with Z_l.
The unit route is retained; its `realized` lists are currently empty and were
not changed.

The first delivery attempt was refused for three unused-simp warnings in the
privately overlaid dependency `Sheaf.AlgebraicGeometry.SfP1ChartExchange` from
snapshot c0c6c1dbd53a01ace3cacf8b04fe35c4221e2554. The current shared source
already moves those unfoldings into `dsimp only` and removes them from the
following `simp only` list. That module is held by B2; this packet does not
adapt it. Submission was retried against the updated source.

## New nodes

`lem-diagonal-completed-pullback-compatibility`, in
`dag/nodes/sec-six-functors-basics/lem-diagonal-completed-pullback-compatibility.json`,
states only the Z_l stage. Its source and proof cover the positive Cartier roof,
whole-system pullback, specified inverse-limit comparisons, splitting inversion,
and transport by the given References.

`lem-diagonal-scalar-pullback-compatibility`, in
`dag/nodes/sec-six-functors-basics/lem-diagonal-scalar-pullback-compatibility.json`,
states propagation from a supplied Z_l pullback comparison, using the prescribed
Cartesian adic maps, to the integral, rational, and closure diagrams. Its proof
uses finite-free extension, localization and the coherent finite-field colimit.
No change record is required: all existing signatures and definitions are
unchanged, and both imports added to the item are private proof imports.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
