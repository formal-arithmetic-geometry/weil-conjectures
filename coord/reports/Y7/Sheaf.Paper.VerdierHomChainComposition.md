## What changed

Repaired and proved `WeilConjectures.VerdierHomChainComposition.stage_specialization`
in `lean/Sheaf/Paper/VerdierHomChainComposition.lean`. The abstract `StageData`
projection is only an objectwise isomorphism family. Added its exact naturality
square in the test object as an explicit hypothesis. Expanded the chain on the
identity to identify `inverseComponent`, used projection naturality and the three
adjunction naturality laws to prove the formula on arbitrary test arrows, then
used `Conclusion.components` and target naturality to obtain the published exchange
and dualizing specialization. Updated the existing node's proof and recorded the
auxiliary statement correction. The main geometric composition and identity
statements, all existing definitions, and all imports are unchanged. Added two
proved private generic tensor-transpose helpers to avoid re-elaborating the large
stage categories for each tensor-coordinate conversion.

Change record: `coord/changes/Y7-verdier-stage-projection-naturality.md`.

## Proved and sorry left

The refreshed library has three original holes. Proved the corrected auxiliary
statement `WeilConjectures.VerdierHomChainComposition.stage_specialization` with
a complete proof. This is a repair of a false auxiliary statement, not a proof of
its original unrestricted signature. It uses no sorry-dependent theorem: only
adjunction naturality, inverse laws, and the supplied projection naturality.
No new holes or split-off statements were added. The hole count decreases from
3 to 2, but this statement repair is reported separately from proving an
unchanged original statement.

Two original holes remain, each with its complete existing source/proof docstring
and node `lem-sf-verdier-hom-chain-composition`:

- `WeilConjectures.VerdierHomChainComposition.verdier_hom_chain_composition`;
- `WeilConjectures.VerdierHomChainComposition.identity_exchange`.

During this session the shared source refreshed with U5's four proved declarations
(`representing_chain`, `chain_naturality`, `coefficient_transposes`, and
`composition_after_change`). Those proofs and their private helper are retained
verbatim and are not counted as this delivery's work.

## No longer needed

None. No import, node, or module is removed. The existing geometric composition
and identity proof plans and the unit route remain intact.

## Where the brief, the DAG or earlier work was wrong

The old `stage_specialization` was false for an arbitrary objectwise projection
family: for identity operations on a characteristic-zero point, keep projection
fixed at the one-dimensional representing object but multiply it by -1 at a
two-dimensional test. Its chain on a nonzero test arrow changes sign while its
identity-test `inverseComponent` is unchanged. This was already documented by U5.
The added hypothesis is the actual canonical projection's naturality square, not
a hypothesis on the chain's conclusion. The proof uses it exactly once to move
the test arrow across projection.

The downstream scan reports zero downstream Lean modules and only the defining
module as a textual use of `stage_specialization`. The sole DAG parent is
`fix-prop-coherence`, which uses the canonical natural projection, so its use holds.
No target meaning or definition changes and no consumer adaptation is required.

Validation: remote single-file compilation succeeded in 59.9 seconds with no
errors or warnings. The two generic private helpers are fully proved. The
specialization theorem uses projection naturality and standard adjunction laws;
the delivery probe will report its axioms. All Lean lines are at most 100 characters.
The timing/profile diagnostics were removed from the delivered file.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
