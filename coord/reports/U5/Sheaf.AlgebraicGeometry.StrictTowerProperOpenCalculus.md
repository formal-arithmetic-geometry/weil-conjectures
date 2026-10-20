## What changed

Filled `pi_components`, `beta_id`, and `gamma_identities` in
`Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`, preserving every public statement.

The projection proof uses the adjoint triple for the image equation. For the complementary
open, the ringed-open comparison reduces restriction of a disjoint direct image to sections
on empty test schemes. Adjunction gives the corresponding vanishing for extension by zero;
termwise extension and exact derived localization preserve this zero-object calculation.
No faithfulness of derived evaluation is used.

The identity proofs first establish sectionwise direct-image compositor unit equations,
transfer them to module pullback by uniqueness of adjoints, and then lift them to strict
towers and their derived categories. Transposition gives the two beta identity equations.
The existing `alpha_cartesian` statement reduces the identity alpha squares to these equations;
abstract mate-pasting gives the specified gamma identity normalizations.

Added private, proved helpers and proof-only imports of adjoint triples, the ringed-open
comparison and its implementation, the slice pullback unit equations, and derived compositor
coherence. Updated the existing node's proof description and recorded the ringed-open
comparison dependency. No public definitions or signatures changed, and no consumer
adaptations or new nodes are needed. The preflight-required record
`coord/changes/U5-strict-tower-calculus-proof-settings.md` documents the private
constructions and scoped elaboration commands, with the complete downstream consumer list.

Validation: the complete delivered Lean module compiles through `lcompile.py` without errors
or warnings. The delivery compile and axiom probe also pass. No diagnostic heartbeat
or profiler options remain.

## Proved and sorry left

Closed 3 of the item's original 10 holes, with 0 holes added and 0 split off:

- `AlgebraicGeometry.ProEtale.StrictTower.pi_components`
- `AlgebraicGeometry.ProEtale.StrictTower.beta_id`
- `AlgebraicGeometry.ProEtale.StrictTower.gamma_identities`

The following 7 original holes remain, all attached to
`lem-cbc-strict-tower-proper-open-calculus`:

- `AlgebraicGeometry.ProEtale.StrictTower.alpha_cartesian`
- `AlgebraicGeometry.ProEtale.StrictTower.beta_comp`
- `AlgebraicGeometry.ProEtale.StrictTower.beta_open_comp`
- `AlgebraicGeometry.ProEtale.StrictTower.alpha_vertical`
- `AlgebraicGeometry.ProEtale.StrictTower.alpha_horizontal`
- `AlgebraicGeometry.ProEtale.StrictTower.alpha_baseChange`
- `AlgebraicGeometry.ProEtale.StrictTower.gamma_evaluation`

`gamma_identities` uses the existing, still-unproved `alpha_cartesian`; its two beta
normalization inputs and its abstract mate calculations are proved in this delivery.
The pre-existing proofs of `gamma_isIso` and `normalizedProperOpenCalculus` are preserved
and are not counted among the holes closed here. Every new private helper is proved.

## No longer needed

None. No existing imports, nodes, modules, or unit steps are withdrawn. The remaining
geometric and finite-comparison dependencies still belong to the unfinished statements.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or definition repair. The existing declarations of normalized
comparators suffice; their actual identity equations require the sectionwise unit laws
and their transfer through the tower and derived constructions, now supplied as private
proved helpers. All statements retain the original arbitrary-ring hypotheses.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
