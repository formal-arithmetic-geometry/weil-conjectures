## What changed

Completed `AlgebraicGeometry.ProEtale.StrictTower.properOpen_clopen_projector` in
`Sheaf.AlgebraicGeometry.ProperOpenClopenProjector`, preserving its statement and
all existing declarations. The displayed alpha word is its definition. The
cartesian lift is the canonical pullback isomorphism. Its inverse-image functor
is faithful by the inverse-map compositor and identity comparison, so the
projector restriction equation and adjunction triangle prove that projector
followed by open counit is identity. Source factorization of the specified
inverse beta then cancels the alpha word to beta. Generic private lemmas compute
whiskered components and cancel compositors before specialization to the derived
functors, keeping kernel conversion away from their large concrete definitions.
The section case uses the already proved derived projector restrictions and pullback projection equation.

Added the proved source-factorization theorem
`AlgebraicGeometry.ProEtale.StrictTower.betaInv_source_factorization` in
`Sheaf.AlgebraicGeometry.OpenBetaSourceFactorization`. It applies to arbitrary
commuting squares factored through an open, with no cartesianness, closedness,
properness or quasi-compactness assumption. Its proof transposes under the
composite open adjunction, uses the conjugate compositor unit equation, and
calculates the two inverse-image compositor associativity equations first for a
generic coherent family, then specializes to the existing concrete system.
Both imported coherence modules are independent of the item; import-direction
checks confirm no cycle.

The new module is a proof-only import of the item. Existing public imports,
statements, definitions and their visibility are unchanged. The node's last
proof step and proof dependencies now describe the actual cancellation argument.

Validation: the server compiled both delivered modules in import order: the new
source-factorization module in 13.5 seconds and the item module in 37.4 seconds.
Both are below the per-file limit, with no `sorry` warnings.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.StrictTower.properOpen_clopen_projector`
(node `lem-cbc-proper-open-clopen-projector`).

Added no holes. The new
`AlgebraicGeometry.ProEtale.StrictTower.betaInv_source_factorization`
(node `lem-cbc-open-beta-source-factorization`) is proved. No `sorry` remains in
either delivered Lean module. This is a proof, not a decomposition.

## No longer needed

Removed no existing Lean import: the earlier section, module, tower and derived
proofs still use the module's existing imports. The new proof does not import
`Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization`, and the parent node drops
`lem-cbc-tower-open-beta-normalization` from its proof dependencies. Directly
transposing the specified beta avoids its additional section and finite
coefficient comparisons. This is local pruning only: that module and node have
other consumers and are not withdrawn.

The `alpha_cartesian` theorem of
`Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` cannot be imported for
this proof: its proof applies this item's theorem. No source-library declaration
is removed or modified. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The final DAG step described transport to the identity informally and called it
elementary. Its Lean content includes a genuine normalized-transpose coherence
calculation. This is now made explicit in the proved source-factorization theorem
and the projector-counit cancellation, with the same hypotheses and conclusion.

A development compile of the new square calculation unfolded large derived
functor definitions and exceeded the file limit. Local irreducibility and a generic
coherent-family calculation, specialized only after the cancellation proof, avoid
that unfolding; no limits are raised and no definition or public interface is
changed. The new module uses the default transparency settings. The
source-factorization statement uses the inverse equality isomorphism directly, so it matches the alpha word without a concrete transport rewrite. The
alpha word is canceled as a natural transformation by a generic proved lemma,
before specializing its components to the derived categories.

## New nodes

`lem-cbc-open-beta-source-factorization` states only the source-open
factorization of inverse beta, a strict part of the parent argument. Its source
is Stacks 03DI, 07A7 and the open-factorization calculation of 0F7B in parent step
8. LeanFinder, Loogle, Mathlib grep and project/source searches found no existing
noncircular theorem for this precise normalization. It is proved from the existing
strict-tower compositor coherence and open adjunctions; no new unproved lemma,
new operation, or alternative coefficient category is introduced. The assertion
also handles empty opens and arbitrary coefficient rings. No change record is
needed: no existing public signature, import, attribute or definition changes.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
