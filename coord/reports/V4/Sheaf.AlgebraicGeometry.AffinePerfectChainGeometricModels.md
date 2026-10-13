## What changed

Replaced the existing hole in
`AlgebraicGeometry.exists_affinePerfectChainGeometricModels` with a complete Lean reduction.
The proof obtains the derived equivalence induced by `Y.isoSpec.symm`, transports the
localized-open derived categories, preserves perfectness under the inverse equivalence,
and uses perfectness to obtain quasi-coherent derived objects. It applies
`perfect_iff_affine_bounded_projective` separately to construct genuine projective models
and their tilde-model isomorphisms. Those are passed to the new specified-model comparison.
The returned explicit scalar extensions and comparison equations give the witnesses.
The existing theorem's signature and its public imports are unchanged.

The new module is `Sheaf.AlgebraicGeometry.AffineSpecifiedModelChainComparison`.
This is a reduction of the initial-model construction, not a sorry-free proof of all
base-change geometry. No definition selects arbitrary data from its unproved theorem:
the theorem is used only by existential elimination in a proof.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.exists_affinePerfectChainGeometricModels` by decomposition.
Added one hole in `AlgebraicGeometry.exists_affineSpecifiedModelChainComparison`, node
`lem-pc-affine-specified-model-chain-comparison`. It assumes the actual bounded-projective
complexes and explicit tilde-model isomorphisms; constructing those models has been completed
from existing library declarations in the item's proof. Net holes closed minus added: zero.
No sorry remains in the item's module. The previously attempted `_models` auxiliary was
removed, since it provided no connection to P and Q. No claim of transitive sorry-freeness
is made: existing named library dependencies may themselves rest on sorry.

## No longer needed

Removed direct proof imports of
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` and
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`: they now belong to the comparison
node's proof dependencies and remain imported there, so these modules are not pruned from
the target closure. Removed `Sheaf.AlgebraicGeometry.SchemeIsoDerivedQCoh`:
`lem-pc-scheme-iso-derived-qcoh` is no longer needed on this proof route, because
quasi-coherence is obtained directly from transported perfectness. Its module may still
be reached elsewhere; no claim of global pruning is made.

## Where the brief, the DAG or earlier work was wrong

The old sandbox attempted a comparison for arbitrary bounded finite-projective E,K.
This is false: zero complexes cannot model a pair with nonzero Hom. Genuine identifications
with P,Q were missing. The discarded split and metadata were replaced; the new comparison
requires an exact scheme-isomorphism derived equivalence and two actual tilde-model
isomorphisms. The existing target statement is unchanged. No unit or chapter route was
changed. The unit's realized field does not name this node as a required unit-level step.

Chosen derived-category instances require care: destructing the existential localization
transfer would shadow the existing global scheme-derived category. The proof extracts
only the open-site witnesses. The affine bounded-projective theorem uses the explicitly
rebundled ring, so the corresponding open-site instance is also supplied. Elaboration of
these comparisons required an 800000 heartbeat budget; single-file runtime stays below
the 60-second bound.

LeanSearch was attempted and unavailable (Internal Server Error). LeanFinder, Loogle,
and Mathlib source grep found ordinary scalar-extension functors and sheaf pullback
comparisons, but no combined specified-model comparison. The Stacks pages for Tags
09RE, 06Z0 and 08DW were read online because the cited local perfect.tex is absent here.

## New nodes

`lem-pc-affine-specified-model-chain-comparison`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-specified-model-chain-comparison.json`, records
base-change geometry and chain-map compatibility for supplied genuine affine models.
Its complete Lean signature is recorded verbatim. Its module is
`lean/Sheaf/AlgebraicGeometry/AffineSpecifiedModelChainComparison.lean`.
The bounds, finite generation and projectivity of E0,K0 and the explicit model
isomorphisms are hypotheses, so the theorem does not repeat the original existence
assertion for models of arbitrary perfect objects. Zero rings, empty spectra, and the
single-object tail were checked in the construction described in its proof.
No statement/interface change records are required.

## Second reading by V4

1. Compared the delivered target module with the repository version. The theorem signature is byte-for-byte unchanged; only its proof, proof-only imports, and local elaboration options differ. The added comparison module and node are separately declared, and no target statement or definition was altered. Verdict: pass.

2. Compiled both sandbox modules with `lcompile.py --all`; both compile cleanly. The target has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The only remaining `sorry` is the named theorem `exists_affineSpecifiedModelChainComparison`, with its source docstring and matching split node. Verdict: pass subject to that documented split.

3. Reviewed the split statement and its edge cases. It assumes actual bounded finite-projective complexes and explicit tilde-model isomorphisms, so it is strictly weaker than the original existence target and supplies exactly the comparison still needed. The statement is not duplicated by an existing declaration; searches recorded in `searches.jsonl` found no match. Verdict: pass.

4. The proof follows the shortest available reduction: scheme-isomorphism transport, affine bounded-projective models, then the specified-model comparison. Removed unused direct imports of affine pullback/QCoh comparison and scheme-isomorphism QCoh transport from the target module; the comparison node retains the imports it needs. Verdict: pass; no additional pruning found.

5. The target node proof steps and `proof_deps` now match the Lean proof, and the new split node records its complete signature, source, proof route, searches, and Lean location. The unit route is unchanged. Verdict: pass.

Changed during second reading: appended this review only; no code or node repair was necessary.
