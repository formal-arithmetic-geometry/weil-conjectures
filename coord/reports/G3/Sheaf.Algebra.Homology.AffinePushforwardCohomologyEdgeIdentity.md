## What changed

Proved `AlgebraicGeometry.exists_affinePushforwardCohomologyEdge_identity` by explicitly
constructing alpha from the existing sheaf edge epsilon, the supplied ordinary comparison,
and the pushforward of the tilde/Gamma counit. The Lean proof specializes the sheaf edge
to exact tilde, proves the counit cancellation using naturality and the adjunction triangle,
and applies the new ordinary comparison factorization. The existing theorem signature and
its public import remain unchanged. Added one proof-only import and updated the target node
with the actual construction and proof dependencies. No definitions or other modules change.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.exists_affinePushforwardCohomologyEdge_identity`
(node `lem-pc-affine-pushforward-cohomology-edge-identity`).

Added one hole, `AlgebraicGeometry.affinePushforwardComparison_factorization`
(node `lem-pc-affine-pushforward-comparison-factorization`), in its own new module.
This is a decomposition: one upper hole closed and one strictly smaller lower hole added.
The lower theorem has no existential edge transformation, no quasi-coherence hypothesis,
and no tilde/Gamma counit or representative coordinate. Its complete natural-language proof
and source are in its docstring. The upper assembly has no sorry.

The existing `AlgebraicGeometry.exists_affineDerivedPushforwardSheafEdge` is used as supplied;
its module is not modified by this delivery. No additional holes are delivered.

## No longer needed

Removed the earlier attempt's proof import
`Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentityCanonical`.
Neither that proposed module nor its proposed node
`lem-pc-affine-pushforward-cohomology-edge-identity-canonical` is used or submitted.
The earlier proposed `AffinePushforwardCohomologyEdgeIdentityData` module and node
`lem-pc-affine-pushforward-cohomology-edge-identity-data` are also unnecessary and unsubmitted.
These proposals were absent from the repository; their sandbox records were archived in
scratch, so no landed DAG node or module is deleted. Both original target dependencies,
comparison coordinates and the sheaf edge, remain necessary. No other node is pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier canonical helper repeated exactly the target statement and was not a strict
reduction. Its node also inherited irrelevant review records. The replacement isolates
only ordinary comparison naturality, while the actual edge construction and adjunction
calculation are proved in the target module.

The node's intended mathematical argument is usable. A proof attempt of the remaining
factorization successfully rewrote the Q/homology comparison by naturality and computed
the homology map of sigma using `ShortComplex.homologyMap_mapNatTrans`. The unfinished
part is the final cancellation and conversion between the scheme-module pushforward
and ringed-space presentation. Generic simp/conversion attempts expose the separate
`Scheme.Modules` category instance and expand affine sheaf data. The scratch proof attempt
records the direct rewrites; it is not part of the delivery. This is an unfinished local
calculation, not a tool failure or a disputed statement. Zero rings, zero complexes,
unbounded complexes, and arbitrary supplied sigma introduce no exceptional cases.

## New nodes

`lem-pc-affine-pushforward-comparison-factorization` records the ordinary comparison
factorization in `Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization`.
It is strictly one step of the argument: cohomology naturality of sigma before applying
the derived unit. Its preservation hypotheses are supplied in the upper proof by
transporting exactness of restriction of scalars followed by tilde_B along sigma.
No unit-level step is bypassed, and there is no change record or forced adaptation.

## Second reading by G3

1. Compared the delivered existing module against the repository with `diff` and
   checked its theorem signature byte for byte: unchanged. The sole existing-node
   changes are `proof`, `proof_deps`, and `proof_origin`. No definitions, public
   imports, or other existing declarations change. Verdict: pass.
2. Compiled both delivered modules in import order using `lcompile.py --all`:
   clean, without warnings. A scratch copy with `#print axioms` for both public
   declarations reports only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`. There is exactly one delivered sorry, in the named factorization
   theorem, and no prohibited declaration or data chosen in a definition.
   The upper theorem constructs its witness in its proof. Verdict: pass as a
   decomposition, not a sorry-free dependency closure.
3. Read the factorization statement and docstring against the expanded comparison
   definition, Mathlib's `ShortComplex.homologyMap_mapNatTrans`, and inverse
   Q/homology naturality. Independently searched with the different phrase
   "inverse homology isomorphism commutes with natural transformation between
   functors" (Lean Finder), the fully qualified naturality lemma (Loogle), and
   `rg` across both library roots. The generic ingredients exist; the exact affine
   factorization does not. Zero rings, zero complexes, every integer degree, and
   unbounded complexes introduce no exceptions. The statement is a strict part of
   the upper argument and has its own source, proof in words, and node. Verdict: pass.
4. Read the construction from the target downward: sigma, the counit, and the
   supplied sheaf edge define alpha; sigma naturality and the adjunction triangle
   cancel the representative coordinate. Both old proof dependencies are used;
   none is pruned. Checked `dag/units/sk-thm-picard-semicon.json`: its `realized`
   entries are empty, and this local naturality calculation bypasses no unit step.
   All imports are used and have the required visibility. Verdict: pass.
5. Compared the target node's three proof steps with the Lean construction and
   cancellation. Checked the new node's statement, dependencies, source, search
   records, creation/blueprint metadata, and verbatim Lean signature. Verdict: pass.

Second-reader changes: appended this independent review and performed additional
searches and scratch proof checks. The generic comparison naturality proof closes
in scratch; the affine presentation conversion remains open. No delivered Lean
statement or definition was changed. The current delivery closes one original
hole and adds one smaller hole, so its net is zero; it is a decomposition.
