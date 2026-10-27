## What changed

Extracted the existing finite comparison construction to
`Sheaf.Paper.FinitePullbackTensorConstruction` and the already-proved signed total and
derived braiding declarations to `Sheaf.Paper.FinitePullbackTensorBraiding`. The original
module publicly reexports both layers. Existing public names and signatures are retained;
`canonicalFinitePullbackTensor` is a definitionally identical wrapper of the extracted
construction. The new `finitePullbackTensorConstructionIso` packages the same component
family naturally in the two inputs.

Reduced `WeilConjectures.canonicalFinitePullbackTensor_braiding` to the signed comparison
calculation on flat-term K-flat complex inputs in
`Sheaf.Paper.FinitePullbackTensorSignedRepresentatives`. The combining proof is complete:
it obtains a complex preimage of each derived object, resolves it by a flat K-flat
complex, and transports equality of the two natural transformations along the product
of the resulting isomorphisms. Naturality and cancellation prove the arbitrary-input
statement. The split theorem has a full generator proof in its docstring and node.

Change record: `coord/changes/Q2-finite-pullback-tensor-construction-layer.md`.
No existing module besides the assigned item is changed. No source-library declaration
is removed or edited. The prescribed unit route is unchanged.

## Proved and sorry left

Original item: four holes. Closed one upper hole by decomposition:
`WeilConjectures.canonicalFinitePullbackTensor_braiding`
(node `def-pur-finite-pullback-tensor-comparison`). Its naturality/descent proof contains
no holes. Added one strictly restricted representative-calculation hole:
`WeilConjectures.finitePullbackTensor_signed_representatives`
(node `lem-pur-finite-pullback-tensor-signed-representatives`). This is a decomposition,
not a net proof: one closed, one added, net zero.

The other three original holes remain unchanged, all on
`def-pur-finite-pullback-tensor-comparison`:

- `WeilConjectures.canonicalFinitePullbackTensor_associativity`;
- `WeilConjectures.canonicalFinitePullbackTensor_unit`;
- `WeilConjectures.canonicalFinitePullbackTensor_composition`.

Both extracted construction modules have zero holes. The original signed total uniqueness
and derived braiding uniqueness proofs are preserved, not counted as newly closed.

Validation: `lcompile.py --all` compiled the four delivery modules cleanly, including
writing their compiled outputs: braiding 26.9 s, construction 51.6 s, representatives
36.7 s, and the assigned item 39.5 s. The sole direct importer, unchanged
`Sheaf.Paper.CompletedPullbackTensorComparison`, passes the standalone check against
these sandbox modules in 38.0 s. Writing that unchanged consumer in the all-file run
took 78.1 s; its source is not adapted or delivered. The temporary consumer copy was
removed. All 27 original public declaration signatures are preserved across the
reexported layers. Profiling options have been removed.

## No longer needed

No mathematical dependency or module is pruned. The original direct imports are
relocated to the construction layers and remain needed there. The coherence file now
publicly imports both layers, privately imports the representative lemma, and privately
imports the existing independent-coefficient K-flat resolution and tensor-presentation
API used by its descent proof. All five original proof dependencies remain needed by
the extracted constructions. The new final extension uses essential surjectivity from
resolutions; it does not require a further localization-fullness theorem.

## Where the brief, the DAG or earlier work was wrong

The existing node had proof steps for the already-proved constructions but no separate
Lean statement for the signed finite representative coherence calculation. The existing
`proEtaleCanonicalTensorPullback` normalization theorem supplies the representative
square, not its signed coherence equation. The new node isolates that remaining
calculation. Restriction to flat K-flat inputs is a real reduction: the new theorem
accepts explicit complexes with their flatness witnesses, while the original statement
is for arbitrary unbounded derived objects. The Lean proof constructs and uses the
resolution isomorphisms and naturality to bridge this difference.

The rework row points to a quarantine path, but this snapshot contains the restored
item source. It is preserved and adapted, not withdrawn. No definition is hollow.
Edge cases retain all integer degrees and the Koszul sign, allow the zero complex and
empty schemes, and include n=0 and identity morphisms without extra hypotheses.

## New nodes

`def-pur-finite-pullback-tensor-construction` records the existing normalized construction
layer and its natural-isomorphism packaging. It has zero holes.

`def-pur-finite-pullback-tensor-braiding` records the already-proved signed total and
derived braiding constructions in a separate module with zero holes. This separates
the two independent constructions so that writing their compiled modules meets the
per-file limit. Their signatures and proof bodies are retained. The two layers also
make the import direction for the representative theorem acyclic.

`lem-pur-finite-pullback-tensor-signed-representatives` states exactly the remaining
signed tensor/pullback square on localizations of flat-term K-flat complexes. Its proof
plan compares pure generators in each bidegree, then applies the canonical
representative normalization and realization comparisons. It contains one hole and
is strictly below the arbitrary-derived-object braiding theorem.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
