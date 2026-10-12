## What changed
Repaired the incomplete first-worker split of `Sheaf.AlgebraicGeometry.EtaleFieldPointFunctor`.
The original declarations, signatures, definitions and public imports are unchanged.
Restored the original full-faithfulness docstring and proved
`AlgebraicGeometry.etaleFieldPointFunctor_fullyFaithful` by gluing local realizations,
checking compatibility with geometric-point detection, and proving faithfulness directly.
The proof now imports `EtaleFieldPointMapLocal`, `EtaleFieldGeometricPointsDetect` and
Mathlib's gluing API privately. The unchanged geometric-action source is present only
because the synchronized compiled dependency was initially absent; it is not a source change.

## Proved and sorry left
Closed: `AlgebraicGeometry.etaleFieldPointFunctor_fullyFaithful`
(node `lem-exc-etale-field-point-functor-fully-faithful`).
Added hole: `AlgebraicGeometry.etaleFieldPointMap_local`
(node `lem-exc-etale-field-point-map-local`), in its own new module, with a complete
natural-language proof. This is the finite-spectrum local realization step, without
any gluing or uniqueness assertion.
Proved new helper: `AlgebraicGeometry.etaleFieldGeometricPoints_detect`
(node `lem-exc-etale-field-geometric-points-detect`), with no `sorry`.
The item's module has no remaining `sorry`. One old hole is closed and one new hole is
added: this is a decomposition, net zero, not a completed proof of full faithfulness.
The first draft's undocumented `_full` and `_faithful` holes were removed entirely.
No holes are added in definitions, and no arbitrary existence witness is used to define
public data. Witnesses chosen inside the proof only construct the existential lift.

## No longer needed
Removed direct proof imports of `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
and `Sheaf.FieldTheory.EtaleFieldGaloisClassification` from the item. Their nodes,
`lem-weil-pbc-etale-fibre-discrete-separable-points` and
`lem-exc-etale-field-galois-classification`, are no longer immediate proof dependencies
of the item; both remain needed by the local realization node and are imported there.
No module or node is pruned from the target import closure. The geometric-point
continuity module remains publicly imported because the functor definitions use it.
The unit `sk-prop-h2` has empty `realized.statement` and `realized.steps` entries;
no unit realization or unit route is bypassed or modified.

## Where the brief, the DAG or earlier work was wrong
The first report said the target remained `sorry` and that the draft helper modules
were not imported. Its source actually replaced the target hole with two new holes,
imported a third hole, and supplied no nodes. That was not a valid delivery.
The missing compiled geometric-action dependency was an environment issue, resolved
by compiling its unchanged source locally. Detection has a shorter proof than the
original finite-extension decomposition: quasi-finiteness gives discreteness, reducedness
and singleton opens give integral one-point schemes, the separably closed lifting lemma
gives flat surjective points, and epimorphism cancellation gives local equality.
Mathlib supplies lifting, flat epimorphisms, local extensionality and gluing; no searched
result states the remaining local equivariant realization. LeanSearch was unavailable;
LeanFinder, Loogle and grep searches were run and recorded with `msearch.py`.

## New nodes
`lem-exc-etale-field-geometric-points-detect`: equality of arbitrary scheme maps out of
an étale field scheme is detected by its geometric points. Proved via Mathlib's lifting,
flat epimorphism and local extensionality APIs and the upstream proved reducedness
result `etale-proposition-etale-reduced`. Source: Stacks 03QR and 02GL. Searches found
the tools, no exact statement. The target Y need not be étale.

`lem-exc-etale-field-point-map-local`: realize an equivariant action morphism on a
neighbourhood of each source point. Source: the finite-spectrum step of Stacks 03QR,
with 02GL and the existing finite Galois classification. One named `sorry` remains.
The statement is strictly part of the item: compatibility, global assembly and
faithfulness are proved separately in the item. Searches found no exact statement.
There are no statement/definition change records because no existing signature or
public definition changed.

## Second reading by P2
1. Compared every delivered source with the repository. Existing signatures and
   definitions are byte-for-byte unchanged. The geometric-action module is identical.
   New statements are confined to their own new modules. Verdict: pass after repair.
2. Compiled all delivered modules through `lcompile.py`, without errors or warnings.
   Only the named local realization theorem remains `sorry`; no forbidden declarations
   or hollow definitions occur. The detection proof uses only standard axioms; the
   target's axiom list includes `sorryAx` solely through local realization.
   Verdict: valid conditional proof/decomposition, not a closed target.
3. Read both new statements top-down and checked their edge cases. Empty sources make
   detection vacuous and the local statement has no x; empty targets cannot receive a
   geometric-point action map from a nonempty source. Over a separably closed K the
   singleton components are Spec K, so local realization is a map of components.
   For general K, transitivity sends one finite source orbit to one target component;
   the existing finite Galois Hom-bijection has the correct contravariant orientation.
   Searches with different wording found no duplicate statement. Verdict: true and
   exactly sufficient. Detection is proved; local realization is the sole split hole.
4. Read the final proof from full faithfulness downward: local maps agree on pullback
   overlaps by detection, gluing constructs a map, cover extensionality checks it is
   over K, and factoring geometric points into an open verifies its action map.
   Faithfulness uses the independently proved detector. All imports serve definitions
   or these proof steps. Immediate old dependencies are reported above and retained
   below the local lemma. The unit's realized route is unchanged. Verdict: pass.
5. Checked new node signatures against Lean and updated the item's proof steps,
   proof_deps and proof_origin to the actual gluing/detection route. New nodes have
   sources, complete proof steps, searches, provenance and Lean records.
   Verdict: pass.

Changes made by the second reader: removed undocumented full/faithful holes; proved
geometric-point detection and the gluing/faithfulness reduction; restored the existing
docstring; corrected private imports; added two matching nodes and updated the old
node's proof route; replaced the inaccurate report; excluded the scratch check module.
