## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.cartier_generic_stalk_galois_model`
with a complete Lean proof from a geometric model with a Galois fraction-field
action and a compatible residue-field square. The original signature is unchanged.
Added the proof imports `CartierGenericStalkGaloisModelCore` and
`Mathlib.RingTheory.Flat.TorsionFree`. Added one new statement module and its node;
updated the original node's proof, proof dependencies and proof origin.

The proof performs three actual algebraic steps: injectivity gives torsion freeness
and then flatness over the DVR; finiteness gives integrality, so the fraction-field
Galois action descends over the integrally closed DVR; compatible residue-field
isomorphisms give the finrank equality, which is the prime's inertia degree.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.cartier_generic_stalk_galois_model`
(node `lem-sbc-cartier-generic-stalk-galois-model`).
Added one remaining hole:
`AlgebraicGeometry.Scheme.cartier_generic_stalk_galois_model_core`
(node `lem-sbc-cartier-generic-stalk-galois-model-core`). No other holes remain
in the delivered modules. This is a decomposition, with net hole change zero,
not a proof of the geometric construction. The new statement does not assert
flatness, a Galois action on the integral rings, or equality of dimensions. Those
are proved in the item using Mathlib, rather than handed to another sorry.

The remaining geometric statement requires injectivity, a fraction-field action,
and actual compatible residue-field isomorphisms for the selected factor. Merely
being a finite Galois algebra would not provide this comparison. The proof uses
no arbitrary chosen witness in a definition. The new theorem was checked on an
empty normalization fibre (vacuous), trivial G (S is the base DVR), and disconnected
torsors (select the component whose normalization contains x).

Both delivered modules compile locally with the project's module system.

## No longer needed

None. No original imports were removed. The original proof dependency
`lem-sbc-normalization-stalk-base-change` is needed by the geometric construction,
so it moves below the new intermediate node and is not claimed as pruned.
The field-component classification alone does not give the subgroup action or
residue square needed here; it is recorded as an input to that construction.
No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG's three geometric steps are not directly supplied by its one
proof dependency: normalization stalk base change supplies the localization
comparison, but not the torsor field factor with subgroup action and compatible
residue maps. These missing interfaces are the remaining geometric work.
The library's `field_torsor_galois_components` supplies component fields and their
Galois property, but its signature does not supply the subgroup action required
by this item. The new statement retains that requirement explicitly.

Read Stacks 0307 (integral closure localization) and 09EB (the degree formula in
an already Galois field extension). Tag 09EB by itself does not construct the
field factor or residue comparison; the new node cites the original geometric
argument as well. The degree formula is not used in the delivered proof.

## New nodes

`lem-sbc-cartier-generic-stalk-galois-model-core` in
`dag/nodes/sec-smooth-base-change/lem-sbc-cartier-generic-stalk-galois-model-core.json`
is the geometric construction, stopping before ring-level Galois descent,
flatness and finrank calculations. Its Lean statement includes both residue
ring isomorphisms and their commutative square. Its docstring gives the local
Cartier, torsor factor, integral-closure, finiteness and residue arguments.
LeanFinder, Loogle and grep searches were run and logged in `searches.jsonl`.
LeanSearch was also called and returned Internal Server Error (recorded unavailable).
No existing statement or definition was changed; no forced adaptations or
change records are needed.

## Second reading by B4

1. **Statements and accidental changes.** Compared the delivered main module
with the repository version: the target declaration's signature is byte-for-byte
unchanged. The added core declaration is a separate split-off node with the
reported statement; no existing declaration or definition was changed. Verdict:
pass.

2. **Compilation and proof checks.** Compiled both delivered modules with
`lcompile.py --all`; they compile cleanly. The only remaining `sorry` is the
named core theorem, and it is documented and has a matching node. The main
theorem proof contains no forbidden commands or hollow definitions. Verdict: pass
subject to the declared split-off geometric hole.

3. **New statement.** Checked the core theorem's hypotheses and conclusion
against the geometric construction: it supplies exactly the selected
integral-closure factor, injective base map, fraction-field Galois action, and
residue square needed by the main proof, without asserting the later flatness or
inertia equality. Edge cases described in this report remain valid. Verdict:
pass.

4. **Pruning and route.** The proof uses the core geometric node, then the
torsion-free flatness, fraction-field Galois descent, and residue finrank lemmas.
No original import can be removed, and the unit route through normalization and
the field-factor construction is retained. Verdict: pass.

5. **DAG agreement.** The main node's proof and `proof_deps` name the core node,
and the core node records its module, declaration, source, proof steps, and split
status. Verdict: pass.

Changed only this report section after second reading; no Lean statement or proof
was altered.
