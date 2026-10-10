Files written:

- `dag/nodes/sec-picard-framework/lem-pc-perfect-tensor-hom-duality.json`: item, split.
- `dag/nodes/sec-picard-framework/lem-pc-perfect-termwise-dual.json`: statement-only unsplit node, no Mathlib exact match.
- `dag/nodes/sec-picard-framework/lem-pc-dualizable-tensor-hom-equivalences.json`: Mathlib leaf, exact declarations `CategoryTheory.tensorLeftHomEquiv` and `CategoryTheory.tensorRightHomEquiv`.
- `citations.json`: verbatim statement excerpts for every proof-step citation.

Attachments: none.

WANTED: none.

## Not duplicates

lem-pc-perfect-termwise-dual vs lem-sc-finite-locally-free-derived-hom: the existing node concerns a single finite locally free module in degree zero, while this node concerns a bounded complex, its degree-reversing dual differential, and the evaluation/coevaluation zig-zag identities.

lem-pc-perfect-rhom-tensor-comparison vs lem-sc-finite-locally-free-derived-hom: the existing node is only the degree-zero special case of a single finite locally free module, while this node treats arbitrary bounded perfect complexes, biduality, and the derived-pullback RHom base-change map.

lem-pc-perfect-termwise-dual vs lem-pc-perfect-tensor-hom-duality: the new node concerns only a bounded strict-perfect representative and its explicit termwise dual, evaluation, coevaluation, and zig-zag identities; the item concerns arbitrary perfect objects, Hom isomorphisms for all quasi-coherent complexes, and compatibility with every derived pullback.

lem-pc-perfect-termwise-dual vs lem-sc-smooth-proper-tensor-perfect-case: the new node is the local bounded strict-perfect dual-complex calculation and has no morphism, properness, right-adjoint, or projection-formula hypotheses; the existing node is a proper perfect-morphism projection comparison theorem.

The item had no exact sorry-free declaration in either Lean checkout. This repair replaces derived-category gluing with globally defined RHom comparison maps and adds `lem-pc-perfect-rhom-tensor-comparison`; the pullback step also uses `lem-pc-derived-pullback-tensor-qcoh` for strong monoidality.

## Review by H1

I read Tags 08DQ, 0FPC, 0GM7, 09UA, and 0A9T and the definitions of perfect complexes and derived pullback. Step 1 uses the new node's global definition of `K^vee`, evaluation comparison, and bidual isomorphism; no equality of derived-category morphisms is inferred from restrictions. Step 2 uses the Mathlib exact-pair Hom equivalences together with that global dual data. Step 3 uses the local finite-locally-free description, termwise derived pullback, `lem-pc-derived-pullback-tensor-qcoh` for strong monoidality, and the new node's global RHom base-change map, checking only its isomorphism locally. Step 4 applies the same exact-pair equivalence after pullback. I checked every citation quote against its node statement and the hypotheses for arbitrary `g`; small degree-zero finite-free and zero-complex cases remain valid. Searches for the new node used LeanFinder, Loogle, grep, and unavailable LeanSearch as recorded.

## Second reading by H1

- Item statement: checked against Cohomology Lemma 20.50.5 (Tag 08DQ), Example 20.50.7 (Tag 0FPC), Cohomology Tag 09UA (cohomology-lemma-perfect-pullback), and Duality Lemma 48.8.1 (Tag 0A9T), hypothesis by hypothesis; verdict: mathematically valid, with source references corrected because 0A9T alone is only the pullback/projection comparison.
- Step 1: checked against `lem-pc-perfect-rhom-tensor-comparison`; verdict: valid with globally defined RHom maps and no derived-category gluing.
- Step 2: checked against the exact-pairing hypotheses and both Mathlib declarations in `lem-pc-dualizable-tensor-hom-equivalences`; verdict: variance and tensor factors agree, and the source is now 08DQ/0FPC.
- Step 3: checked against `def-pc-derived-pullback`, `lem-pc-flat-complex-derived-pullback`, `lem-pc-derived-pullback-tensor-qcoh`, and `lem-pc-perfect-rhom-tensor-comparison`; verdict: valid because only the global base-change map's isomorphism is checked locally.
- Step 4: checked against the same exact-pairing statement on `X'`; verdict: valid and natural in both arguments.
- New node `lem-pc-perfect-rhom-tensor-comparison`: checked against 08DQ/lemma-internal-hom-evaluate-isom, 0GM7/lemma-pullback-internal-hom, and 09UA/lemma-perfect-pullback; verdict: self-contained statement-only global comparison, biduality, and pullback base-change assertion, no duplicate found.
- New node `lem-pc-dualizable-tensor-hom-equivalences`: checked against Mathlib `CategoryTheory.tensorLeftHomEquiv` (line 386) and `tensorRightHomEquiv` (line 410); verdict: exact specialization with the stated evaluation/coevaluation orientation and recorded searches.

Changes made: corrected the item, RHom-comparison, and termwise-dual source metadata to Tags 08DQ, 0FPC, 0GM7, and 09UA; specialized the Mathlib leaf to `D_QCoh(O_X)` and restored its valid scheme definitions; corrected Step 2's source; made local-to-global gluing and pullback-cover arguments explicit; recorded the source error and all per-step/per-node verdicts required for delivery.

## Source error

The worker attributed the dualizability and tensor-Hom calculation to Tag 0A9T. That tag actually states the right-adjoint pullback/projection comparison for a quasi-compact, quasi-separated morphism. The dual construction, evaluation/coevaluation, and tensor-Hom identification used here are stated in Cohomology, Tag 08DQ (Lemma 20.50.5) and Tag 0FPC (Example 20.50.7); Tag 09UA supplies preservation of perfect complexes under pullback, while 0A9T is retained only for the separate pullback-comparison context.
