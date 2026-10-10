# Stage 1 report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-pseudo-coherent-finite-tor-perfect.json` (statement, split; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-pc-ring-pseudo-coherent-finite-tor-perfect.json` (statement-only algebraic criterion; no Mathlib match).
- `citations.json` and this report.

2. Attachments: none. No sorry-free declaration in the project source states the scheme-level item exactly.

3. WANTED: `literature/stacks-project/more-algebra.tex`, More on Algebra, Lemma 15.76.2 (Tag 0658), for `lem-pc-ring-pseudo-coherent-finite-tor-perfect`; the local literature checkout contains the citation but not the source TeX.

4. No statement error was found. The imported item had no proof steps; I supplied the locality, affine translation, and ring-criterion route from Tag 08CQ. The existing ring-level node `lem-weil-bounded-finite-tor-perfect` is narrower (bounded complexes with finite cohomology), so it does not state the criterion needed here and was not cited.

## Review by M1

I read the item source as Cohomology of Sheaves, Lemma 20.49.5 (Tag 08CQ), and checked its hypotheses against the item: a scheme, a pseudo-coherent derived object, and finite Tor dimension, with perfectness local on the scheme. I also read the existing statements of `def-pc-perfect-complex`, `def-pur-pseudo-coherent-complex`, and `lem-pc-affine-qcoh-derived-equivalence`; each citation in the three proof steps quotes the exact portion used. Step 1 uses the local definition of perfectness and pseudo-coherence. Step 2 uses the affine derived equivalence to pass to a ring complex and the new Tag 0658 criterion, whose statement supplies the bounded finite-projective representative. Step 3 uses the affine characterization of strictly perfect complexes to return to the scheme and is elementary once that characterization is available. The ring node is strictly smaller than the item (a ring object rather than a scheme-local object), has no proof sketch because it is intentionally statement-only, and was checked for duplicates by searching the DAG and blueprint. I tested the edge case of an affine scheme `Spec(R)`, where the item reduces directly to the new ring criterion, and the identity morphism case in which the conclusion is the usual affine perfectness criterion. The required Mathlib searches were run for both the item and the new node; LeanSearch was unavailable and recorded as such for the item.

5. Nothing remains unfinished beyond the stated WANTED source document.

## Not duplicates

lem-pc-ring-pseudo-coherent-finite-tor-perfect vs lem-weil-bounded-finite-tor-perfect: the new node assumes a pseudo-coherent complex over an arbitrary ring and finite Tor dimension, while the existing node assumes a bounded complex with finite cohomology over a Noetherian ring and concludes a bounded finite-projective model.
lem-pc-ring-pseudo-coherent-finite-tor-perfect vs lem-trf-finite-tor-amplitude-perfect: the new node is the general ring criterion for pseudo-coherent complexes, while the existing node is restricted to bounded complexes over the specific finite coefficient ring A_{E,n} and characterizes finite Tor amplitude by membership in a pre-defined finite-coefficient category.

## Second reading by M1

- Item statement: checked against Cohomology of Sheaves, Lemma 20.49.5 (Tag 08CQ), including scheme, pseudo-coherence, finite Tor dimension, and perfectness; verdict: agrees.
- Step 1: checked against Tag 08CQ's locality reduction and the statements of `def-pc-perfect-complex` and `def-pur-pseudo-coherent-complex`; verdict: the cited definitions support the local reduction and restriction argument.
- Step 2: checked against Tag 08CQ's affine reduction and More on Algebra, Lemma 15.76.2 (Tag 0658), and the statements of `lem-pc-affine-qcoh-derived-equivalence` and the ring node; verdict: dependencies state the affine translation and ring conclusion used.
- Step 3: checked against the affine clause of `def-pc-perfect-complex`; verdict: elementary once the bounded finite-projective representative is obtained.
- `lem-pc-ring-pseudo-coherent-finite-tor-perfect`: checked against More on Algebra, Lemma 15.76.2 (Tag 0658), including its definition of perfect over a ring and finite Tor dimension; verdict: corrected to be self-contained and removed the unrelated scheme pseudo-coherence and Weil Tor-amplitude dependencies.

Changes made: corrected the ring node's statement and dependencies to match Tag 0658; updated its citation quote; fixed the scheme node's `created.item` metadata, which incorrectly named another item. Edge cases checked: the zero complex satisfies the criterion, a field reduces to bounded finite-dimensional complexes, and the affine scheme case reduces to the ring node. Mathlib searches were rerun and recorded in `searches.jsonl`; no exact declaration was found.
