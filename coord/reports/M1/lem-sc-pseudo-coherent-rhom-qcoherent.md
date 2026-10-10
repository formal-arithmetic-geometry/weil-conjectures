Files written:

- `dag/nodes/sec-picard-framework/lem-sc-pseudo-coherent-rhom-qcoherent.json`: completed the item split with three proof steps.
- `dag/nodes/sec-picard-framework/lem-sc-affine-pseudo-coherent-rhom-qcoherent.json`: added the smaller affine statement-only prerequisite.
- `citations.json`: verbatim statement quotes for every cited node in every step.

No Lean declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states the item or the new affine statement; the blueprint-tag and concept searches were negative.

## Review by M1

I checked the item against Stacks Project `perfect.tex`, Tag 0A6H, clause (1), and its proof reduction to clause (3) on affine opens. Step 1 uses the definition of pseudo-coherence, which explicitly supplies local bounded-above finite-free models, and the existing open-restriction node, whose statement explicitly gives restriction of derived internal Hom and compatibility with cohomology sheaves. Step 2 uses the new affine node; its statement is the affine comparison and the bounded-below quasi-coherence conclusion needed here, so this is a strict local prerequisite rather than a restatement of the global item. Step 3 uses the existing derived algebra-module definition, which states the natural B-module structure and derived functor, and the existing definition of the quasi-coherent B-derived category, which states that quasi-coherence is detected on the underlying O-module. The Noetherian, quasi-coherent-algebra, and bounded-below hypotheses are exactly those in the item and are preserved under restriction. I tested the local statement on the identity affine scheme and on a bounded finite-free complex, where the comparison reduces to the ordinary Hom complex. Mathlib searches for the item and affine node were run with LeanFinder, Loogle, grep, and LeanSearch; no exact scheme-level declaration was found, and the unavailable LeanSearch service is recorded as unavailable.

## Not duplicates

lem-sc-affine-pseudo-coherent-rhom-qcoherent vs lem-sc-affine-rhom-qcoherent: the existing node is only for degree-zero finite modules and identifies Ext sheaves, whereas the new node handles arbitrary bounded-above pseudo-coherent complexes against bounded-below complexes.

lem-sc-affine-pseudo-coherent-rhom-qcoherent vs lem-sc-derived-internal-hom-stalk-localization: the existing node is a stalk-localization theorem for a coherent sheaf in degree zero, whereas the new node is an affine derived-category comparison for arbitrary pseudo-coherent and bounded-below complexes.

lem-sc-affine-pseudo-coherent-rhom-qcoherent vs def-pur-pseudo-coherent-complex: the definition node only defines pseudo-coherence by local bounded-above finite-free models, whereas the new affine node proves the derived internal-Hom comparison and quasi-coherent bounded-below cohomology.

lem-sc-affine-pseudo-coherent-rhom-qcoherent vs lem-sc-pseudo-coherent-rhom-qcoherent: the existing item is the global theorem for a quasi-coherent algebra on a Noetherian scheme, whereas the new node is its affine local calculation for an arbitrary ring and two associated complexes, with no algebra-module conclusion.

## Second reading by M1

- Item statement: checked against Stacks `perfect.tex`, Tag 0A6H, clause (1); the Noetherian specialization and natural algebra-module conclusion are consistent with the project's derived-category definitions.
- Step 1: checked against Tag 0A6H's affine-local reduction and the statements of `def-pur-pseudo-coherent-complex`, `lem-sc-derived-internal-hom-restrict-open`, and `lem-sc-derived-open-restriction-adjunction-exact`; repaired the missing exact-restriction citation.
- Step 2: checked against Tag 0A6H, clauses (1) and (3)(a), and the affine prerequisite; repaired the representative notation from equality to quasi-isomorphism.
- Step 3: checked against `def-pc-derived-rhom-algebra-module` and `def-pc-derived-category-qcoh-algebra`; the elementary module-structure and forgetful-category argument is sound.
- `lem-sc-affine-pseudo-coherent-rhom-qcoherent`: checked against Tag 0A6H clause (3)(a); made the bounded-below condition explicit and retained the strict affine scope.

Changes: added the exactness node citation and verbatim citation, corrected affine representative language, and defined bounded-below cohomology in the affine statement. No node was removed; the affine node is a genuine smaller prerequisite and no Mathlib declaration matches either theorem.
