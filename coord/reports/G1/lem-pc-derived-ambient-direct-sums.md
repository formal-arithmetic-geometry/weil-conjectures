Files written:

- `dag/nodes/sec-picard-framework/lem-pc-derived-ambient-direct-sums.json` — statement, split proof, no Mathlib leaf.
- `dag/nodes/sec-picard-framework/lem-pc-scheme-modules-grothendieck-abelian.json` — statement node attached to the sorry-free source theorem; Mathlib search verdict no match.
- `citations.json` — verbatim citations for all proof-step uses.

Attachments:

- `AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian` belongs to `lem-pc-scheme-modules-grothendieck-abelian`.

WANTED: `literature/stacks-project/injectives.tex`, Lemma 07D9, for the derived-category coproduct construction (the local literature checkout contains only citation metadata).

WANTED: `literature/stacks-project/perfect.tex`, Lemma 08DT proof, for the cohomology direct-sum identity (the local literature checkout contains only citation metadata).

## Review by G1

I read the item, its ancestor route through `lem-sc-finite-duality`, and the existing `lem-pc-derived-qcoh-direct-sums` node. The latter explicitly uses this item for both the ambient coproduct and the cohomology formula, so the item is not already complete in the DAG. In the Lean source I read `WeilConjectures/AlgebraicGeometry/Cohomology/DirectImage.lean` lines 155–161: the declaration `AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian` states exactly the prerequisite that the module-sheaf category is Grothendieck abelian and its proof has no `sorry`; this is recorded as the only new node and attached in its `lean_audit`.

The first item step uses that node for existence and exactness of set-indexed coproducts, exactly as its statement says. The second step follows Stacks 07D9: representatives are complexes, coproducts of complexes are degreewise, and exact coproducts descend through the quasi-isomorphism localization to the derived coproduct; the empty and singleton cases were checked explicitly. The third step follows the first sentences of the 08DT proof: exact direct sums commute with cycles, boundaries, and their quotient, giving the canonical cohomology isomorphism in every integer degree. Every non-elementary category fact is tied to the Grothendieck prerequisite node; the item clauses themselves were kept as proof steps rather than duplicated nodes. I also ran the required Mathlib searches for the new prerequisite and for the item; Mathlib supplied only partial sheaf/complex infrastructure and no exact theorem for this statement.

Small-case checks: for an empty family the termwise sum is the zero complex and both sides of the cohomology formula are zero; for a singleton family the coproduct and comparison map are identities; for a finite family the argument reduces to the usual finite biproduct calculation.

What was wrong in the imported material: the item had no proof or prerequisite for exact coproducts. The source literature files named by the node are not present in this checkout, so the report records both WANTED entries and uses the cited Stacks locations as proof origins.

What remains unfinished: no Lean code was written or compiled, as required for stage 1. The new prerequisite is unsplit beyond its attached source declaration.

## Second reading by G1

- Item statement: checked against Stacks Injectives Lemma 07D9 clauses (1)-(2) and Perfect Lemma 08DT proof; the scheme, arbitrary set-indexed family, termwise representative coproduct, and all-degree cohomology isomorphism agree hypothesis by hypothesis.
- Step 1: checked against `AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian` (DirectImage.lean lines 155-161); the cited statement supplies the abelian category, small colimits, and exact filtered colimits used here. Verdict: sound.
- Step 2: checked against Injectives Lemma 07D9 clauses (1)-(2) and the Grothendieck exact-coproduct hypothesis; degreewise coproducts, preservation of quasi-isomorphisms, and the localization coproduct universal property are the stated construction, including empty and singleton families. Verdict: sound; no existing DAG node states this ambient derived-category result (search of all `dag/nodes`).
- Step 3: checked against the first three sentences of the Perfect Lemma 08DT proof and exactness from the Grothendieck prerequisite; kernels, images, and cycle-boundary quotients commute with the termwise direct sum, giving the canonical map in every degree. Verdict: sound.
- New node `lem-pc-scheme-modules-grothendieck-abelian`: statement-only and self-contained with `[def-pc-scheme]`; source checked against the attached sorry-free Lean declaration, B1-B7 satisfied, and semantic/loogle/grep searches recorded. Verdict: sound and not a duplicate.
- New node `lem-pc-derived-ambient-direct-sums`: statement has only the required definitions and TeX, cites the Stacks tags/labels, and keeps the item clauses in proof steps rather than duplicating them as nodes. Verdict: sound; no Mathlib declaration or blueprint duplicate found.

Changes made: none. The initial split already passed citation, search, duplicate, DAG-shape, and preflight checks; no statement, dependency, or citation repair was justified.
