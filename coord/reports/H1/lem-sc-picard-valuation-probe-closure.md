Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-picard-valuation-probe-closure.json` — item, split into two proof steps.
- `dag/nodes/sec-abelian-varieties/lem-sc-picard-closure-specialization.json` — statement node, attached to `AlgebraicGeometry.exists_specializes_of_mem_closure_range` (closed project declaration).
- `dag/nodes/sec-abelian-varieties/lem-sc-picard-valuation-probe-specializes.json` — statement node, attached to `AlgebraicGeometry.ValuativeCommSqWithPt.ofSpecializes` (closed project declaration).
- `citations.json` — verbatim statement quotes for every step citation.

Attachments:

- `AlgebraicGeometry.exists_specializes_of_mem_closure_range` belongs to `lem-sc-picard-closure-specialization`.
- `AlgebraicGeometry.ValuativeCommSqWithPt.ofSpecializes` belongs to `lem-sc-picard-valuation-probe-specializes`.

WANTED: none.

What was checked:

- The item source is Stacks Project Morphisms, Lemma `morphisms-lemma-reach-points-scheme-theoretic-image`, Tag 02JQ. Its closure-point argument first obtains a source point specializing to the chosen closure point, then constructs the valuation probe. The item statement retains the quasi-compact immersion hypotheses and all three requested maps and equalities.
- The first child node was checked against `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean`, theorem `exists_specializes_of_mem_closure_range` (lines 69–87), whose hypotheses and conclusion match exactly. The second child was checked against `WeilConjectures/Compactification/ValuativeCriterion.lean`, definition `ValuativeCommSqWithPt.ofSpecializes` (lines 90–117), whose structure fields provide the valuation ring, fraction field, generic commutative square, and closed-point equality.
- Step 1 uses only the exact specialization statement of `lem-sc-picard-closure-specialization`; the quasi-compactness hypothesis is the item's hypothesis.
- Step 2 uses only the exact valuation-probe statement of `lem-sc-picard-valuation-probe-specializes`; the specialization obtained in Step 1 supplies its premise. Unpacking the square fields is definitional.
- The second child is an off-unit tool from the Nagata compactification route and is declared in `split_report.tool_uses`; no route lemma in the abelian-varieties unit supplies this valuation construction.
- I searched the whole DAG for Tag 02JQ, closure-range specialization, and valuation-probe declarations. The existing Nagata nodes `def-nagata-dense-valuation-probe` and `lemma-nagata-dense-valuation-probe` require a schematically dense source and affine/image-isomorphism setup, so they are not duplicates of either child or this item's arbitrary closure-point statement.
- Mathlib searches were run for the item and both children with LeanFinder, Loogle, grep, and LeanSearch. LeanSearch was unavailable and is recorded as unavailable; no upstream Mathlib declaration matched either valuation construction. The exact project declarations were attached instead.

## Review by H1

I read the Tag 02JQ source route and both project declaration bodies. Step 1's cited node states precisely the specialization extracted from a closure point under quasi-compactness. Step 2's cited node states precisely the valuation ring, fraction field, two morphisms, generic compatibility, and closed-point condition used in the conclusion. The only non-elementary facts are therefore represented by the two child nodes; field unpacking is definitional. I checked that all hypotheses are present: the item's immersion is in particular a morphism and is quasi-compact, and Step 1 supplies the specialization required by Step 2. The small edge case where `s` already lies in the range is covered by reflexive specialization. No statement was weakened, no child restates the whole item, and the existing Nagata dense-source nodes were rejected as non-duplicates because their hypotheses are stronger and their witness is selected under a different setup.

## Not duplicates

lem-sc-picard-closure-specialization vs lem-sc-picard-valuation-probe-closure: the new node asserts only existence of a specializing point; the item additionally constructs a valuation ring and a commutative scheme square.
lem-sc-picard-closure-specialization vs def-nagata-dense-valuation-probe: the new node applies to any quasi-compact morphism and a point in the closure of its range, and asserts only a specialization; the Nagata definition selects valuation data under a schematic-density and affine-base setup.
lem-sc-picard-closure-specialization vs lem-sc-picard-locus-closed-valuation-criterion: the new node supplies a specializing source point but assumes no valuative factorization and concludes no closedness.
lem-sc-picard-valuation-probe-specializes vs lem-sc-picard-valuation-probe-closure: the new node constructs a valuation square from a specified specializing source point; the item obtains such a point from quasi-compactness and closure membership.
lem-sc-picard-valuation-probe-specializes vs def-nagata-dense-valuation-probe: the new node assumes a given specialization and no density or affineness; the Nagata definition selects a witness under schematic density and affineness.
lem-sc-picard-valuation-probe-specializes vs lem-sc-picard-locus-closed-valuation-criterion: the new node constructs one valuation square; the criterion assumes factorization of all such squares and concludes the immersion has closed image.

## Second reading by H1

- Item statement: read Morphisms, Lemma `morphisms-lemma-reach-points-scheme-theoretic-image`, Tag 02JQ; the quasi-compact immersion supplies the quasi-compact morphism hypothesis, and the closure-of-range formulation matches the source's scheme-theoretic-image point set and valuation diagram.
- Step 1: checked against the statement of `lem-sc-picard-closure-specialization` and the declaration `AlgebraicGeometry.exists_specializes_of_mem_closure_range`; it supplies exactly the specializing point required, with no unstated hypothesis.
- Step 2: checked against the statement of `lem-sc-picard-valuation-probe-specializes` and the declaration `AlgebraicGeometry.ValuativeCommSqWithPt.ofSpecializes`; unpacking its fields gives the valuation ring, fraction field, maps, generic commutativity, and closed-point equality.
- `lem-sc-picard-closure-specialization`: statement-only unsplit node; self-contained scheme and quasi-compact morphism notions cite their definition node, source/declaration lines were read, Mathlib searches were run, and identity, empty-source, and field cases behave as expected.
- `lem-sc-picard-valuation-probe-specializes`: statement-only unsplit node; all objects and the specialization premise are explicit, source/declaration lines were read, Mathlib searches were run, and identity, field, and reflexive-specialization cases are consistent.
- Duplicate and blueprint checks: searched the DAG for Tag 02JQ, closure-range specialization, and valuation-probe declarations; the Nagata dense-source nodes have stronger density/affineness hypotheses and are not duplicates. Both new nodes use nearest blueprint ancestor `thm-sc-theorem-of-cube`, with the proof place recorded; no blueprint match exists.
- Edge hypotheses: `s` in the closure is used only in Step 1; the resulting `z` supplies Step 2's specialization; an immersion is a morphism and quasi-compactness is retained. No empty-scheme, zero-object, or numerical parameter hypothesis is present in this lemma.
- Changes: reran the exact recorded LeanFinder, Loogle, and grep searches and synchronized `searches.jsonl` so every recorded query is verifiable by the delivery tool; no mathematical statement or proof step required repair.
