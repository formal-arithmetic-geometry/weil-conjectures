1. Files written:
- `dag/nodes/sec-deligne-laumon-general/lem-zl-geometric-irreducibility-affine-local.json` — item, split with three proof steps and no new DAG nodes.
- `citations.json` — empty because every step is elementary or a one-line Mathlib specialization.

2. Attachments: none.

3. WANTED: none.

4. I read the item source, Stacks Project `varieties.tex`, Tag 038G (`lemma-geometrically-irreducible-local`, lines 1405--1442), and the current blueprint ancestry in `lem-zl-bertini-finite-cover-curve`. The imported statement agrees with Tag 038G after restricting to irreducible X and retains the final nonempty-open assertion; no reducedness, quasi-compactness, or finite-type assumption was added. I searched the DAG and blueprint for the affine-local and pairwise-open-cover criteria. A separate pairwise-cover node would duplicate the item's Stacks tag and move one clause into a child, so I removed it; the criterion is written directly as a one-line specialization of Mathlib's `PreirreducibleSpace.of_isOpenCover`.

## Review by N4

I checked each proof step against Tag 038G. Step 1 uses only the definition of geometric irreducibility, the affine identification of an affine scheme with the spectrum of its global sections, and the elementary fact that a nonempty open of an irreducible space is irreducible; it also verifies the moreover clause after every field extension. Step 2 uses the scheme affine-open basis, affine base change `Spec(Γ(U,O_X) tensor_k K)`, and surjectivity of the projection after a field extension to preserve nonemptiness and pairwise intersections; these are the direct affine calculations in the cited Stacks proof. Step 3 explicitly names Mathlib's `PreirreducibleSpace.of_isOpenCover`; irreducible opens are preirreducible and the nonempty index family supplies nonemptiness, so the theorem yields irreducibility. I checked the edge cases of a one-point scheme, an affine irreducible scheme, and an arbitrary nonempty open; the cover index is nonempty because X is irreducible. The Mathlib searches for the item and the pairwise-cover formulation were run with LeanFinder, LeanSearch, Loogle, and Mathlib grep; no exact item theorem was found, while the open-cover theorem was found as the direct generalization.

5. Nothing remains unfinished.
