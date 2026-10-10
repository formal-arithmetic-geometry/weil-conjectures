1. Files written:

   - `dag/nodes/sec-picard-framework/lem-pc-perfect-generation-koszul-orthogonal.json`, statement, split.
   - `dag/nodes/sec-picard-framework/lem-pc-koszul-affine-detection.json`, statement-only unsplit node, no Mathlib match.
   - `citations.json`.

2. Attachments: none. No sorry-free declaration in `WeilConjectures/` carries the item or the new affine detection statement.

3. WANTED: none. The Stacks source tag and its proof are available from the cited source; no external document was needed.

4. What was checked and corrected: the item was compared with Stacks Tag 09IR (Lemma 36.15.2). The proof is split at the actual cone reduction, affine Koszul detection, and converse adjunction arguments; it does not restate the item as a child node. The new node records the strictly smaller affine supported-object lemma used by the source proof. I searched the DAG and blueprint for Koszul orthogonality and found no existing statement of that lemma; the existing `lem-pc-supported-open-pushforward` and `lem-pc-restrict-derived-direct-image-open` were read but do not state the affine detection result. The source hypotheses were checked: the complement is the vanishing locus of finitely many elements on the affine open, the cone restricts to zero on the smaller open, and the Koszul restriction to that open is zero. The auxiliary statement was tested on the edge cases `r=0` (the support condition forces the object to vanish) and `r=1` (powers of one element give the usual principal-open detection). Mathlib leanfinder, loogle, and grep searches were run for the new node and found no scheme-level theorem; the existing generic derived-category orthogonality hits do not specialize in one line.

## Review by C1

I read the item record, Stacks Tag 09IR, and the statements of `def-pc-derived-category`, `lem-pc-ringed-spaces-derived-adjoint-general`, and the new `lem-pc-koszul-affine-detection`. Step 1 uses the derived-category setting and the derived pullback/direct-image adjunction; these statements provide exactly the Hom identification used after restricting the Koszul complex to the open. The remaining cone argument is the standard long-exact-Hom calculation in a distinguished triangle. Step 2 uses only the new node's stated supported-object criterion, with the cone's restriction-to-zero hypothesis verified directly from the triangle. Step 3 uses the same adjunction and the fact that the restricted Koszul object is zero. Every citation in `citations.json` is copied verbatim from the cited node statement. The source's affine support hypothesis and all open-intersection hypotheses were checked against the item statement; no unsupported hypothesis or duplicate node was introduced.

## Not duplicates

lem-pc-koszul-affine-detection vs lem-pc-perfect-generation-koszul-orthogonal: the new node is an affine scheme lemma for an object already known to restrict to zero, using all positive powers of the Koszul sequence; the existing item is the open-immersion equivalence between the canonical restriction map and orthogonality to one Koszul complex, with no affine hypothesis on X.

lem-pc-koszul-affine-detection vs lem-pc-perfect-generation-open-induction-step: the new node only detects a supported object on an affine V and concludes that object is zero; the existing induction node constructs a global perfect generator on X and uses the 09IR criterion as one internal step, so neither statement is a special case of the other.

5. Nothing remains unfinished in the split. The maintainer's global build is outside stage 1; the required delivery dry run is the final check.

## Second reading by C1

- Item statement: checked against Stacks Tag 09IR, label `lemma-orthogonal-koszul-complex`, hypothesis by hypothesis; the affine open, quasi-compact overlap, principal-open equations, Koszul object, and both equivalent conditions agree.
- Step 1: checked the cone triangle and the derived adjunction against `def-pc-derived-category` and `lem-pc-ringed-spaces-derived-adjoint-general`; the cited statements provide the Hom identification, and the remaining triangle calculation is explicit.
- Step 2: checked the cone's restriction-to-zero and affine complement against Tag 09IR; rewrote the previously implicit induction using the Koszul multiplication triangles and the long exact Hom sequence, then applied the affine detection node.
- Step 3: checked the converse against Tag 09IR and the same derived adjunction; the restriction of the Koszul complex is zero, so every displayed Hom group vanishes.
- `lem-pc-koszul-affine-detection`: checked self-contained affine hypotheses, definitions, positive exponent quantification, and edge cases `r=0` and `r=1`; no existing DAG or blueprint statement matched, and the recorded Mathlib searches were rerun by the worker.

Changes made: corrected the item's `created.item` metadata (it incorrectly named the open-induction item) and replaced Step 2's unsupported “triangles propagate” shorthand with the explicit exponent induction and long-exact-sequence argument required by E5.
