1. Files written:

- `dag/nodes/sec-abelian-varieties/pqf-lem-integral-lft-finite.json`: item, split; no new nodes.
- `citations.json`: citation for step 1.

2. Attachments:

- None. No sorry-free slopmaster2 declaration states this item.

3. WANTED:

- None.

4. What was wrong in the imported node:

The imported proof expanded a ring-local argument and cited only the conventions definition, leaving the finite-type-to-finite-module theorem implicit. The DAG already has the stronger statement `lem-weil-pbc-finite-iff-integral-lft`, backed by Mathlib's `AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`; I replaced the incomplete expansion by its reverse implication and cited that node. No new node is needed.

5. What I could not finish:

Nothing.

## Review by M1

I read the item node, its chapter and unit records, the blueprint citation for Stacks Tag 01WJ, and the existing node `lem-weil-pbc-finite-iff-integral-lft`. That existing statement explicitly says that a scheme morphism is finite if and only if it is integral and locally of finite type, so step 1 uses exactly its reverse implication under the item's two hypotheses. The source is Stacks Morphisms, Lemma 29.45.4 (Tag 01WJ), matching the item's statement. I verified the Mathlib declaration and source line (`Mathlib/AlgebraicGeometry/Morphisms/Finite.lean:100-101`) through LeanFinder and grep; Loogle was run with the recorded query but rejected the unqualified identifier, and LeanSearch was unavailable. The citation quote is verbatim from the existing node. I also checked the item has no Lean declaration with the blueprint tag and that no additional statement dependency is required.

## Second reading by M1

- Item statement: checked hypothesis by hypothesis against Stacks Tag 01WJ / Lemma 29.45.4; verdict pass (integral and locally of finite type imply finite).
- Step 1: checked against the statement of `lem-weil-pbc-finite-iff-integral-lft`; verdict pass (its reverse implication gives exactly the conclusion, with no extra hypothesis).
- New nodes: none; the proof uses the existing Mathlib-backed node rather than creating a duplicate or restatement.
- Citation: checked the quote against the dependency node verbatim; verdict pass.
- Small cases: the claim is vacuous for the empty source, and for affine schemes it specializes to the standard finite-ring criterion; no exceptional zero or field case changes the hypotheses or conclusion.
- No node or mathematical statement required repair; the imported item retains its required null blueprint provenance fields.
