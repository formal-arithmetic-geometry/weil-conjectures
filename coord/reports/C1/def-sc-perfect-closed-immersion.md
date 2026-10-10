Files written:

- `def-sc-perfect-closed-immersion.json`: definition, no new nodes; Mathlib searches found no matching declaration.
- `citations.json`: empty, because the item is a definition with no proof steps.

Attachments: none.

WANTED: none.

What was checked: the item is not stated by a declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` (including searches for the node id, “perfect closed immersion”, and likely `PerfectClosed` names). The statement was checked against the cited Stacks sources, Tag 0687 (Definition 37.61.2, perfect morphism) and Tag 068Y (Lemma 15.84.2, the affine ring-map resolution criterion). Its hypotheses explicitly introduce the closed immersion, schemes, affine covering, quotient rings, and finite projective modules, and the finite-free equivalence is the standard affine refinement used by 068Y. Existing DAG searches found no duplicate definition node; the neighboring lemma `lem-sc-koszul-regular-closed-immersion-perfect` correctly uses this definition as its conclusion.

What was wrong or incomplete in the imported node: nothing substantive. The imported node was marked `unsplit` even though it is a complete definition and has no proof to decompose; it is now marked `split` with the required blueprint and split metadata. No new statement was invented and no existing node was modified.

What could not be finished: nothing.

## Review by C1

I read the item JSON and the unit record `dag/units/sk-thm-picard-duality.json`, and checked the blueprint ancestor `lem-sc-finite-duality` and its diagonal-step reference. I read the neighboring proof in `lem-sc-koszul-regular-closed-immersion-perfect.json`; its use is exactly the local quotient-resolution criterion stated here. Since this node is a definition, there are no proof steps, proof dependencies, or non-elementary facts to cite, so `citations.json` is intentionally empty. The four statement dependencies are present and define the notions used: scheme, closed immersion, affine spectrum, and finite projective module. I searched the whole DAG and blueprint for the id, the perfect-morphism terminology, and Tags 0687/068Y; no duplicate statement was found. The required LeanFinder, Loogle, and Mathlib grep searches were run (all no match); LeanSearch was unavailable and is not recorded as a verdict. Small edge cases are consistent with the definition: the empty covering for the empty target is vacuous, the unit ideal gives the empty closed subscheme, and the zero ideal gives the identity immersion with a length-zero free resolution.

## Second reading by C1

- Item statement: checked against Stacks Tags 0687 (Definition 37.61.2) and 068Y (Lemma 15.84.2), including the affine quotient and bounded finite-projective-resolution clauses; pass.
- Proof steps: none; this is a definition, so there are no steps or citations to audit.
- New nodes: none; the item itself is the only node in the split, and its four notion dependencies exist and define the cited terms.
- Blueprint and duplication: checked `lem-sc-finite-duality` and whole-DAG searches for the definition and cited tags; no duplicate or blueprint restatement found.
- Mathlib and Lean searches: checked the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch entries in `searches.jsonl`; no matching declaration was found.
- Edge cases: checked empty target/cover, unit ideal, zero ideal, and length-zero resolution; all are consistent.

Changes made during second reading: no mathematical statement or citation required repair; the node status is already `split`.
