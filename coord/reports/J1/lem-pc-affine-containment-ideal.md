1. Files written:
   - `dag/nodes/sec-picard-framework/lem-pc-affine-containment-ideal.json`: split into four proof steps; no new nodes.
   - `citations.json`: verbatim quotes for the two cited nodes.

2. Attachments: none.

3. WANTED: none.

4. The item had no sorry-free Lean declaration and no existing DAG node stated the affine coefficient-ideal criterion. The imported statement and its Stacks source are consistent. I did not create a child node because a coefficient-ideal lemma would restate the item's own conclusion. The proof now makes the finite dual-system construction, base-change evaluation, and both implications explicit.

5. No Lean was written or compiled. The required dry run passed: `deliver.py J1 lem-pc-affine-containment-ideal --no-push` printed `OK (not pushed)` at preflight commit `7fe4075a`.

## Review by J1

I read the item's source, Stacks `pic.tex`, Lemma 44.2.7 (Tag 0B97), and the existing `lem-pc-hilb-containment-locus` proof that invokes this affine lemma. Step 1 uses `def-weil-pbc-projective-module`; its statement supplies the direct-summand description of a projective module, from which finite generation gives the finite dual system. Step 2 uses the declared generic tool `lem-sc-ext-evaluation`; its statement is the canonical evaluation isomorphism for finite locally free modules, applied on `Spec(R)` and after scalar extension, which gives the displayed Hom base-change identification. Steps 3 and 4 are the two elementary implications: vanishing of the tensor image kills all coefficient generators, while the dual-system identity reconstructs every `j` from those coefficients. I checked that the hypotheses quantify over an arbitrary ring map `R -> R'`, that `J` is an ideal of `B`, and that the conclusion uses the image of `K` in `R'`. The small cases `J=0`, `K=0`, and `B=R` reduce to immediate zero or principal coefficient tests. The final preflight accepted the split and its citations.

## Second reading by J1

- Item statement: checked against Stacks `pic.tex`, Lemma 44.2.7, Tag 0B97; finite projectivity is now explicitly linked to `def-weil-pbc-projective-module`; verdict: correct.
- Step 1: checked against the finite-projective direct-summand statement and the dual-basis construction; verdict: correct.
- Step 2: checked as the forward implication directly from the induced tensor functional; verdict: correct and elementary.
- Step 3: checked as the conclusion of the forward implication; verdict: correct and elementary.
- Step 4: checked against the tensor of the finite dual-system identity; verdict: correct and elementary.
- New nodes: none; no child node was introduced because the dual-system criterion is the item's own content.

Changes: removed the unsupported `lem-sc-ext-evaluation` citation and its affine Hom base-change claim; the proof now uses only the dual-system identity and direct tensor maps. Added the missing projective-module statement dependency and removed the stale citation entry.
