files written:
- `dag/nodes/sec-abelian-varieties/lem-sc-finite-locally-free-residue-isomorphism.json`: item split, status split; no new nodes.
- `citations.json`: empty because both proof steps are self-contained.

attachments: none.

WANTED: none.

The item is not present in the Lean source: searches for the blueprint tag, residue-field criteria, and finite locally free terminology found no declaration stating it. The source is Stacks Tag 00O0, Lemma cokernel-flat, part (3). The local Nakayama argument is written directly as an elementary proof step, so no new node is needed.

## Review by J1

I checked the item statement against Tag 00O0(3): the hypotheses are a scheme, a morphism of finite locally free modules, and an isomorphism after tensoring with every residue field; the conclusion is that the sheaf morphism is an isomorphism. Step 1 spells out the local-ring argument: finite locally free stalks are finite free, the cokernel vanishes by Nakayama, and the split kernel vanishes after reduction and Nakayama. Step 2 is the stalkwise criterion for isomorphisms of sheaves. Both steps use only the stated hypotheses; the rank-zero and rank-one cases reduce directly to the zero and identity maps.

what was wrong in the imported item: its proof was empty; it did not expose the local criterion or the stalkwise conclusion. No source or statement error was found.

what I could not finish: nothing; the dry run passed.

## Second reading by J1

- Item statement: checked against Stacks Tag 00O0, Lemma `cokernel-flat`, part (3), after affine localization; the finite-projective ring criterion globalizes stalkwise, and the fibre is now explicitly the stalk tensor over `O_{S,s}`. Verdict: correct with the notation repair below.
- Step 1: checked each hypothesis against Tag 00O0(3): finite locally free stalks are finite free, the cokernel is finitely generated for Nakayama, the surjection splits because the target stalk is free, and the kernel is a finite free direct summand before the second Nakayama argument. Verdict: correct; the argument is now written without the previous compressed “split inclusion” phrase.
- Step 2: checked against the standard stalkwise criterion for sheaf morphisms and the conclusion of Tag 00O0(3). Verdict: correct and elementary.
- New nodes: none; there are no new-node statements to audit. A repository search found no duplicate residue-field sheaf criterion and no sorry-free Lean declaration matching the item; the recorded Mathlib searches remain in `searches.jsonl`.
- Small cases: the zero-rank case gives the zero map between zero fibres and zero sheaves; over a field the statement is ordinary finite-dimensional linear algebra; the empty scheme is vacuous; ranks one reduce to a scalar whose residue images are units.
- Changes: made the fibre notation self-contained as `E_s ⊗_{O_{S,s}} κ(s)` and expanded step 1 to justify finite generation, splitting, and the kernel Nakayama step. No mathematical hypothesis or conclusion was changed.
