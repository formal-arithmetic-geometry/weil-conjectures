## Files written

- `dag/nodes/sec-trace-formula/lem-trf-flat-fibre-free-neighbourhood.json`: item split, no new nodes, no Mathlib leaf.
- `citations.json`: verbatim citations for every node used in every proof step.

## Attachments

None. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item.

## WANTED

None. The complete Stacks source is present locally.

## Not duplicates

No new nodes were created. Existing inputs were checked by id and statement; the proof uses their stated conclusions without creating restatements.

## Review by Q58

I read the item against `literature/stacks-project/more-morphisms.tex`, Tag 080Q (`lemma-flat-and-free-at-point-fibre`), including the preceding explanation of the fibre-flat hypothesis and the full proof. I also read the complete statements of every cited DAG node. Step 1 uses the existing Nakayama generating criterion (Tag 00DV) exactly to turn the zero residue fibre of the finite stalk into a zero stalk, then uses the existing finite-type surjective-on-stalk theorem (Tag 01B8) on the zero map to obtain a zero neighbourhood. Step 2 specializes the existing fibre flatness criterion (Tag 00R7) to the local maps `O_{S,s} -> O_{X,x} -> O_{X,x}`; I checked the nonzero hypothesis, essential finite presentation from the morphism hypothesis, finite presentation of the stalk, and the identification of the tensor fibre with `(F_s)_x`. Step 3 applies the existing finite-flat-local-free statement (Tag 00NZ) after checking finite generation from finite presentation. Step 4 constructs the map from a finite basis of the stalk and uses Tag 01B8 exactly for spreading stalk surjectivity to an open. Step 5 applies the existing kernel finite-type statement (Tag 01BP) to the restricted finite-presentation module and surjection, and checks that the stalk kernel is zero because the chosen basis map is an isomorphism at `x`. Step 6 again applies Tag 01B8 to the zero map into the finite-type kernel, yielding a neighbourhood where the kernel vanishes. Step 7 is the elementary sheaf fact that a surjection with zero kernel is an isomorphism.

I tested the edge cases in the source argument: `r=0` is handled by the zero-stalk branch; a nonzero free stalk has `r>0`; and the zero morphisms used in Steps 1 and 6 have surjective stalk maps precisely because their targets have zero stalk. No hypotheses were added or dropped from Tag 080Q. The DAG search found no blueprint node duplicating 080Q and no existing node stating the whole item; all five auxiliary results were pre-existing nodes. I ran the required Q58 LeanFinder, Loogle, grep, and LeanSearch commands and recorded their actual results in the item JSON; none states the combined theorem.

## What was wrong or corrected

The imported item had no proof. I supplied the complete Tag 080Q proof with explicit local-ring specialization and explicit zero-kernel shrinking; no statement correction was needed.

## What remains

Nothing remains for this stage-1 split.
