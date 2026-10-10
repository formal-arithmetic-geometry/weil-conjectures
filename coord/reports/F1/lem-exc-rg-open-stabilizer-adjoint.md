1. Files written:

- `dag/nodes/sec-curve-estimates/lem-exc-rg-open-stabilizer-adjoint.json`: item split; no new nodes; no Mathlib match.

2. Attachments: none.

3. Source checked: `literature/stacks-project/injectives.tex`, Tag 04JF (`lemma-G-modules`), lines 409-430, for the item's source proof.

4. What was checked and corrected: the imported item statement was retained. Its three proof steps now expand the exact Tag 04JF route: identify the forgetful functor on morphisms, verify that open-stabilizer elements form an invariant submodule, and prove the adjunction by restriction and inclusion of Hom sets. No fact is hidden behind a new node or an uncited Stacks tag. The generic injective terminology is retained only as the item's stated dependency and is declared as an off-unit tool use.

5. What could not be finished: the proof is complete at the natural-language stage; no Lean declaration exists for this item.

## Review by F1

I read the repository source `literature/stacks-project/injectives.tex`, Tag 04JF (`lemma-G-modules`), lines 409-430, and checked the item against its proof identifying `v` and `u(M)`. The statement's hypotheses are unchanged: arbitrary topological group, arbitrary ring, open stabilizers, equivariant linear maps, and the open-stabilizer submodule. Step 1 uses the category definitions for full faithfulness, then uses the kernel argument: for a monomorphism `f`, its kernel is an object of `\mathcal D_{R,G}`, so the kernel inclusion vanishes; this proves the underlying map is injective and therefore its underlying `R[G]`-map is monic. Step 2 checks each hypothesis needed for `u(M)`: intersections of open stabilizers are open for sums, scalar multiples retain an open stabilizer, and conjugation by a group element preserves openness, giving an induced action. Step 3 checks both directions of the Hom correspondence explicitly; an equivariant map from an open-stabilizer module lands in `u(M)`, while inclusion gives the converse, and both operations are natural. I also read the cited definition source for `def-sp-injective-resolutions`; it is used only to fix the meaning of injective objects. I searched the DAG, blueprint references, and both Lean source trees for the item id, Tag 04JF, and open-stabilizer adjunction; no existing proof or sorry-free Lean declaration was found. Small cases checked were the trivial group (where `u` is the identity), a finite discrete group (all stabilizers open), and the zero module.
