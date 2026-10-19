## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-module-object-ringed-site-derived-comparison.json`: existing item split with five proof steps; no new nodes.
- `citations.json`: verbatim quotes for every cited statement in every step.

## Attachments

None.

## WANTED

None.

## What was checked

The item source is `literature/stacks-project/sites-cohomology.tex`, Tags 08J9, 08JA and 08JB, together with Section 08J7; the module equivalence and tensor comparison are the existing Stacks-derived project nodes. I read the item, the chapter and unit route, and every cited node. Step 1 uses the existing internal-module/section-module equivalence and the exact symmetric tensor comparison; those statements explicitly preserve underlying sheaves, identify relative tensors and units, and preserve and reflect K-flatness. Step 2 uses the Layer-B definition of derived internal Hom as the right adjoint of relative derived tensor, then transports its counit through the tensor comparison. Step 3 uses the ringed-site sections model, which identifies a right adjoint with the functorial K-injective Hom complex, and the ringed-site currying theorem; the K-injective construction is functorial. Step 4 is the elementary uniqueness-of-right-adjoints argument and records the evaluation normalization. Step 5 checks exact slice restriction, tensor restriction, and the RHom restriction theorem; the same module equivalence applies to the restricted ring object, so successive slice compatibility follows from naturality.

I tested edge cases conceptually: the empty site gives zero Hom and zero evaluation; the terminal site reduces to the ordinary equivalence between modules over a ring object and modules over its section ring; and U equal to the terminal object recovers the global comparison. No statement was changed, no new definition was introduced, and no SGA source was used.

## Review by NI

I checked that every step cites only statements that contain the fact used. In particular, the tensor node says exactness, unit and K-flat preservation; the derived tensor-Hom definition says the module-object right adjunction; the sections-model node says that any such right adjoint is represented by the K-injective Hom complex; and the ringed-site comparison node says both currying and restriction. The slice step uses the exact module restriction and the explicit tensor restriction statement. The proof dependencies are exactly the union of the step uses, with no cycle. The Mathlib searches for the item were run and recorded in `searches.jsonl`: grep, LeanSearch, Loogle and LeanFinder found only generic underived or closed-category declarations, so the item is not a Mathlib leaf. There are no new nodes requiring additional searches.

## What could not be finished

Nothing.
