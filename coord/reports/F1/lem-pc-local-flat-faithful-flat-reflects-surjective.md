Files written:

- `dag/nodes/sec-picard-framework/lem-pc-local-flat-faithful-flat-reflects-surjective.json`: item, statement, Mathlib leaf.
- No new nodes.

Attachments:

- None.

WANTED:

- None.

What was checked:

- The item node was read against its source entry and its existing statement dependencies. The statement introduces a flat local homomorphism of local rings, identifies it as faithfully flat, and applies faithful flatness to the induced tensor map on modules.
- The Mathlib source was read at `Mathlib/RingTheory/Flat/FaithfullyFlat/Algebra.lean:60`, where `Module.FaithfullyFlat.of_flat_of_isLocalHom` assumes local source and target rings, flatness, and an `IsLocalHom` algebra map, and concludes faithful flatness. This is exactly the first clause after viewing the ring homomorphism as an algebra map.
- The Mathlib source was read at `Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean:392`, where `Module.FaithfullyFlat.lTensor_surjective_iff_surjective` states that the left-tensor map is surjective if and only if the original linear map is surjective. This supplies the second clause for the module tensor map.
- The existing searches in the node include LeanSearch, Loogle, and a Mathlib source grep, and their declarations were verified against the source signatures. The small identity-map case and a field extension case satisfy both clauses directly. No proof steps remain, so `citations.json` is the empty list.

## Review by F1

I checked the item source and the two cited Mathlib declarations line by line. The first declaration supplies the precise local-flat hypotheses and faithful-flat conclusion; the second supplies the precise equivalence needed to reflect surjectivity after tensoring. The item already cites the three definitions needed to state the result, and no additional mathematical fact is used. I searched the project source for the blueprint tag and for the declaration names and found no project declaration stating this item. I also checked the identity and field-extension cases, and corrected the node from `unsplit` with a null Mathlib match to a Mathlib leaf with one declaration recorded for each clause. Since the item is a leaf, there are no proof-step citations or new nodes.

What could not be finished:

- Nothing.
