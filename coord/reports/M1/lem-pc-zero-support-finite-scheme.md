Files written:

- `dag/nodes/sec-picard-framework/lem-pc-zero-support-finite-scheme.json`: statement, split proof, and blueprint metadata.
- `dag/nodes/sec-picard-framework/lem-pc-zero-dimensional-closed-subscheme-finite.json`: unsplit statement-only child; Mathlib search verdict: no match.

Attachments:

- None.

WANTED:

- None. The Stacks source is available by stable tags 0AYT and 06LH.

What was checked:

- The item source is Stacks Tag 0AYT, Lemma 33.33.3, parts (3)--(5). Its proof first replaces the sheaf by the coherent module on the scheme-theoretic support, then uses the zero-dimensional algebraic-scheme result, closed-pushforward cohomology, the projection formula, and affine cohomology. The item statement agrees with that route and explicitly includes the finite-dimensional algebra, closed immersion, tensor, support, and cohomology conclusions.
- The new child is Stacks Tag 06LH, Lemma 33.20.2. I checked that its hypotheses are exactly an algebraic (finite-type) scheme over a field with zero-dimensional underlying space and that its conclusions are affineness, finiteness over the field, and finite-dimensional global sections. It is statement-only as required for a new unsplit node. Whole-DAG and blueprint searches found no duplicate node or blueprint statement.
- Step 1 cites the existing finite-type support-closed node, the existing zero-dimensional closed-set finiteness node, and the existing scheme-theoretic support node. These statements supply closedness, finiteness of the underlying support, the annihilator closed immersion, equality of underlying support, and annihilation of the coherent module.
- Step 2 cites only the new 06LH child. Its statement supplies the finite morphism, affine identification with `Spec A`, and finite-dimensionality of `A`; the hypotheses are checked because the scheme-theoretic support is a closed subscheme of the finite-type scheme and has the same zero-dimensional underlying space.
- Step 3 cites the existing closed-immersion coherent-equivalence node. That node states coherence, cohomology comparison, and the tensor projection isomorphism. Pullback preserving invertibility is immediate from the local definition; invertible tensor factors preserve nonzero stalks.
- Step 4 cites the existing finite-scheme cohomology/tensor node, whose hypotheses match `A`, `G`, and `i^* N`; it supplies higher-cohomology vanishing, finite-dimensional global sections, and equality after tensoring.
- I tested edge cases mentally: empty support gives the zero algebra and zero sheaf; `X = Spec k` with `F = O_X` gives `A = k`; a skyscraper at a closed point with residue field `L` gives `A = L` and the expected finite-dimensional sections. The Mathlib searches for the new child used LeanSearch, LeanFinder, and source grep and found no exact theorem, so it remains unsplit.

## Review by M1

I read the Stacks pages for 0AYT and 06LH and compared every hypothesis and conclusion with the item and child statements. I also opened each cited DAG node: `lem-weil-pbc-finite-type-module-support-closed`, `lem-sc-dim0-finite`, `lem-weil-pbc-scheme-theoretic-support`, `lem-weil-pbc-closed-immersion-coherent-equivalence`, and `lem-pc-finite-scheme-cohomology-tensor`. Step 1 uses exactly the support and annihilator claims those nodes state; Step 2 uses the finite/affine/finite-dimensional conclusions of the new 06LH node; Step 3 uses the closed-immersion node's stated cohomology and tensor maps; Step 4 uses the finite-scheme node's stated vanishing and dimension equality. No step treats a Stacks tag as a citation without a node, and no step is marked elementary while hiding a nontrivial theorem. I searched the whole DAG and blueprint before adding the child, checked its three Mathlib search records, and corrected the initial plan to reuse the already existing scheme-theoretic support node rather than create a duplicate annihilator node.

What could not be finished:

- The new 06LH child is intentionally unsplit and has no Lean proof, as required by stage 1.
