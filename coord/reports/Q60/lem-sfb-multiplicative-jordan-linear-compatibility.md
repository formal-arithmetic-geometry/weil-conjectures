1. Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-multiplicative-jordan-linear-compatibility.json`: item split into six proof steps; original statement retained in full.
- `dag/nodes/sec-six-functors-basics/lem-sfb-generalized-eigenspace-direct-sum.json`: one new statement, a Mathlib leaf, for primary direct-sum decomposition and stabilization at the dimension. No proof or proof dependencies are put in this leaf.
- `citations.json`: verbatim supporting statement for every cited node in the item.
- `searches.jsonl`: actual msearch receipts, retained from the initial session. No searches were repeated on resumption.

2. Attachments

None. Searches in `lean/WeilConjectures/` by the item's blueprint id and Jordan/unipotent/semisimple terminology found no declaration stating this item. `LinearMap.trace_pow_eq_sum_pow_roots_charpoly` uses a primary decomposition internally but states a trace identity, so is not an attachment. Mathlib's additive Jordan-Chevalley theorem is not an attachment or an exact match for the item.

3. WANTED

None. The source is present as `literature/milne-algebraic-groups_iAG2017.pdf`.

4. Issues and changes

The item had no proof. Its statement is correct, including arbitrary characteristic and the zero vector space, and is unchanged. Milne 9.11 is stated over a perfect field, whereas the item asks only for the algebraically closed specialization. The Galois descent and polynomial-expression clauses of that theorem are therefore unnecessary here. The proof uses primary spaces as in Milne, with a direct uniqueness argument on an eigenbasis of a competing semisimple factor. This expands the argument without adding a polynomial interpolation prerequisite. The tensor-primary inclusion that Milne 9.15 states without calculation is proved explicitly by commuting operators X and Y.

I read the chapter/unit records and the current latest blueprint unit and direct-images proof. The inherited dependency chain runs through the alteration/moduli input to Milne 19.16 and 9.19. `blueprint_refs.py ancestor` returns None for this long created-node chain. I retain the item's inherited null ancestor and exact place/via information, extend it to the new leaf, and record that fact in split_report. The current blueprint names the direct-images node with `sk-` where the inherited place names `det-`; no route or target is changed.

5. Unfinished work

No mathematical gap is left in the item. The supporting node is a Mathlib leaf, so creates no additional unsplit item. Required delivery checks follow this report.

## Not duplicates

lem-sfb-generalized-eigenspace-direct-sum vs lem-sfb-invariant-complements-eigenspace-span: the existing node requires invariant complements and concerns ordinary eigenspaces; the new leaf concerns generalized eigenspaces of any endomorphism and their direct-sum uniqueness and dimension bound, without any complement/semisimplicity hypothesis.

lem-sfb-generalized-eigenspace-direct-sum vs p-linear-triangular: the existing node gives an invariant complete flag and triangularization; it does not state the primary direct-sum decomposition or its dimension bound.

lem-sfb-generalized-eigenspace-direct-sum vs lem-sfb-multiplicative-jordan-linear-compatibility: the new leaf is a theorem about additive generalized eigenspaces for arbitrary endomorphisms. It asserts no multiplicative factors, no intertwiner law, and no tensor law. All three arguments remain in the item's proof. Whole-DAG searches by primary/generalized eigenspace, Jordan decomposition, and the three Mathlib declaration names, and blueprint searches by Jordan, generalized eigenspace, and primary space found no existing statement of this leaf. The occurrence of the decomposition in the proof of the trace theorem is not a node with this statement.

## Review by Q60

I read Milne Proposition 9.9 on printed p.167, the algebraically closed case of Theorem 9.11 on pp.168-169, and Propositions 9.13 and 9.15 on p.169. For the new leaf I also read Mathlib Eigenspace/Triangularizable.lean:75-76, Eigenspace/Basic.lean:602-607 and 714-716, with the membership definitions at 91-92 and 551-552. These give exactly spanning, independence, and the dimension exponent. The field is algebraically closed and the vector space finite dimensional, as the spanning theorem requires; vector spaces over fields satisfy the domain/torsion-free hypotheses of independence. Maximal generalized eigenspaces are exactly the explicitly defined spaces in the new node, rather than ordinary eigenspaces. Each search recorded in that node occurs in the msearch log; both semantic services, Loogle, and source grep were available. The second semantic phrasing for the item again yielded additive decomposition and semisimple commuting-product results, not the full item.

In step 1 the cited leaf says V is the internal direct sum and gives the dimension bound. Invertibility excludes the zero primary space by applying A inverse to a vanishing power. This is the only structural input to the construction. Step 2 uses the direct-sum decomposition already obtained in step 1 to define the factors block by block: the eigenbasis is the union of bases of the blocks; the inverse is scalar multiplication by a inverse; the displayed formula for U minus 1 gives the nilpotence exponent. Step 3 cites the definition of E_a from that same leaf: every eigenvector of a competing semisimple part belongs to the primary space because (A-a)^r equals a^r(U'-1)^r on its eigenspace. This identifies S on a whole basis and then U by cancellation. No unsupported simultaneous-diagonalization or uniqueness theorem is used. Step 4 cites the same definition; the induction explicitly proves that f preserves primary spaces, with no injectivity or surjectivity hypothesis on f. Multiplying the semisimple intertwining equation by the two inverses gives the stated inverse identity and hence the unipotent law.

Step 5 takes precisely the dimension bounds from the cited leaf, applied to A and B. The tensor map C is first checked invertible and finite dimensional so that the construction already proved applies to it. The displayed X and Y preserve H_{a,b}, commute, and have the vanishing powers claimed, as follows on generators. Their sum is C-ab; expanding into words proves nilpotence without a binomial-coefficient division, so positive characteristic causes no exception. Step 6 uses that proved inclusion and the construction of C_s: both semisimple maps act by ab on each H_{a,b}, those spaces span by primary expansion and bilinearity, and the unipotent identity follows from the explicit inverse. No new theorem is hidden in this final equality of linear maps on spanning pure tensors.

I checked the zero space, a one-dimensional scalar automorphism, A=identity, a nontrivial unipotent Jordan block in positive characteristic, and colliding products ab=a'b' in the tensor assertion. Empty bases and exponent 1 handle dimension zero; one-dimensional blocks have U=identity; for unipotent blocks S=identity; collisions do not matter because equality is checked on a spanning family, never on an asserted direct sum of the H_{a,b}. The node makes no claim that arbitrary products of noncommuting unipotent maps are unipotent. All uses of a inverse occur only on nonzero primary spaces of an invertible map.

Against delivery-errors B-E, the only new node is self-contained, statement-only, not a restatement of a clause, and a verified Mathlib leaf. The cited statement was read directly and copied verbatim into citations.json. Proof dependencies equal the union of uses; the new leaf depends only on the field definition, so there is no cycle back to the item. There is no off-unit non-Mathlib tool. Every step is below 2000 characters. The expanded tensor argument and eigenbasis uniqueness argument are direct computations from the stated definition and the preceding construction, rather than appeals to unnamed compatibility lemmas. No Lean file was written and no compiler, Lake or build command was run. Only sandbox files were written.
