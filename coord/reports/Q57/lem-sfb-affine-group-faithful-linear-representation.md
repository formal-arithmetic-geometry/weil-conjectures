# Stage 1 report: lem-sfb-affine-group-faithful-linear-representation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-group-faithful-linear-representation.json: statement, split; no Mathlib match. Six steps prove the coordinate map surjective and obtain all clauses. Statement and statement dependencies unchanged.
- citations.json: 18 step/node entries, each quoting the verbatim complete statement actually read. Full quotations keep their hypotheses visible.
- searches.jsonl: five fresh logged Mathlib queries for the item; results read. No previous sandbox attempt existed. Existing searches from the item's creation were read and the same questions were rerun under Q57 to establish this sandbox's own search log.
- report.md: this report. No new DAG nodes, Mathlib leaves, Lean files, or unit changes.

## Attachments

None. Searched lean/WeilConjectures for the exact item id and the blueprint tag, faithful representations, comodules and Hopf algebras; read GroupScheme/GeneralLinear.lean and GroupScheme/GeneralLinear/Representation.lean. The latter assumes a given rational representation and its simplicity notions require algebraically closed characteristic zero coefficients. It does not construct an embedding for an arbitrary affine finite-type group scheme.

## WANTED

None. Milne's Algebraic Groups is present, and all supporting Stacks text is present.

## Findings and corrections

The imported statement is correct, including nonreduced group schemes and arbitrary imperfect base fields. No STATEMENT-DISPUTED correction is needed. The previous item had no proof. I kept Milne's coordinate-surjectivity route rather than introducing a node restating the embedding or relying on injectivity only on rational points. Including 1 in the finite generating subset ensures a positive-dimensional representation, even if the algebra has an empty generating list.

Existing nodes suffice: lem-sfb-comodule-finite-subcomodule, lem-sfb-affine-group-coordinate-hopf, lem-sfb-rational-representation-comodule-dictionary, lem-pc-affine-finite-type-algebra and lem-weil-pbc-closed-immersion-affine-cover-criterion. Whole-DAG searches by both ids and concepts also found the finite-subrepresentation and coefficient-coalgebra nodes. I use the general finite-subcomodule node, and do not duplicate any of them. Whole-blueprint searches for comodule, faithful representation, linear representation and faithful found no statement asserting this embedding over arbitrary fields. The existing blueprint's linear-algebraic-group block fixes a characteristic-zero algebraically closed field and begins with a given matrix group.

The ancestor command reports None for this inherited supporting chain. I retained the item's existing blueprint.from, including its precise long place and via list. The current latest blueprint unit and direct-image proof were read: the item is a supporting linearity fact deep below the inherited alteration argument, and this split does not change the unit or chapter route.

## Tool use

lem-pc-affine-finite-type-algebra is a generic tool from another unit: it translates affine geometric finite type into finite generation of the coordinate algebra (Stacks 01T2). It is declared in split_report.tool_uses. Its statement has exactly the hypotheses here, and the current unit has no replacement for that implication. The other non-Mathlib statements used belong to the item's own unit; definitions and Mathlib leaves are generic notions/tools.

## Unfinished work

None for this one-level split. New node count: 0. New Mathlib leaf count: 0. Existing prerequisites retain their independent proof status.

## Not duplicates

No new nodes. Existing finite-subcomodule, rational-representation dictionary, Hopf algebra and affine closed-immersion criterion are cited directly.

## Review by Q57

I read Milne, Algebraic Groups, Theorem 4.9 and Corollary 4.10, printed p.87 (PDF p.99), Proposition 4.7, p.86, and the definitions and Remark 4.1 on pp.83–84. I also read Corollary 3.35 on p.75, but the split does not invoke its nontrivial kernel-to-closed-immersion direction: the ring surjection is established explicitly, and pointwise injectivity follows by cancellation of that surjection. I read Stacks morphisms.tex, lemma-locally-finite-type-characterize (01T2), and lemma-closed-immersion (01QO), and checked their tag mappings. No SGA source is used.

Step 1 uses the full statement of lem-sfb-affine-group-coordinate-hopf: it gives both counit laws, coassociativity and the identification of G with its spectrum without smoothness or reducedness. The statement of lem-pc-affine-finite-type-algebra applies to this affine finite-type k-scheme and yields exactly finite generation, interpreted by def-weil-pbc-finite-type-algebra. The statement of lem-sfb-comodule-finite-subcomodule allows an arbitrary coalgebra and every finite subset, so it applies to the regular coaction and the set including 1. Its conclusion supplies an actual restricted coaction and the inclusion compatibility used later. This is stronger than just a finite-dimensional subspace, which would not suffice.

Step 2 uses the finite-span definition in def-weil-finite-dimensional-subspace, with elementary deletion of dependent vectors to obtain a finite basis. The Hopf node says the counit preserves 1, proving 1 is nonzero and the basis has positive size. The coefficient maps are written using the tensor universal property in def-weil-pbc-module-tensor-product; no tacit infinite expansion or choice of algebra-valued density is involved.

Step 3 uses the statement of lem-sfb-rational-representation-comodule-dictionary, read in full: its G hypotheses are exactly affine finite type over a field, its finite-dimensional clause produces a group-scheme homomorphism, and its explicit evaluation formula gives the matrix entries. The spectrum and general-linear-group definition statements identify the coordinate map. Evaluation at the universal H-point proves phi(x_ij)=a_ij, including nilpotents, without relying on equality of k-point functions. There is no change from an abstract-group representation to a group-scheme representation hidden here; the dictionary explicitly supplies that assertion.

Step 4 is the actual argument of Milne Theorem 4.9. I checked the counit is applied on the first factor of Delta(e_j), whereas the regular right-comodule axiom in Step 1 used the second factor. Both identities occur in the Hopf node's statement. The linear combination e_j=sum epsilon(e_i)a_ij places V and then all algebra generators in the image. Polynomial evaluation explicitly lifts every element. This is a short elementary calculation from the cited tensor and algebra-generator definitions, rather than a new lemma restating the item.

Step 5 cites clause (2) of the affine-cover criterion, whose entire statement is quoted in citations.json. It is applied to one affine open, the entire target. Its preimage is affine because G was assumed affine, and its section map is exactly the surjection just proved. This checks every hypothesis of Stacks 01QO and gives a closed immersion independently of the faithful-kernel criterion.

Step 6 uses the spectrum definition's bijection between affine morphisms and ring homomorphisms. Precomposition with a surjection is injective by the explicit lift argument for each h. I checked the affine fibre-product statement gives precisely the tensor-product coordinate rings for extension of k to K, and the tensor-pushout statement gives the map phi tensor 1. Finite sums of pure tensors lift term by term, so no flatness or descent theorem is silently invoked. The same cancellation proves injectivity for every K-algebra, not just field-valued points.

Edge cases checked: the trivial group (H=k, take V containing 1, m at least 1); empty algebra-generator list; a nonreduced group such as alpha_p or mu_p (the coaction and coordinate proof retain nilpotents); positive characteristic; finite and imperfect fields; arbitrary and nonreduced value algebras, including the zero algebra; arbitrary field extension K/k. There is no use of smoothness, connectedness, reducedness or perfectness. Every proof step is below 2000 characters (maximum 987), and each contains one assembly or explicit elementary computation without an unrecorded standard sublemma. No new statement-only node was necessary, so the new-node requirements B1–B9 and duplicate-pair check are vacuous. For C1/C4 I opened every cited node and used only its statement; citations.json contains verbatim quotations for all 18 pairs. Proof dependencies equal the union of the step uses. D1/D2 are avoided by carrying the embedding argument in the item's own steps, not in a new copy of its conclusion. No cyclic dependency is knowingly introduced; the server dry run remains the mechanical authority.
