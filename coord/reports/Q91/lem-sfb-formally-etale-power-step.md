# Q91: lem-sfb-formally-etale-power-step

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-formally-etale-power-step.json: statement, split; seven elementary steps, no Mathlib match for the whole item.
- citations.json: verbatim statement of the sole cited definition for each of the seven steps.
- report.md and searches.jsonl: review and actual search records.

New nodes: 0. New Mathlib leaves: 0. The statement and statement dependencies are unchanged. No existing metadata was removed.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and the notions formally etale and infinitesimal lifting. The declarations found concern differential comparisons, residue fields, localizations and other lifting problems; none states all the clauses of this item. The item is not attachable.

## WANTED

None. The source is available locally.

## Findings and route

Read literature/stacks-project/algebra.tex, label lemma-formally-etale-lift-infinitesimal, Tag 0H1D (lines 41257–41290), including its proof. The dotted arrows and the uniqueness assertion are the route here. The source leaves the factorization and inverse checks short; the delivery writes them out. No false statement was found. In particular one must not claim that ell(J) is killed modulo I^n: for n>1 that need not hold. Instead, if ell(j) is represented by a, apply f_n to the lifting equality to show phi(a)-j belongs to J^n, and then use J^n contained in J to deduce a belongs to I.

Read the chapter record sec-six-functors-basics and the unit record sk-thm-sf-ctf-stability, and the current latest blueprint unit and direct-images proof in literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/. The inherited ancestry records the tangent-cone comparison beneath alteration reduction. The latest unit is higher level and its direct-images proof (3) assembles compactification. This local quotient calculation does not change that route. The item is not the unit's key statement; no unit record was changed. The ancestor command returns None, matching the existing blueprint.from.node = null. Kept the detailed existing from.place and via, and confirmed same_as = [] by blueprint searches for formally etale, infinitesimal, and 0H1D.

Searched the DAG by 0H1D and by infinitesimal quotient / successive inverse terminology. The parent lem-sfb-augmented-etale-associated-graded uses this item for its induction; citing it backwards would be circular. Its sibling lem-sfb-power-quotient-graded-comparison assumes the quotient isomorphisms and proves the graded consequence, so it does not supply this step. lem-sfb-nodal-graph-cone-chart applies the parent to graph charts. None needs duplication. No new node is appropriate for a one-line specialization of the assumed lifting bijection or for quotient representative arithmetic.

The actual Q91 Mathlib searches, recorded in searches.jsonl and appended to the node, include two different LeanFinder phrasings, Loogle, LeanSearch and two greps. Read Mathlib/RingTheory/Etale/Basic.lean:77–94: comp_bijective and iff_comp_bijective give exactly the hypothesis already assumed, not the quotient factorization and inverse identities. LeanSearch also found Ideal.Quotient.liftₐ and adic-completion lifting results; the former constructs a quotient map after vanishing is proved, and the latter need a complete target and compatible entire families. Neither proves the item in one line. Also read the quotient-algebra reduction formulas in Mathlib/RingTheory/Ideal/Quotient/Operations.lean. The original Q31 search records are retained as historical evidence, and no unrun searches were added.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs.

## Review by Q91

I checked the seven steps directly against the source above and opened the full statement of def-weil-pbc-algebra-hom-quotient. That statement explicitly supplies algebra structure maps and their commutation rule, ideal multiplication and powers, square-zero meaning, and surjective quotient maps with the specified kernels. These are exactly the definitions cited by each step, and citations.json copies their full statement verbatim. No theorem is being taken from the proof of another node.

Step 1 uses the kernel description I = phi inverse-image J and the definition of ideal powers to show f_m is well defined by products, sums and multiples. It checks that the given inverse g_n is an A-algebra map on images of all a in A, so Step 3 has the right kind of input. Reduction squares commute on representatives.

Step 2 uses those same quotient and product definitions: the kernel of r_n is I^n/I^(n+1), and the displayed two representative maps explicitly identify E/N with A/I^n. Both independence-of-representative checks follow from the stated ideals. The inequality 2n >= n+1 is valid precisely because n >= 1; it makes the kernel square zero. This uses neither Noetherianity nor a hidden ideal-image equality.

Step 3 directly instantiates the item's bijection with the E,N just checked. Its surjectivity supplies ell and its injectivity supplies uniqueness. This is elementary because the theorem is already a hypothesis, not an uncited formal-etaleness theorem. Composing the given algebra maps preserves the required A-structure by its defining commutation identity.

Step 4 checks membership in I using the equality after f_n, not a nonexistent identification of J with IC. Products of n+1 such images vanish modulo I^(n+1), and finite sums and multiples account for every element of J^(n+1) by ideal multiplication. Step 5 defines the quotient map on representatives, with well-definedness supplied by precisely that vanishing; ell(phi(a)) = [a] is the algebra-homomorphism identity. Thus the left inverse is checked on every class.

Step 6 applies injectivity of the SAME stated hypothesis to E' = C/J^(n+1), N' = J^n/J^(n+1). The square-zero and quotient-identification checks are those of Step 2 with C,J in place of A,I. The displayed composition calculation uses s_n f_(n+1) = f_n r_n from Step 1 and f_n g_n = id from the hypotheses. Both maps compared have domain C and codomain E', as required. Equality descends to all quotient representatives and proves the right inverse. Step 7 evaluates on every [c] to prove reduction compatibility, including the exact orientations of r_n and s_n.

Small cases checked: n=1 gives I/I^2 and J/J^2 as square-zero kernels, with no use of n>=2. For phi=id on k[t], I=J=(t), the map is the identity at every level, including the possibly nonzero classes of t. For A=k, C=k times k, phi diagonal and J=0 times k, one has I=0 and J not equal to IC; ell is the first projection, J is idempotent, and all claimed quotient maps are identities on k. For I=A and J=C all quotients are the zero ring and the construction still works. For I=J=0 and f_n an isomorphism the kernels vanish and uniqueness gives the same inverse immediately. The proof never uses finite generation, properness of the ideals, nonzero rings, or J=IC.

I reviewed delivery-errors B through E: the statement introduces every object, the single definition dependency actually defines every notion used, Tag 0H1D and its label were verified in the source and tag table, no new node hides a proof, no Mathlib claim exceeds the declaration read, and no non-elementary external fact is omitted. Each step is a short explicit calculation or an instance of an assumption (maximum 408 characters); no step hides a lemma requiring a new node. There is no circular dependency and no statement repair was needed.

## Unfinished work

None in this stage-1 split. No Lean was written and no compiler, Lake or build tool was run. Dry-run and delivery results are supplied by deliver.py.
