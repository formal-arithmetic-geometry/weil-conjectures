# Worker report: lem-pc-tate-adelic-reciprocity

## Files written

- dag/nodes/sec-picard-framework/lem-pc-tate-adelic-reciprocity.json: item, split into eight steps; statement unchanged.
- dag/nodes/sec-picard-framework/lem-pc-tate-abstract-residue-calculus.json: new statement-only node, unsplit; no Mathlib match after four recorded searches. Abstract residue construction, ambient invariance, and basic vanishing laws.
- dag/nodes/sec-picard-framework/lem-pc-tate-residue-lattice-identity.json: new statement-only node, unsplit; no Mathlib match after four recorded searches. Admissibility and the sum/intersection identity for two arbitrary admissible subspaces.
- citations.json: twelve records, one for each cited node in each item step, with verbatim statement excerpts (whole statements where several clauses are used).
- searches.jsonl: twelve actual msearch.py invocations, covering the item and both new nodes. Each was read; no unavailable response occurred.

## Attachments and Lean searches

No attachment is claimed. The prior worker's rejected attachment is not reused. I searched the current read clone for the exact item tag and the notions, and read WeilConjectures/RingTheory/TateResidue/{Residue,ResidueProperties,LocalResidue,ResidueTheorem}.lean. The current clone does contain TateResidue.residue_theorem in ResidueTheorem.lean, and smaller constructions/properties. The explicit instruction for this continuation forbids answering ATTACH again, so this delivery is the requested natural-language split, not a renewed assertion about the rejected files or a compiler certification. Nothing was compiled.

For future formalization the lattice equation occurs as TateResidue.res_sup_add_res_inf, ResidueProperties.lean:143; TateResidue.res_eq_add_of_exact is at line 55 and res_prod at line 128. The new lattice node additionally states admissibility of both resulting subspaces, not just that equation. Basic vanishing statements are in Residue.lean:393, 401, 410 and 425. These are read-only implementation pointers, not a claim that a source check has established closure of every declaration under all its dependencies. In particular the imported local node uses [projection times multiplication, multiplication], whereas the most immediate upstream projection formula at Residue.lean:358 uses two projected multiplications; I retained the source's formula rather than silently identifying the formulas without a comparison.

## WANTED

None. Tate's paper is present locally and is the source of every non-elementary mathematical input in this split. There is no Stacks tag for the Tate abstract-residue construction used here; I cite the actual human-written primary source, not a guessed Stacks tag. No SGA source is used.

## Changes and route

The original item had no proof or proof dependencies. It already had the correct abstract finite-intersection/finite-cokernel hypotheses. I read Tate, Residues of differentials on curves, §§1–3, pp. 149–157, especially §2 Theorem 1 and R1/R2/R5 and §3 Theorem 3. I also read the current main-20261015 unit statement, the DAG unit and chapter, and the parent sk-thm-picard-duality statement. The proof realizes precisely the parent's residue-theorem clause, needed to define its cokernel trace; it neither changes Serre duality nor its route.

Tate uses completed local fields in §3. The same lattice argument works with K in each coordinate because this item's own hypotheses already give the two finite-dimensional spaces. Steps 1–3 explicitly construct the restricted product and the principal-parts quotient without completions. In particular this proof does not assume a coefficient field, residue-field separability, properness of a scheme, or an identification with curve cohomology. All are unnecessary under this item's abstract hypotheses.

## Not duplicates

The whole-DAG searches for finite-potent, Tate residue, abstract residue, the Lean names, and the sum/intersection terminology found the existing local node and parent, but no node for the two abstract statements. Whole-blueprint searches included 'abstract residue', 'admissible subspace', 'finite-potent', 'sum/intersection', 'reciprocity', 'residue theorem', and 'residue'. The parent describes the global residue theorem but does not state the abstract calculus for arbitrary modules and subspaces. The new nodes have the parent as nearest blueprint ancestor and the item in their via chain.

lem-pc-tate-abstract-residue-calculus vs lem-pc-tate-dvr-residue-calculus: the former constructs a residue for any admissible subspace of any module over a commutative algebra and states ambient/vanishing properties; the latter is a local DVR statement, including uniformizer and Laurent-coefficient formulas, and does not supply these ambient identities.

lem-pc-tate-abstract-residue-calculus vs lem-pc-tate-adelic-reciprocity: the new node involves one arbitrary admissible subspace and no indexed local rings, principal-parts map, or reciprocity conclusion. The restricted product and both finite-dimensional comparisons remain in the item's proof.

lem-pc-tate-residue-lattice-identity vs lem-pc-tate-dvr-residue-calculus: the new node concerns two admissible subspaces and their sum and intersection; the local DVR node gives no identity between residues of different lattices.

lem-pc-tate-residue-lattice-identity vs lem-pc-tate-adelic-reciprocity: the new node is the general two-subspace identity, with no finiteness assumptions on the intersection or ambient quotient and no vanishing conclusion. The item supplies those special hypotheses and the proof of local finite summation.

lem-pc-tate-residue-lattice-identity vs lem-pc-tate-abstract-residue-calculus: the first adds the non-elementary two-lattice identity R5, whereas the second supplies the single-lattice construction and R1/R2 only.

Both new nodes vs sk-thm-picard-duality: that unit is curve Serre duality, whose trace invokes global reciprocity. It does not state either abstract result, and citing it here would be circular.

## Review by NS

I reread sections B through E of coord/delivery-errors.md against the JSON and Tate's text. For B, both new statements introduce their own field, commutative algebra, module and subspaces; admissibility and finite-potent trace are defined inline in the abstract node and the differential notion is linked to the existing Kähler node. They contain no proof, no proof dependencies and no proof sketch disguised as a statement. Each has four real logged searches, two different natural-language phrasings, and exact query strings. Hits concerning field residues, number-field zeta residues, annihilators, rank identities and sums over residue classes do not give a differential residue; neither node is a Mathlib leaf. Their statements use single TeX escapes in the decoded JSON. I checked the nearest blueprint ancestor with blueprint_refs.py. No unit or chapter file is changed.

For the item I read Tate §3 Theorem 3 and its corollary on pp. 155–157. For the abstract node I read §1 T1–T5 on pp. 149–151 and §2 Theorem 1, formula (*) and R1/R2 on pp. 151–153; these supply the trace construction, restriction of ambient module and all three vanishing cases actually used. For the lattice node I read §2 R5 and its proof on p. 153. Its source number is R5; upstream Lean's different R3 numbering is explicitly distinguished. I did not infer general linearity of finite-potent trace: that would be false without a common finite-potent subspace. R5 is a separate non-elementary input precisely to avoid that gap.

Step 1 uses no theorem: I checked closure of the restricted product under addition and multiplication by a fixed scalar using unions of finite exceptional sets, and separated the empty index set before using diagonal injectivity. Step 2 cites the abstract node only for its stated admissibility condition and the local DVR node for its exact finite-dimensional quotient clause. The displayed injection into finitely many local quotients proves the global condition and works for every subfamily. The subring and finite-residue-field assumptions required by the local node are all present in the item. B is stable by the displayed multiplication identity. This is an elementary finite-dimensional bound, not an unproved product-of-lattices theorem.

Step 3 is an explicit construction with no external theorem citation: finite-support representatives give the onto principal-parts map, and its kernel is exactly A. The written inverse modulo A+B verifies the cokernel comparison, including the dependence on the range of P. I checked that the assumption on the intersection applies via the injective diagonal, and the assumption on the cokernel applies to exactly this quotient, not to a completed or infinite-product quotient.

Step 4 cites the lattice node for its exact displayed sum/intersection equation and the abstract node for its stated vanishing of stable, finite-dimensional and finite-codimensional lattices. Admissibility is established before application. The intersection and quotient finiteness have already been proved. This step does not take any theorem from the proof of a cited node.

Step 5 uses the local node's statement that the residue annihilates the image of differentials of O_i. With f,g in O_i, f dg is in that image. It establishes support before any infinite-index sum is interpreted. Step 6 cites the lattice node repeatedly on finitely many disjoint coordinate lattices. The explicit finite induction proves product additivity rather than hiding a new comparison lemma. The abstract node's ambient-restriction and isomorphism clauses say exactly what is needed to replace the coordinate lattices by their ambient K factors. Their containing modules are K-stable; zero intersections have finite dimension, so their residue is zero. Step 2's subfamily calculation and the local quotient clause verify every admissibility hypothesis. The argument does not turn an infinite product into an infinite direct sum.

Step 7 uses the abstract node's preservation vanishing on the remaining coordinates, and checks local/generic comparison using literally the same projection and commutator formula in both statements. It then uses the previously obtained finite decomposition and global vanishing; there is no unstated transport or change of residue convention. Step 8 uses the existing Kähler node's explicit free-module symbol presentation, which really does imply a finite sum of f_j dg_j. It uses the local node's k-linearity, not K-linearity of residues. The support union and both sums are finite, so distributivity suffices. citations.json has one verbatim excerpt for every use in these steps; the whole statement is quoted where several of its clauses matter.

For C and D, no cited definition is substituted for a theorem, no statement is borrowed from another node's proof, and neither new node is the item or one of its two global clauses. The finite-support proof and zero-sum proof remain in the item. Dependencies all point down: the abstract node uses the existing differential definition; the lattice node uses the abstract node; neither points back to the item or its parent. No cross-unit proof theorem is needed. The differential definition is an existing Mathlib notion, not a route change.

For E I tested zero modules and zero lattices in the abstract statement: the commutator is zero, the finite-dimensional clauses give zero, and ambient restriction has no nonzero part to lose. For the lattice identity I tested A=0, B=0 and A=B; the equation reduces respectively to the same residue on both sides, with no cancellation that fails in characteristic two. The abstract assertions require no faithfulness of the C action. For the item I tested the empty index set, empty pole set, empty complementary set, zero differential and constant f,g. Empty pole set makes all residues zero by the local node; an empty complementary set gives a zero residual module. The proof uses neither characteristic zero nor a separable residue extension, so it also covers the imperfect-field cases motivating the parent's Tate convention. I found no false imported statement and changed none.

I checked the long-step rule: all eight item steps are shorter than 2000 characters (the longest is 1151). The finite-coordinate comparison is an explicit finite induction from R5 and R1, not an omitted 'standard' lemma. This review is my direct-delivery self-check; no second worker or compiler was used.

## Unfinished work

The two new non-elementary statements are intentionally unsplit leaves of this one-level stage-1 delivery. Their later splits must realize Tate's finite-potent trace arguments. No part of the item's eight-step proof is left as an unspecified argument. Required server dry-run and push results follow from deliver.py; I will repair reported failures before pushing.
