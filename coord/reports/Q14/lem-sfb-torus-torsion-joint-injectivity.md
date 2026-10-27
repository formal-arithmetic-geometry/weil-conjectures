## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-torus-torsion-joint-injectivity.json`: item split; statement unchanged; no exact Mathlib match.
- `citations.json`: the quotient-kernel sentence quoted verbatim for step 5.
- `report.md`: this report.

No new nodes; no Mathlib leaves created. The five proof steps total under 2000 characters, and each step is under 600 characters.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the blueprint id, torus/torsion wording, joint injectivity, and Laurent/AddMonoidAlgebra notions. The projective-space Laurent coefficient and Cech declarations concern different objects; none states detection by all ideals $(t_i^n-1)$.

## WANTED

None. Milne's book and the current blueprint were available locally.

## Problems found and changes

The imported item was statement-only and had no argument. Its arbitrary commutative coefficient ring and rank-zero clause are correct; I did not change the statement or add reducedness, domain, field or characteristic hypotheses. I expanded the elementary content of Milne's family-injectivity assertion, rather than assuming that tensoring an arbitrary jointly injective family remains jointly injective.

The existing `blueprint.from.node` is null even though its `place` and `via` contain its full supporting ancestry. `tools/blueprint_refs.py ancestor` reports None for this item. I retained those inherited fields; the existing place is specific, not unspecified. Searches of the whole blueprint for Laurent, torsion quotients and residue class found no equivalent blueprint assertion, so `same_as` remains empty. I read the latest blueprint unit and its direct-images proof (3); this is the inherited elementary algebra input below that proof, not a replacement of the unit's route.

I preserved the inherited item searches and added the five searches actually run for Q14, as recorded in `searches.jsonl`. Both natural-language phrasings were read. LaurentPolynomial localization and embeddings, p-adic coordinate detection and ZMod characters do not state this result. In particular, `AddMonoidAlgebra.mapDomain_injective` (Mathlib/Algebra/MonoidAlgebra/MapDomain.lean:53) requires injectivity on the entire exponent domain; reduction modulo n is not injective there. `Finsupp.lmapDomain_disjoint_ker` (Mathlib/LinearAlgebra/Finsupp/Supported.lean:247) concerns a fixed map injective on a prescribed support and supplies neither a separating modulus nor annihilation of the generated torsion ideal, so it is not a one-line specialization giving the item. Its elementary support calculation is written explicitly in step 4.

## Unfinished work

None in the mathematical split. Required server validation and push follow this report.

## Not duplicates

No new nodes, hence no new/existing node pairs sharing a tag. The existing univariate `def-weil-laurent-polynomial-ring` assumes a field and describes a subring of its rational function field; it does not state this item. This item already defines multivariable formal Laurent sums over any commutative ring inline. Whole-DAG searches found the existing torus-rigidity parent, which uses this item, not an independent statement proving it.

## Review by Q14

I read Milne, Algebraic Groups (2017), Theorems 12.33 and 12.36 on printed pp.243--244, including their proofs. The former reduces schematic density to coefficient-ring quotient maps and calls their family injectivity obvious; the latter needs it after adding the parameter algebra. My proof makes precisely that coefficient argument explicit for any B. There is no appeal to geometric points, roots of unity being distinct, finite-group averaging, or preservation of infinite products by tensor product. No SGA source is used. There are no new-node sources to review.

For step 1 I checked the empty coordinate set directly: its only exponent is the empty tuple, and the empty generating family generates the zero ideal. Step 2 introduces only finite sums of coefficients already present in the statement. Addition is checked on the union of finite supports with zeros inserted, and scalar multiplication distributes; no new module or algebra existence theorem is used. Step 3 reindexes a finite sum by the explicit translation u to u+n e_i, which preserves residues; consequently each multiple h_i(t_i^n-1) has zero residue sum. Writing elements of a finitely generated ideal as finite sums of these multiples proves annihilation of the whole ideal, not just its generators. These steps cite no node because their arguments are the definitions and finite-sum identities written there.

For step 4 I checked that the maximum defining M exists because the support and coordinate set are finite. With n=2M+1, divisibility and the bound |u_i-v_i|<n force each difference to be zero. Thus the residue sum isolates exactly the coefficient of u, and membership in J_n kills it by step 3. This does not cancel any coefficient and needs no domain assumption. All ingredients are elementary finite-set arithmetic and the formal coefficient convention of the statement. In step 5 I opened `def-weil-pbc-algebra-hom-quotient` and checked its actual statement, which explicitly says the quotient map is a homomorphism with kernel J. Its hypotheses hold with D=L_B, R=B and J=J_n. The resulting equivalence is q_n(f-g)=0 iff f-g is in J_n, followed by the intersection calculation. The exact kernel sentence is copied into citations.json without changing its TeX escapes. This is the only node cited in proof steps, and proof_deps is exactly its union of uses; the same node suffices for the statement's quotient notion.

I checked B=0, r=0, a single monomial, negative exponents, B=Z/4Z with nonzero nilpotent coefficient 2, and B=F_p with n divisible by p. Translation and coefficient isolation work in each case. For example 2(t^{-1}-t) can disappear at the modulus 2, but choosing modulus 3 separates its two exponents and detects it. This illustrates why the modulus depends on the support and why injectivity for each single n is not asserted. No inverse of n is used even in characteristic p.

Against delivery-errors B--E: no new statement-only node hides a proof, no new elementary or duplicate lemma was introduced, and no clause was relabelled as a new node. The item contains the full coefficient argument, so the split is not circular or a mere application of a restatement. Every object is defined in the statement or explicitly in a step. All five steps are elementary with their calculations shown, and all are below the long-step threshold. I checked the unique cited statement for C4 and found no uncited non-elementary input for C1. The only correction during review was to defer rank-zero joint injectivity to step 5, where the quotient-kernel definition is explicitly cited. The target, source intent, statement dependencies, and unit route are unchanged.
