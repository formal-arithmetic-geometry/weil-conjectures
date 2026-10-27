# Stage-1 delivery: lem-sfb-chevalley-unipotent-polynomial-coordinates

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-unipotent-polynomial-coordinates.json: existing statement, now split in ten steps; no statement change.
- dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-nonopposite-exponential-commutator.json: new statement-only lemma; no Mathlib match, unsplit.
- citations.json: verbatim statements/formulas for all step citations. searches.jsonl records the searches actually executed. This report accompanies the delivery.

One new node, zero Mathlib leaves. No Lean was written or compiled, and no repository or launcher file was changed.

## Attachments

None. Searched the live WeilConjectures source by the exact blueprint tag and by Chevalley, unipotent, root commutator and divided-power language. The hits concern Chevalley constructibility, matrix commutator Lie algebras, and elementary triangular category matrices. No project declaration states this item or the new exponential commutator lemma.

## Wanted literature

WANTED: Steinberg, Lectures on Chevalley Groups, integral construction and Chevalley commutator relations (edition and lemma numbering to be verified), for lem-sfb-chevalley-nonopposite-exponential-commutator.

Milne's available book was read with pdftotext at printed pp.508-511. Theorem 23.71 gives the bracket constants; equation (153) gives the integral exponential, but the proof of 23.72 explicitly omits the group-construction details. The two-root polynomial commutator input is therefore honestly a new unsplit statement, not a theorem claimed to follow just by citing 23.71. Its future argument should calculate in the rank-two root systems A1 x A1, A2, B2 and G2, then compare the integral polynomial coefficients; neither analytic exponentials nor division by 2 or 3 after base change will suffice.

## What was wrong or missing

The item was unsplit, rather than already proved. Its statement is retained in full. A field-points uniqueness argument would not have proved the stated scheme-theoretic assertion. This split instead supplies explicit polynomials in ambient matrix entries recovering all root coordinates, proving surjectivity of the coordinate-algebra map. The full weight condition is used: faithfulness over Q alone would not justify that a root vector survives modulo a bad prime. Primitive coroots and Z Omega = P provide the missing argument.

The newest blueprint at literature/blueprint/latest (main-20261024) was consulted, including sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, clause (3). This item is deep inside the recorded supporting alteration/algebraic-group chain; no chapter, unit route or unit realization is changed. tools/blueprint_refs.py ancestor returns None, as the imported current parent chain records; that null ancestor and the full inherited via chain are retained, with this item prepended for the new node. The exact immediate source is Milne's omitted one-sign-coordinate verification, not a new claim that the blueprint directly states Chevalley construction.

## Not duplicates

lem-sfb-chevalley-nonopposite-exponential-commutator vs lem-sfb-chevalley-rank-two-straightening: the existing statement gives additive integral linear combinations for the difference of two individual divided-power monomials, with a lower-degree condition. It does not give a multiplicative factorization of the entire exponential commutator into higher-root exponentials with integral scalar parameters. That difference is needed for closure of finite products under collection.

lem-sfb-chevalley-nonopposite-exponential-commutator vs lem-sfb-chevalley-opposite-rational-collection: the existing statement concerns a localized product of full opposite-sign root words, with torus factors and denominators. The new lemma concerns two distinct nonopposite roots, no torus or localization, and a polynomial identity over Z.

lem-sfb-chevalley-nonopposite-exponential-commutator vs lem-sfb-chevalley-unipotent-polynomial-coordinates: the new statement is a local two-root identity, valid even for nonfaithful representations and lattices without full weight generation; it asserts no closed immersion, unique coordinates, subgroup image or triangularity. The item's ten steps carry those arguments.

Searched all DAG node titles/statements and the blueprint with Chevalley, root, commutator, weight lattice, exponential, polynomial root, nonopposite, root subgroup and commutator identity. No existing blueprint node states the new identity. The existing rank-two and root-base nodes were opened; the two root-base lemmas are reused, not duplicated. No Stacks tag is assigned to the new Lie-theoretic identity. Stacks Tag 01QO is used only through the existing closed-immersion node, whose affine criterion states exactly what is needed.

## Review by Q147

I read Milne 23h, printed pp.508-511, and Appendix C.21-C.22, C.35-C.38, printed pp.612,615-616. I also read Stacks morphisms.tex, lemma-closed-immersion (01QO), particularly the quotient-algebra condition (2), rather than relying on a tag alone. Milne provides the exponential construction and bracket normalization but omits the details of the claimed group theorem; I marked the overall proof agent-written and explicitly requested the missing commutator source for the new statement. No SGA source is used.

For step 1 I opened lem-sfb-root-base-rational-integral-spans and lem-sfb-root-base-reflection-induction. The former really supplies the simple-coroot basis and equality of the integer coroot spans, including the coroot sign condition needed for a dual base. The latter really states induction under negation and simple reflection. The primitive-coroot predicate holds at a simple coroot, and integral involutions preserve it; these are the actual three hypotheses, not an invocation of Weyl transitivity without an input. The identification of P with the integer dual follows from the equality of spans. The zero-rank case is handled separately in step 10.

For step 2 I opened lem-sfb-chevalley-admissible-representation: its statement supplies [e_alpha,e_-alpha] = h_alpha, the weight eigenvalues, the direct-sum lattice and Z Omega = P, and the integral first divided powers. If E_alpha is zero modulo p, the commutator forces every weight value of the coroot divisible by p. Weight generation then contradicts a value 1 on P from step 1. This is why the proof works also in characteristics 2 and 3. In characteristic zero the faithful representation supplies nonvanishing. Nothing from the proof or reductivity conclusion of a group-realization node is used.

Step 3 uses the same actual representation conditions, deriving all weight shifts from the bracket equation before base change. Rational weight labels, rather than their possibly equal positive-characteristic differentials, control the matrix blocks. Positive q-values give the required upper and lower orientations for decreasing q order; a nonzero shift cannot give a diagonal block. Step 4 is a coefficientwise binomial calculation in integral matrices, so inverses exist over every test algebra.

Steps 5 and 6 expand the finite polynomial product. A monomial with total shift beta and more than one factor has only roots of smaller height. Thus its entry is a nonzero field coefficient times b_beta plus a polynomial in previous heights. I wrote the recursive recovery polynomial explicitly, including the height-one base and the induction step. Only that nonzero element of F is inverted. Surjectivity of the ambient affine coordinate map follows because each b_beta is in its image. The existing def-weil-closed-immersion statement includes exactly the quotient-algebra affine criterion; no uncited geometric-points-to-schemes inference occurs. The negative sign uses the same positive heights of the indexing beta and the operators E_-beta.

Step 7 uses precisely the displayed formula in the new commutator statement. The representation need not be faithful for that identity; our input has the required integral divided powers and nilpotence. Two distinct roots of the same sign cannot be opposite, and every generated i alpha + j beta has larger height. Step 8 gives the full collection induction: its prefix/tail invariant, empty initial prefix, finite movement of the height-h factors, the fact that no such factors are newly created, and termination at maximal root height. Equal-root addition is already proved in step 4. This yields polynomial multiplication and inverse parameters, including over nonreduced rings.

For step 9 I read def-sc-group-scheme-subgroup: it explicitly defines a closed subgroup by the subgroup condition on every test algebra. Step 6 identifies the closed image scheme with affine space, so all its algebra-valued points really have the displayed parameters. Step 8 gives the subgroup condition; the ambient group identities restrict through the injective matrix realization. Step 10 checks N = 0 and both identity images directly, including the closed equations for the identity in GL.

I tested the new statement with commuting roots (empty higher cone), in type A2 with E12,E23 where the commutator is I+uv E13, with u=0 or v=0, and modulo 2 and 3; the identity specializes without dividing by these primes. The item in type A1 has p_+(b) = I+b E12 in the standard full-weight lattice, so coordinate recovery is b = M12, and the product is addition; the negative root gives the lower matrix. In type A2, an E13 entry may contain a b_alpha b_beta term depending on product order, exactly the lower-height polynomial Q in step 5. R empty is handled explicitly. No statement correction was necessary. None of the proof steps exceeds 2000 characters. The only newly isolated fact is a strictly smaller two-root identity, not a restated clause of the item. All new-node fields are statement-only, search records come from searches.jsonl, and no new Mathlib leaf is claimed.

## Unfinished work

No stage-1 part of the assigned split is left unfinished. The new commutator node is intentionally unsplit and joins the queue. It needs its own future literature-based split; this delivery does not claim that its proof has been completed.
