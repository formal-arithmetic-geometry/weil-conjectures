# Stage-1 delivery: lem-sfb-additive-jordan-linear-compatibility

1. Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-additive-jordan-linear-compatibility.json`: item, now split in seven explicit steps; statement and statement dependencies retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-jordan-chevalley-decomposition.json`: statement, Mathlib leaf for polynomial existence and commuting-pair uniqueness, using invariant-complement semisimplicity.
- `dag/nodes/sec-six-functors-basics/lem-sfb-geometric-semisimplicity-field-extension.json`: statement only, unsplit; comparison of invariant complements, separable minimal polynomial and geometric diagonalizability, with preservation and reflection under arbitrary field extension. Searches find partial results, not the full comparison.
- `citations.json`: one verbatim statement quote for every cited node in every step.
- `searches.jsonl`: actual msearch.py records. Preexisting searches in the item were retained; fresh searches are appended where appropriate.

2. Attachments

None. Searches for the item's blueprint tag, Jordan-Chevalley declaration names and the mathematical notions in `lean/WeilConjectures/` found no project declaration stating the item. The strict-Weil-complex Jordan-block results concern a different subject. Mathlib declarations are used as a new Mathlib leaf, not claimed as project attachments.

3. WANTED

None. Milne's Algebraic Groups PDF is present. The comparison prerequisite is explicitly worker-supplied supporting linear algebra, not an assertion that Milne proves the invariant-complement formulation verbatim.

4. Problems and changes

The imported item had no proof. Its statement is correct and has not been changed. The important terminology issue is that Mathlib's `Module.End.IsSemisimple` means invariant complements, whereas Milne and the item mean geometric diagonalizability. A direct Mathlib-leaf claim for the entire item would overlook both that comparison and all three compatibility clauses. The new comparison node makes this obligation visible. The inherited item search commentary says uniqueness is at line 85; the pinned declaration actually starts at line 84, and the new leaf records the read lines 84-92.

I read the latest blueprint's `sk-thm-sf-ctf-stability` unit, direct-images proof (3), and `det-d-linear`. They do not themselves state the Jordan lemma. This item's inherited prerequisite chain passes through `lem-sfb-algebraic-lie-additive-jordan`; its source place is Milne p.376. `tools/blueprint_refs.py ancestor` returns `None` for this existing long chain, so the inherited null ancestor and full via chain are retained. Each new node prepends this item to that via chain and names the specific local argument it supports. Blueprint searches for Jordan, Jordan-Chevalley, diagonalizable, semisimple, nilpotent and invariant complement found no blueprint statement of either new prerequisite.

The item's proof origin is `agent`: the book explicitly supplies the additive existence/uniqueness discussion on p.376 and the multiplicative analogues on pp.168-169, but the tensor-sum calculation, scalar-extension verification and interface to Mathlib are expanded here by the worker.

5. Unfinished work

The geometric comparison node is deliberately left statement-only for its own stage-1 split. Its natural proof uses the squarefree minimal-polynomial criterion in Mathlib, perfectness to pass to separability, and the primary-space/eigenvector criterion for diagonalizability. Minimal polynomials are unchanged under a field extension: in a finite basis their annihilation equations are linear equations over the base field, and scalar extension preserves their ranks. Separability is preserved and reflected under extension using the Bezout criterion for the polynomial and its derivative. These observations prove the stated arbitrary-extension equivalence and explain why no perfection of the extension field is required there. This outline is in the report only; no proof is hidden in the new node's statement.

## Not duplicates

lem-sfb-polynomial-jordan-chevalley-decomposition vs lem-sfb-multiplicative-jordan-linear-compatibility: the existing node concerns invertible maps and multiplicative diagonalizable/unipotent factors over an algebraically closed field; the new Mathlib leaf concerns arbitrary maps, additive nilpotent/complement-semisimple parts over a perfect field, and polynomial membership.

lem-sfb-polynomial-jordan-chevalley-decomposition vs lem-sfb-additive-jordan-linear-compatibility: this is the actual Mathlib existence/uniqueness input in invariant-complement language; it asserts none of the intertwiner, tensor-sum or scalar-extension conclusions, which the item's steps prove. It is delivered as a verified Mathlib leaf, not an unsplit restatement of the item.

lem-sfb-geometric-semisimplicity-field-extension vs lem-sfb-squarefree-annihilator-invariant-complements: the existing leaf proves that a specified squarefree annihilating polynomial gives invariant complements. It does not prove the converse, identify this with geometric diagonalizability, or state its behavior under arbitrary field extension.

lem-sfb-geometric-semisimplicity-field-extension vs lem-sfb-invariant-complements-eigenspace-span: the existing leaf works over an algebraically closed field and concludes that eigenvectors span there. It does not compare the two notions over a perfect nonclosed base or handle arbitrary extension fields.

lem-sfb-geometric-semisimplicity-field-extension vs lem-sfb-generalized-eigenspace-direct-sum: the existing leaf gives the primary decomposition of any endomorphism over an algebraically closed field, not a comparison or scalar-extension criterion for semisimplicity.

## Review by NB

I checked B-E against the statements and sources, with particular attention to the two different meanings of semisimplicity. I read Milne Section 9(b), printed pp.166-170 (PDF pages 178-182), and the preliminaries and Proposition 17.74 on printed pp.376-377 (PDF pages 388-389). Page 166 defines semisimplicity geometrically and discusses its minimal-polynomial criterion. Page 376 states additive Jordan decomposition and points to the proof of 9.11. Propositions 9.13 and 9.15 on p.169 are the primary-space and tensor arguments being adapted; I have not cited them as if they already stated the additive tensor-sum law.

For the polynomial leaf I read the complete signatures and proofs of `Module.End.exists_isNilpotent_isSemisimple` at Mathlib/LinearAlgebra/JordanChevalley.lean:76-80 and `Module.End.isNilpotent_isSemisimple_unique` at lines 84-92, and `Module.End.isSemisimple_iff` at Semisimple.lean:74-76. The former gives polynomial membership of both parts and existence; the latter gives uniqueness under exactly the commuting, nilpotent and semisimple hypotheses. The leaf deliberately uses complement-semisimplicity, so no geometric identification is being smuggled into its Mathlib match. The zero-dimensional convention for nilpotence is compatible with Mathlib's exponent-zero option.

For the geometric comparison node I read the same p.166 source, Mathlib's invariant-complement characterization, its squarefree-annihilator theorem at Semisimple.lean:218-232 and its squarefree-minpoly theorem at line 243. The semantic searches in two different phrasings and the name/source searches returned these as partial inputs. None states the full geometric/extension comparison, so it is unsplit and has no Mathlib match. Its meaning is fully spelled out, including the polynomial 1 for the zero space, distinct roots, complements, the extension map and the absence of perfection assumptions on L.

Step 1 is an elementary pair of inverse coordinate formulas. The coefficient maps explicitly establish finite dimension and injectivity of scalar extension on Hom, so later descent of equalities is justified. It also checks zero spaces. It invokes no uncited extension theorem.

Step 2 cites the polynomial leaf for its existence, polynomial membership and uniqueness clauses, and the geometric comparison for the equivalence of complement and geometric semisimplicity over a perfect base. Both cited statements explicitly contain these assertions. Commutation of the two polynomial parts is proved by expanding powers. For uniqueness the competing parts need not lie in k[A], as the cited uniqueness clause also does not assume that.

Step 3 cites the geometric comparison for preservation after K/k and equivalence with complement semisimplicity over K, and the polynomial leaf for uniqueness over K. Here K is explicitly perfect, the extended space is finite dimensional by step 1, powers of the extended nilpotent map vanish, and commutation and the sum identity are checked on pure tensors. The algebraic closure used later is perfect. This proves scalar extension before the later arguments use it.

For step 4 I opened `lem-sfb-generalized-eigenspace-direct-sum` and read its full statement: it defines the primary spaces by powers, says that every vector has a unique finite primary expansion, and includes the dimension-zero case. The elementary argument in step 4 uses exactly those assertions. Commutation with N keeps each S-eigenspace stable, so an S-eigenvector of value a lies in the A-primary space of value a. Uniqueness of primary expansion then identifies S on the entire primary space; no simultaneous-diagonalization theorem is asserted without proof.

Step 5 cites the same primary-decomposition statement for spanning and uses step 4 for the scalar action of the semisimple parts. I checked the powers of B-a and A-a explicitly intertwine, and that this requires neither f to be invertible nor A or B to be invertible. The subtraction for the nilpotent parts and the matrix-entry descent are included, rather than hidden behind a compatibility assertion.

Step 6 is elementary algebra in the endomorphism ring: tensor operators on different factors commute by their values on pure tensors, and same-factor commutation follows from the already constructed parts. The word expansion with exponent r+t has no factorial denominator, so it works in positive characteristic, including when eigenvalue sums coincide. Both r and t are chosen positive.

Step 7 cites the geometric comparison for the diagonalizability of the extended semisimple parts, the existing Mathlib leaf `lem-sfb-finite-tensor-product-basis-coordinates` for its explicitly stated basis of pure basis tensors (two factors), and the polynomial leaf for uniqueness after converting the semisimplicity terminology. I opened all three statements and checked each conclusion taken from them. The reassociation across scalar extension is given with both maps, not simply called a transport. Its eigenvalue computation uses addition, as required by this additive item. Repeated sums a_i+b_j do not require distinctness for an eigenbasis. There is no unproved assertion that an arbitrary tensor functor preserves semisimplicity.

I tested the statements and argument on V=0, W=0, zero endomorphisms, a single Jordan block, a scalar operator, noninjective intertwiners, and characteristic-p tensor sums of two nilpotent blocks. The exponent bound remains valid in all cases. An imperfect base is excluded where invariant-complement and geometric semisimplicity can differ; the new comparison still correctly allows an imperfect extension of a perfect base. Neither new node is a duplicate of the group-representation semisimplicity definitions. No cyclic use of the Lie-algebra parent is introduced. All new nodes have empty proofs; none contains a proof sketch in its statement. Every item's proof citation has a verbatim quote in citations.json. No non-elementary step exceeds 2000 characters. The server review_split and check_dag probes passed; final packaging is checked by the required deliver.py dry run. No Lean was written and no compiler or Lake was invoked.

The first packaging dry run flagged the contextual phrase “the item’s statement” in step 2 under B2. I replaced it with the full competing-pair hypotheses A=S\prime+N\prime, commutation, geometric semisimplicity and nilpotence; the mathematical argument is unchanged.
