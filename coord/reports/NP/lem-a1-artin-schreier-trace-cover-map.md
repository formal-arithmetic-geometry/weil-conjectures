# Stage-1 report: lem-a1-artin-schreier-trace-cover-map

1. Files written

- dag/nodes/sec-deligne-laumon-a1/lem-a1-artin-schreier-trace-cover-map.json: statement, split; all five original clauses retained verbatim. Nine steps prove them on polynomial algebras and geometric fibres.
- dag/nodes/sec-deligne-laumon-a1/lem-a1-finite-field-trace-frobenius-sum.json: statement, Mathlib leaf. Exact match FiniteField.algebraMap_trace_eq_sum_pow, Mathlib/FieldTheory/Finite/Trace.lean:49–56. This is the sole new node.
- citations.json: one verbatim statement quote for each cited node in each step.
- searches.jsonl: actual msearch results; inherited item searches remain in the item. No search was invented or recorded as unavailable when it succeeded.

2. Attachments

None. Searching WeilConjectures/ by the exact blueprint tag found no declaration for this item. Concept searches found FourierTransform/ArtinSchreier.lean's q-cover and character-sheaf interfaces, but no trace-polynomial comparison giving all five clauses. Those interfaces are not an attachment to this statement. No master sorry declaration is counted as a proof.

3. WANTED

None. The necessary texts and pinned Mathlib declaration are available locally.

4. Faults and changes

The item had no proof. Its statement is correct, including the subgroup order and arbitrary base change; it is unchanged. Statement dependencies now explicitly include finite/étale morphisms and the relative-spectrum construction. Laumon (1.1.3) supplies the Lang torsor and pushout context, not this explicit trace-polynomial calculation. The proof is consequently marked agent-written. No SGA source was read or cited as a dependency.

A tempting proof using Tr(1) != 0 is wrong when p divides r. Step 7 instead invokes the existing trace-pairing nondegeneracy leaf with the nonzero multiplier b. Empty affine charts are omitted before using polynomial degree; no nonemptiness hypothesis is added to X. The geometric-fibre point count uses the existing polynomial root/factorization statement: a prime containing the product of distinct linear factors contains a factor. It does not silently appeal to an unstated theorem on residue fields.

5. Unfinished work

None for this split. The new trace node is already a Mathlib leaf; the existing cited tools retain their own recorded states. No unit record was edited because this item is a supporting comparison, not the statement of the unit.

## Not duplicates

lem-a1-finite-field-trace-frobenius-sum vs lem-a1-trace-pairing-nondegenerate: the new leaf computes the value of trace for an arbitrary finite-field extension; the existing leaf asserts nondegeneracy of the prime-field trace pairing and contains no sum formula.

lem-a1-finite-field-trace-frobenius-sum vs lem-weil-finite-field-pow-card: the existing leaf gives x^Q=x and its iterates, not the trace value. It was reused in steps 3, 5 and 7 rather than recreated.

lem-a1-finite-field-trace-frobenius-sum vs lem-a1-artin-schreier-trace-cover-map: the new leaf has no schemes, covers, translations or base change and is the general field trace formula, not a restatement of a cover-map clause.

There were no existing node sources with Stacks Tag 0BIH when searched. The new leaf's direct source is the pinned Mathlib declaration; its source place also names 0BIH (fields.tex, lemma-trace-and-norm-from-minimal-polynomial) to identify the ordinary field-trace convention. That tag is not claimed to print the finite-field sum formula itself.

## Searches and blueprint route

Before creating the trace leaf I searched the entire DAG for algebraMap_trace_eq_sum_pow, trace_eq_sum_automorphisms, trace polynomial, Frobenius, and finite-field trace/sum terminology, distinguishing occurrences in search-result metadata from actual statements. blueprint_refs.py ancestor returns lem-a1-unramified-nonexceptional. Whole-blueprint searches included trace, Frobenius, finite field trace, trace polynomial, Frobenius sum, trace-frobenius, and Frobenius powers; no blueprint statement states this trace formula or the full item. The new node therefore has same_as=[] and via=[lem-a1-artin-schreier-trace-cover-map, lem-a1-artin-schreier-prime-character-comparison]. Its source is the case a != 0 of that ancestor, where the q-character must be compared to the prime-degree character before applying local ramification.

The actual msearch calls for the new leaf were LeanFinder "The finite field trace is the sum of the iterates of Frobenius", Loogle "FiniteField.algebraMap_trace_eq_sum_pow", grep "algebraMap_trace_eq_sum_pow", and LeanSearch "For a finite extension of finite fields the trace is the sum of the powers of Frobenius". All succeeded and returned the displayed declaration. I read the hypotheses and proof at lines 46–56: finite L, fields K and L, and an algebra structure are exactly enough; no separability or Galois assumption needs to be added. The other msearch queries were for the full item or to locate the already-existing power identity; their partial field-theory hits do not establish the five cover clauses. Full commands and actual result digests are in searches.jsonl.

## Review by NP

I read the chapter record sec-deligne-laumon-a1, the unit sk-p-dl-a1-middle and the current main-20261015 proof of lem-a1-unramified-nonexceptional, especially case a != 0. This is supporting algebra for the prime-character comparison already used by that case, so it changes neither the unit's ramification argument nor any chapter route. I read Laumon pp. 139–140, (1.1.3), for the Lang torsor, character pushout and pullback along a function. The explicit sum and the coordinate calculations are my argument, not a claimed quotation from Laumon. For the new leaf I read the complete Mathlib statement and proof at Trace.lean:49–56 and the Stacks trace-from-minimal-polynomial convention at fields.tex, lemma-trace-and-norm-from-minimal-polynomial (0BIH). The source agrees with its finite-field-extension hypotheses and trace value; the leaf is general enough to specialize to F_q/F_p.

Step 1 uses the statements of lem-weil-pbc-affine-morphism-relative-spec (parts 2 and 4, affine charts and restriction), lem-weil-pbc-monic-quotient-free (the power basis and finiteness), and lem-weil-pbc-standard-etale-monic-derivative (étaleness after localizing the monic polynomial at its derivative). I opened all three. The last theorem does not itself assert finiteness, which is why the monic-quotient node is separately cited. I checked q and p are positive and the derivative is the unit -1 in characteristic p. The finite and étale definition nodes give exactly the affine-local meanings used, and pqf-def-coherent gives the local associated-module meaning verifying the quasi-coherent hypothesis of relative Spec. I read algebra.tex, definition-standard-etale and lemma-standard-etale (00UB/00UC), and constructions.tex, lemma-spec-properties (01LX).

Step 2 uses the full statement of lem-weil-pbc-relative-spec-base-change: pullback is of the algebra sheaf, not merely inverse image. Its canonical algebra comparison and isomorphism give the relative spectra of those pullbacks. The polynomial-quotient identification is written with both inverse maps on generators, so no flatness or tensor-injectivity claim is used. I checked the relative-Spec node's anti-equivalence and restriction clauses identify these formulas globally. The geometric-point specialization is allowed since the base-change theorem has no finite-type restriction on S'.

Step 3 uses the ring-Frobenius definition's binomial identity and naturality, the finite-field power leaf, and the relative-Spec statement on morphisms. The substitutions preserve the relation and have the explicitly written inverse. This establishes the named translations rather than confusing them with the full automorphism group. All elementary assertions here are substitutions, composition and inverse formulas.

Step 4 uses def-pc-separable-polynomial literally as the Bézout condition, with coefficients 0 and -1. I read lem-pc-separable-polynomial-distinct-roots-alg-closed: it gives both the number of roots and the product factorization, not just existence of one root. It applies with F=Omega and the identity extension, so no new finite-field-extension hypothesis is required. That factorization and primality give the fibre's points. The q distinct translates found in step 3 exhaust exactly q roots and give freeness and transitivity. The same argument with p proves the prime-fibre fact needed later.

Step 5 uses the Frobenius and finite-field power statements for the telescoping calculation and b^q=b. The original identity is proved in the polynomial algebra before reduction. The relative-Spec anti-equivalence's actual statement includes the map on affine charts and therefore gives precisely the desired morphism in the correct contravariant direction. This step's calculation is elementary from those cited identities; it creates no new lemma.

Step 6 uses the new trace formula with K=F_p and L=k_0, together with Frobenius additivity and the relative-Spec anti-equivalence. The finite-field degree r is justified by counting coordinates of a basis: p^n=p^r. The two compositions are compared on coefficients and t, so the equivariance equality has the stated sign and order, including characteristic 2. The algebraic trace formula is only a small ingredient here, not the cover-map assertion moved into a new node.

Step 7 uses the existing trace-pairing nondegeneracy statement with its first entry a=b, which is nonzero by hypothesis. I checked the node gives an element with Tr(bc_0) != 0, exactly what is needed. Frobenius and the power identity for F_p give the scalar-linearity calculation. The preimage of d is explicitly (d/e)c_0, and the inverse bijections with the kernel justify the cardinal q/p by partition into p equal fibres. This does not infer surjectivity from Tr(1).

Step 8 uses only already-proved steps 4–7: it explicitly writes every source point as alpha+c and every target point as beta+d and checks the image and the difference criterion. It does not invoke a separate unproved torsor-quotient theorem. The subgroup in the statement is exactly ker T_b, and the computed orbit has q/p points.

Step 9 reopens the same two relative-spectrum statements used in step 2. The base-changed algebra morphisms are checked on coefficients and their single generator; the displayed image of the trace polynomial fixes b because h is over k_0. These equalities glue and the faithful anti-equivalence gives equality of scheme maps, not just equality on geometric points. This checks all three named maps and not only the cover objects.

I tested r=1, where Theta_b=by, trace is the identity and the kernel has order 1, so the map is an isomorphism on each fibre. For p=2 and r=2, b=1, Tr(1)=0 but the trace map is still onto; the nondegeneracy argument handles this case. For f=0, both covers split and the map on the root labels is c -> Tr(bc), with fibres cosets of the same kernel; disconnected covers present no problem. Empty X and empty base changes have empty schemes and no geometric fibres. Nonreduced affine algebras cause no problem because the polynomial identity is in the ring itself and the derivative remains -1. No step assumes an integral, connected or smooth base, b in F_p, or a flat base change.

Finally I checked B–E against the delivered files: the new node contains only a self-contained statement, no proof sketch; all searches are actual logged queries; no new node is an elementary substitution, a duplicate, or a cover-map clause; all non-elementary imported tools are cited as statements and are below no cycle through this item. Every citation has a literal quote in citations.json. The only off-unit non-Mathlib tools are the generic relative-Spec construction and its base-change theorem, declared with reasons in split_report.tool_uses. Every step is below 2000 characters. The repairs made during self-review were to handle empty affine charts explicitly, add the quasi-coherence check, and use the root factorization to count scheme points without an uncited residue-field identification.
