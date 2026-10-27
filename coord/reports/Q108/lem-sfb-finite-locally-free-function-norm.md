# Stage-1 report: lem-sfb-finite-locally-free-function-norm

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-function-norm.json: item, statement, split; Mathlib has algebraic ingredients but no single declaration or one-line specialization giving every scheme-level clause.
- citations.json: one entry for every cited node in every numbered proof step, quoting its statement verbatim.
- report.md: this report.

No new nodes; no new Mathlib leaves. The item statement and all maintainer-owned fields remain unchanged. The six proof steps have lengths 812, 788, 919, 515, 753 and 1071 characters, below the long-step threshold.

## Attachments

No attachment for the item. The exact blueprint tag search and concept searches in lean/WeilConjectures/ found no declaration stating all its clauses. AlgebraicGeometry.exists_finiteLocallyFree_norm_charts, FiniteLocallyFreeNormCharts.lean:186, already belongs to lem-pd-finite-locally-free-norm-charts and proves existence of a section with pointwise selected free charts only. It does not state multiplicativity, the scalar-power formula, or vanishing. Algebra.norm_notMem_iff, WeilConjectures/Mathlib/RingTheory/Localization/NormTrace.lean:46, already belongs to lem-pd-finite-free-norm-prime-criterion. I read both source proofs; neither warrants attaching this whole item. No Lean was written or compiled.

## WANTED

None. All proof sources used are present: literature/stacks-project/divisors.tex, 0BD2 (divisors-lemma-finite-locally-free-has-norm) and 0BCX (divisors-section-norms); exercises.tex, 02DU/02DV (exercises-exercise-trace-det and exercises-exercise-trace-det-rings). I also read morphisms.tex, morphisms-definition-finite-locally-free and morphisms-lemma-finite-flat, to check the finite/flat/locally-finitely-presented convention against the locally-free pushforward convention.

## Audit and corrections

The live item was unsplit with an empty proof; the sandbox had no earlier item, report or searches. No statement dispute was found. The positive degree and all hypotheses match Stacks 0BD2, and the item deliberately omits that source's extra arbitrary-base-change conclusion.

The inherited blueprint.from.node is null: blueprint_refs.py ancestor reports None because the historical created.item chain is broken. This is existing metadata, not a new node, and the field is maintainer-owned. I preserved it and its detailed from.place and via list, searched the whole imported blueprint by norm, finite locally free, determinant of multiplication, 0BD2, function norm and determinant norm, and retained same_as=[]. I read the latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and det-thm-sf-ctf-stability-direct-images proof (3). This remains the generic norm prerequisite in the previously chosen alteration/ampleness branch; it does not replace a unit proof step. Historical source paths in reused nodes were read as references, not substituted for the current blueprint.

Mathlib searches were all made through the prescribed msearch.py command. The six logged searches include leanfinder twice with distinct phrasings, loogle, leansearch, and two grep queries. I read the returned hits and the pinned Mathlib Norm/Defs.lean:61-90, including Algebra.norm, norm_apply, norm_eq_matrix_det and norm_algebraMap_of_basis. These require or express global free algebra determinants; they do not provide a map on arbitrary scheme opens. Algebra.norm_eq_zero_iff' needs domains, absent here, so it is not used. Normalization hits are unrelated. All newly appended search records are the actual log records, with their unchanged tool and query text. The item's inherited Q91 searches are preserved.

## Not duplicates

No new-node pairs: the split creates no nodes. Existing lem-pd-finite-locally-free-norm-charts was considered and is only an existence statement on selected charts. Instead of introducing a second affine restriction lemma, I reused lem-a1-principal-free-algebra-determinant-norm, whose final statement explicitly treats every free affine subopen. The rank theorem is lem-pc-flf-properties, matrix multiplicativity is lem-sfb-matrix-cramer-determinant-identities, and vanishing uses lem-pd-finite-free-norm-prime-criterion. The latter two relevant algebraic statements from other units are declared as generic tool uses in split_report; the matrix identity is already a Mathlib leaf, and lem-pc-flf-properties is Lean-closed.

## Review by Q108

I checked delivery-errors B through E against the actual item, every cited statement, and the sources above. There is no statement-only child containing a disguised proof, no new definition, no unsearched node, and no clause repackaged as a new lemma. The item's determinant formula is explicit, and JSON uses ordinary single TeX backslashes after decoding.

Step 1 uses the exact rank-d pushforward assertion in lem-pc-flf-properties, not merely the definition of a finite locally free morphism. def-amb-finite-locally-free-module explicitly supplies a trivializing open cover and quasi-coherence. Its restriction trivializations give rank-d section bases on smaller affine opens. def-pc-scheme provides local affine neighbourhoods; def-weil-finite-integral-morphism explicitly says finite morphisms are affine. The sheaf, open and affine notions used here are already defined, and no extra Noetherian hypothesis enters.

Step 2 applies lem-a1-principal-free-algebra-determinant-norm to a globally free chart, with the one-element principal cover generated by 1. I read its full statement: it asserts the determinant after scalar extension, independence of bases, and, under quasi-coherence, the determinant formula on every free affine subopen. The last clause is exactly what the compatibility argument needs; I am not taking a hidden fact from its proof. The quasi-coherence hypothesis comes from the locally free module definition cited in this step. def-weil-endomorphism-determinant explicitly asserts basis independence. This existing affine algebra result is strictly smaller than the scheme norm item and supplies neither the global family nor its multiplication, scalar or vanishing clauses.

Step 3 compares local sections on an affine cover of each overlap, uses the basis independence just cited, and then applies the structure sheaf's equality and gluing axioms. I explicitly avoid assuming intersections of affine opens are affine or quasi-compact. The independence of the cover and the formula on any extra free affine chart follow by adding that chart and repeating this same two-chart comparison; no uniqueness theorem is assumed without proof. This step is elementary after steps 1-2: it is precisely application of the sheaf axiom to the supplied compatible family.

Step 4 writes the restriction identity on a covering family of free affine charts and then uses equality of sections. It works for arbitrary opens and for the empty open, and does not presuppose the restriction conclusion.

Step 5 uses exactly det(AB)=det(A)det(B) from lem-sfb-matrix-cramer-determinant-identities; its hypothesis n>=1 is satisfied by n=d. The identifications m_bc=m_b composed with m_c and m_(f-sharp a)=a times the identity are immediate multiplication calculations. I explicitly compute the scalar and identity determinants from def-weil-pbc-matrix-determinant's permutation formula, so those formulas do not hide a new lemma. Equality on the covering charts proves the global equalities. This is elementary using the cited matrix identity and definition.

Step 6 uses the exact finite-free norm/primes equivalence stated by lem-pd-finite-free-norm-prime-criterion, with the coordinate algebras supplied by finiteness. def-weil-affine-spectrum supplies the prime-spectrum interpretation of the affine morphism, and def-weil-residue-field supplies the stalk quotient and induced field map. I wrote the kernel calculation at a prime explicitly, so vanishing in the residue field is not silently identified with zero in the whole ring. Contraposing the norm/primes equivalence with the specified prime above the image gives the required vanishing. This is also the residue-field argument in 0BD2 and exercise 02DV(2); no domain criterion or field-only norm formula is substituted.

I tested the statement and argument with V empty, X empty, d=1 (the identity norm locally), a split product algebra R^d (product norm), and the nonreduced algebra k[epsilon]/(epsilon^2), where multiplication by epsilon has zero determinant. A nilpotent or inseparable fibre causes no problem. The zero ring has an empty spectrum and all section identities hold in its singleton ring; no pointwise argument is applied there. Degree zero is outside the item, and the positive-rank hypothesis needed for the cited matrix identity is checked. Arbitrary overlap topology causes no hidden separatedness assumption.

All citations quote complete verbatim statements for mechanical comparison. I checked the dependency closures of the reused affine norm and prime criterion and found no path back to the item. No step exceeds 2000 characters or hides a separate comparison lemma. The algebraic auxiliary results are existing DAG nodes, and each proof step uses their statements rather than their internal proofs.

## Unfinished work

None in the stage-1 split. Validation and direct push follow this signed report; the maintainer performs the independent mathematical review.
