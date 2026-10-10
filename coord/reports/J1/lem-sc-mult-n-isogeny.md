# Delivery report

1. Files written:
   - `dag/nodes/sec-abelian-varieties/lem-sc-mult-n-isogeny.json` — statement, split into two proof steps; no Mathlib match.
   - `dag/nodes/sec-abelian-varieties/lem-sc-finite-surjective-dimension.json` — statement-only support node; no Mathlib match.
   - `dag/nodes/sec-abelian-varieties/lem-sc-closed-full-dimension-eq.json` — statement-only support node; no Mathlib match.
   - `citations.json` — verbatim citations for every proof-step dependency.
2. Attachments: none.
3. WANTED: none.
4. The imported item was not attachable because `AlgebraicGeometry.surjective_npow_id` is not sorry-free transitively. Its first proof paragraph is supplied by the existing finite-kernel node. The second paragraph previously used dimension preservation and the full-dimension closed-subscheme argument without DAG statements; I added two strictly weaker statement-only nodes and cited them. The factorization through the scheme-theoretic image is finite because a finite morphism factoring through a closed immersion remains finite; the image node supplies surjectivity and closed subgroup structure.
5. Nothing remains unfinished.

## Review by J1

I read the item source and the corresponding Lean block in `WeilConjectures/AlgebraicGeometry/AbelianVariety/Isogeny.lean` (the `surjective_npow_id` declaration, lines 179–210). The finite-kernel step uses exactly the statement of `lem-sc-mult-n-finite-kernel`, including finiteness of `[n]` and of `A[n]`. The image step uses `lem-sc-image-subgroup` for the scheme-theoretic image, its induced surjection, and closed subgroup structure, and `lem-sc-mult-n-homomorphism` for the homomorphism hypothesis. I read both cited node statements rather than relying on their proof text.

For the two new nodes I checked the imported blueprint proof sentence they make precise and searched the whole DAG and blueprint for duplicates. `lem-sc-finite-surjective-dimension` states the finite-surjective dimension equality used in step 2; `lem-sc-closed-full-dimension-eq` states the final closed-subscheme equality used in that step. Both are statement-only because their proofs are deferred as independent DAG work. I ran LeanFinder, Loogle, and Mathlib grep searches for the item and for each new node; none gave an exact theorem. The small cases are consistent: a finite surjection of zero-dimensional finite schemes preserves dimension, and a proper closed subscheme of an irreducible finite-dimensional scheme has strictly smaller dimension, so the second node has the expected edge behavior. I also checked that the item’s hypotheses provide properness, separated finite type, reducedness, irreducibility, and nonempty finite type as required by the cited statements.

## Not duplicates

lem-sc-finite-surjective-dimension vs lem-sc-mult-n-isogeny: the new node is a general dimension-preservation statement for arbitrary finite surjective morphisms, while the item concerns multiplication on an abelian variety and concludes surjectivity plus finite kernel.
lem-sc-finite-surjective-dimension vs lem-sc-divisible-group-structure: the new node concerns Krull dimensions of finite surjections and has no group-scheme or divisibility conclusion.
lem-sc-finite-surjective-dimension vs lem-sc-mult-n-finite-flat: the existing node concerns finiteness and flatness of multiplication by n; the new node concerns dimension equality for any finite surjection.
lem-sc-finite-surjective-dimension vs lem-sc-isogeny-surjective: the existing node concerns point-surjectivity over an algebraically closed field; the new node concerns scheme dimensions over any field.
lem-sc-finite-surjective-dimension vs lem-sc-mult-n-finite-kernel: the existing node specializes to finiteness of multiplication and its kernel; the new node states a dimension theorem for arbitrary finite surjections.
lem-sc-finite-surjective-dimension vs lem-sc-isogeny-facts: the existing node gives degree, flatness, and surjectivity of multiplication over an algebraically closed field; the new node gives only dimension equality for finite surjections.
lem-sc-closed-full-dimension-eq vs lem-sc-mult-n-isogeny: the new node is a general closed-subscheme dimension criterion, while the item concerns multiplication on an abelian variety and concludes surjectivity plus finite kernel.
lem-sc-closed-full-dimension-eq vs lem-sc-divisible-group-structure: the new node has no divisibility or group-scheme conclusion.
lem-sc-closed-full-dimension-eq vs lem-sc-mult-n-finite-flat: the existing node concerns finiteness and flatness of multiplication; the new node concerns equality of a closed subscheme with its irreducible reduced ambient scheme.
lem-sc-closed-full-dimension-eq vs lem-sc-isogeny-surjective: the existing node concerns surjectivity on rational points; the new node concerns closed subschemes and Krull dimension.
lem-sc-closed-full-dimension-eq vs lem-sc-mult-n-finite-kernel: the existing node concerns finiteness of multiplication and its kernel; the new node is an ambient-scheme dimension criterion.
lem-sc-closed-full-dimension-eq vs lem-sc-isogeny-facts: the existing node gives multiplication-by-n isogeny facts over algebraically closed fields; the new node is a general scheme-theoretic closed-subscheme statement.
lem-sc-finite-surjective-dimension vs lem-zl-noether-normalization-dimension: the existing node concerns a finite extension of a polynomial algebra, whereas this node concerns arbitrary finite surjective scheme morphisms.
lem-sc-finite-surjective-dimension vs lem-weil-pbc-integral-injective-dimension-equal: the existing node is an affine ring extension theorem; this node asserts the global scheme result after passing among affine charts.
lem-sc-finite-surjective-dimension vs lem-zl-noether-normalization-field: the existing node produces a finite polynomial subalgebra, while this node compares dimensions across a given finite surjective scheme morphism.
lem-sc-finite-surjective-dimension vs thm-sc-serre-duality-curve: the existing theorem concerns coherent cohomology of smooth proper curves; its citation of 00OY does not state dimension preservation under finite maps.
lem-sc-finite-surjective-dimension vs lem-sc-deg-principal-zero: the existing node gives degree zero for a principal divisor on a curve; it does not compare dimensions of schemes.
lem-sc-finite-surjective-dimension vs lem-weil-pbc-noether-normalization-field: the existing node constructs a polynomial subalgebra for one finite-type algebra; this node compares two arbitrary finite-type schemes connected by a finite surjection.
lem-sc-finite-surjective-dimension vs thm-sc-affine-torsion-cd: the existing theorem bounds torsion cohomological dimension of an affine scheme; it contains no finite-surjection dimension conclusion.
lem-sc-finite-surjective-dimension vs lem-sc-normalization-exists: the existing node gives a finite birational normalization of one integral scheme and equality of dimensions in that special case; this node allows arbitrary finite surjections.
lem-sc-finite-surjective-dimension vs lem-sc-base-change-curve: the existing node treats extension of algebraically closed base fields for a curve, not a finite surjective morphism.

## Second reading by J1

- Item statement: compared with Groupoid Schemes Proposition 39.9.11, Tag 03RP, clauses (3) and (5), and Lemma 39.9.8, Tag 0BFG; finite kernel and surjectivity for n >= 1 agree, including n = 1 and dimension zero. The empty abelian variety is excluded by its identity section; n = 0 is outside the statement.
- Step 1: checked against the complete statement of lem-sc-mult-n-finite-kernel and Tag 0BFG; it supplies both finite multiplication and finite kernel under precisely the item's hypotheses.
- Step 2: checked lem-sc-image-subgroup, lem-sc-mult-n-homomorphism, lem-sc-abelian-variety-characterization, lem-sc-finite-surjective-dimension, and the cited definitions against the hypotheses. The finite factorization is proved on affine opens; strict dimension drop follows by appending the irreducible ambient space to a maximal chain; reducedness then kills the full-support ideal. The zero-dimensional case gives H = A, and the argument applies at n = 1.
- New node lem-sc-finite-surjective-dimension: checked against Algebra Lemma 00OK (lemma-integral-sub-dim-equal) on finite affine charts and Algebra Lemma 00OY (lemma-Noether-normalization) for finite dimension, and against the existing affine node lem-weil-pbc-integral-injective-dimension-equal. It is a statement-only global scheme assertion, not a duplicate of that ring lemma or of the Noether-normalization specialization; finite surjections of nonempty zero-dimensional schemes and finite disjoint unions preserve dimension. The source, TeX, hypotheses, and definition citations were corrected. LeanFinder, Loogle, and Mathlib grep searches were run; the malformed Loogle query is marked unavailable.
- Removed new node lem-sc-closed-full-dimension-eq: checked its proposed conclusion against Topology Definition 0055 (definition-Krull) and Schemes Lemma 01J3 (lemma-reduced-closed-subscheme). It is an elementary chain and nilradical argument, now written in step 2. It had also mislabeled topological dimension as def-pc-dimension and cited an unrelated abelian-variety proposition as its source.
- Changes: added the missing irreducibility citation, distinguished scheme dimension from topological dimension, proved finite factorization and full-support equality in the step, corrected Tags 00OK and 00OY and definition references, deleted the elementary node, repaired citation quotes, and marked unusable Loogle results unavailable. The finite-dimension conclusion is included in the remaining general node, so the step uses no off-unit dimension tools.
