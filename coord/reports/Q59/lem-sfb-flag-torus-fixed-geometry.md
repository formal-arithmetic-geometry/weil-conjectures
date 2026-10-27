## Worker report

Q59 split `lem-sfb-flag-torus-fixed-geometry` at stage 1. The statement is unchanged. The proof has eight steps and uses twenty existing nodes; no new nodes and no Mathlib leaves are added. No Lean was written or compiled, and no repository files were changed.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flag-torus-fixed-geometry.json`: statement, split; no Mathlib match. Proof, actual Mathlib search records, blueprint comparison and split report completed.
- `citations.json`: one verbatim cited-statement quotation per step/dependency pair.
- `report.md`: this report.

The sandbox also contains the recorded `searches.jsonl`, a local text extraction of Milne and scratch indexing/writing scripts; these are not delivery nodes.

## Attachments

None. Read-only searches in `lean/WeilConjectures/` for the blueprint tag, torus, Borel and cocharacter found no declaration of this result. The only torus hit was a compactness comment in `ZetaLinearAlgebra/FrobeniusModule/TraceBound.lean`, unrelated to algebraic flag varieties.

## Sources and searches

Read Milne, *Algebraic Groups* (2017), Theorem 4.27 (scheme line stabilizers); Theorem 12.12 and Remark 12.13 (rational weight decomposition); Theorem 13.1 (smooth fixed schemes); Lemma 13.51 (weight separation); Section 17f, Proposition 17.53 (fixed Borels and the Weyl action); the paragraphs immediately before Proposition 21.70 (projective embedding and dominant cocharacter); and the tangent quotient computation in the proof of Theorem 21.73. The item’s original source references are retained. The argument supplies the all-test-algebras details missing from a purely pointwise reading of Lemma 13.51. Its proof origin is marked agent because these coordinate and lattice details are supplied here.

Also opened Stacks `descent.tex`, Tag 023Q, label `lemma-fpqc-universal-effective-epimorphisms`; `morphisms.tex`, Tag 01W6, label `lemma-image-proper-scheme-closed`; `etale.tex`, Tag 04XV, label `lemma-characterize-closed-immersion`; and `varieties.tex`, Tag 056S, label `lemma-smooth-regular`. These support existing cited nodes, not new ones. No SGA source is used.

Read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, as well as the recorded chapter and unit. The existing `blueprint.from` chain reaches this auxiliary flag geometry through the alteration/moduli/Haboush prerequisites; its null imported ancestor is retained rather than inventing an imported blueprint id. `blueprint_refs.py ancestor` reports None for this inherited chain. Whole-blueprint searches for flag, cocharacter, split torus, diagonalizable, 12.12, eigenspace, weight, tangent, fixed flags and 13.51 produced no duplicate of this item. In particular the invariant-flag linear-algebra node concerns one endomorphism and is unrelated.

Whole-DAG searches were by torus/Borel/cocharacter/fixed subscheme, line stabilizer, weight/eigenspace, tangent quotient and relevant literature numbers, followed by opening the actual statements. The existing G_m weight-basis result suffices: successive decomposition for the finitely many coordinate factors of a split torus gives a simultaneous character basis. A second torus decomposition node would duplicate elementary assembly of that node. Likewise the smooth-stalk formal lifting node gives tangent surjectivity in two sentences, and the torsor gives its kernel directly; no homogeneous-tangent lemma needs to be created. All twenty proposed dependencies were traversed for a path back to the item; none has one.

Mathlib searches were run only through the required msearch command and read as returned. The log records LeanSearch, LeanFinder, Loogle and grep. Two phrasings were tried for flag fixed schemes, rational torus decomposition, and homogeneous tangent quotients. Returned hits concern abstract root pairings, representations of abstract finite groups, Lie-module generalized weights, manifold tangent spaces, or ordinary projectivization. None states the group-scheme fixed-subscheme assertion. Loogle's unknown-identifier diagnostics are recorded in results, not hidden. `Representation.directSum` merely constructs an already specified direct-sum representation; it does not decompose a rational torus representation. The existing item searches from its creator are retained too. No new-node search is claimed.

WANTED: none.

## Problems corrected

The imported item had a complete and correct statement but no proof. Nothing was weakened, no hypotheses were added, and none of its clauses was moved into a new statement. The proof specifically avoids two common errors: applying an affine fixed-scheme theorem directly to projective Q, and confusing torus characters with their differentials in positive characteristic. It also enforces dominance while separating weights; generic hyperplane avoidance alone would not establish the positivity clause.

## Not duplicates

No new nodes. Existing nodes are reused throughout.

## Review by Q59

I checked the item against the Milne passages listed above with the source and cited node statements open. In particular, the roots of the tangent quotient are characters, the quotient is for right B-cosets, and the action convention is `(w chi)(t)=chi(n^-1 t n)`. The quotient at e_w removes w Phi^+, not Phi^+ itself. I did not use Bruhat cells or attracting charts: those depend on this item and would be circular.

Step 1 uses the actual statement of `lem-sfb-borel-quotient-proper-geometry`, which supplies smoothness, properness, connectedness through geometric integrality, and smoothness of the quotient map for a smooth connected subgroup. The hypotheses hold because B is a Borel. The Borel-pair node supplies the right torsor and quotient. It is not used to assert any projective embedding.

Step 2 uses the all-algebras line-stabilizer statement of `lem-sfb-chevalley-scheme-line-stabilizer`; merely a stabilizer on field points would not prove the monomorphism. The fpqc-representable-descent node explicitly gives existence and uniqueness of the descended orbit map and detection of equality. Projective separatedness and proper-over-separated are stated in their cited nodes. Tag 04XV's node explicitly turns a proper monomorphism into a closed immersion. The common-cover comparison of two lifts uses the torsor condition and the exact stabilizer equality. Thus there is no implicit orbit-immersion lemma.

Step 3 uses exactly the decomposition/basis assertion of `lem-sfb-gm-representation-weight-basis` on each coordinate factor. Commutation preserves the preceding eigenspaces, so induction on r is a finite elementary refinement. Its group-scheme version is valid on nonreduced algebras, unlike a diagonalization of only F-points. The standard-chart node supplies the affine coordinates and their cover. The Laurent-coefficient comparison is written out; it proves representability of the fixed scheme on every chart. No fixed-functor representability theorem is tacitly invoked.

Step 4 uses the stated smooth nonempty fibre of the Borel quotient and the density/existence assertion of `lem-pc-dense-separable-points` to obtain an F-rational lift. The normalizer-transitivity node says precisely that any two Borels containing T are related by an element normalizing T. The scheme-normalizer node gives N_G(B)=B. For the possible stabilizer in N_G(T), the projection B to T from the Borel-pair statement shows conjugation is trivial on T after every algebra extension, permitting application of the self-centralizer node. The rank-one-reflections statement includes finiteness of W. This proves both surjectivity and nonrepetition without presupposing a free Weyl action.

Step 5 uses the smooth-stalk node in its actual lifting form with the square-zero ideal (epsilon), not merely the definition of smoothness. It gives surjectivity on dual-number tangents. The torsor identifies the fibre and hence the tangent kernel. The tangent-definition node supplies the linear differential by composition. The rank-one statement supplies the full root decomposition and multiplicity one; the Borel-pair statement selects exactly the positive roots. The displayed conjugation formula checks the action convention and gives the claimed quotient weights. This entire step is a direct quotient calculation from these statements, not an uncited general homogeneous-space tangent theorem.

Step 6 uses `lem-sfb-torus-fixed-scheme-smooth` only on U_i, which is affine, finite type, invariant and smooth; its statement really does require affineness. The closed representing fixed subscheme was constructed in step 3. Density of separable closed points on this smooth fixed scheme, together with the finite rational-point list of step 4, gives its entire finite underlying space. The smooth-regular node applies to it without a connectedness hypothesis. A zero-dimensional regular local ring is a field by its definition, and the closed-point residue-field node identifies this field with F. This proves the finite reduced scheme assertion, rather than just its geometric point count.

Step 7 uses the converse clause of `lem-sfb-regular-cocharacter-borel-description` to get B=P(lambda_0); its Lie formula, compared with the Borel-pair root statement, forces strict positivity. The explicit polynomial perturbation is elementary integer arithmetic in the coordinate lattice. Each forbidden weight-difference polynomial is nonzero even when its leading coefficient vanishes. There are finitely many such polynomials and each has finitely many roots; their avoidance can be combined with eventual strict positivity. No separate chamber-existence or genericity lemma is hidden.

Step 8 uses the previously supplied chart equations. A nonzero integer exponent gives two distinct Laurent monomials over every coefficient algebra, including when its exponent is divisible by the characteristic. Therefore it forces a coordinate to vanish. Equal weight partitions give identical ideals on the same covering charts. Equivariance and the closed-immersion monomorphism then detect fixedness inside Q after all extensions. This is equality of fixed schemes, not only equality of fixed F-points.

Small cases checked: G a torus (Q is one point and Phi empty), the trivial group/rank-zero torus, rank-one SL_2 and both Weyl points (the two tangent weights are opposite), repeated representation weights (whole projective weight spaces remain fixed), a one-dimensional representation, and positive characteristic with an exponent divisible by p. The lattice construction imposes no unnecessary nontriviality requirement when r=0. The tangent quotient excludes weight zero in the nonempty-root case and is zero for a torus. There are no new statements requiring an independent small-case test.

All eight steps are below 2000 characters. The non-elementary black-box applications (quotient geometry and fixed-scheme smoothness) are marked non-elementary; other steps explicitly assemble cited statements or perform the stated coordinate/dual-number/lattice calculations. Every dependency of every step has a verbatim statement quotation in citations.json. No source error or statement dispute was found. Nothing remains mathematically unfinished in this one-level split; the reused unsplit dependencies retain their own separate work.
