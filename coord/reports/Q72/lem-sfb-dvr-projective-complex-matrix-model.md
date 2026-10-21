# Q72 — lem-sfb-dvr-projective-complex-matrix-model

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dvr-projective-complex-matrix-model.json`: statement node, now split into five steps; no exact Mathlib match for the whole same-support matrix-model assertion. Statement and statement dependencies are unchanged. The seven inherited Q71 searches are retained; the seven Q72 wrapper searches are appended.
- `citations.json`: one verified verbatim statement excerpt for each node cited by each step.
- `report.md`: this report.

New nodes: **0**. New Mathlib leaves: **0**. The non-elementary finite-free theorem is the existing Mathlib leaf `lem-sc-dvr-fg-torsionfree-free`.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact item id and by projective complex / finite matrix / matrix model / DVR concepts, and checked `dag/lean_names_upstream.json`. There is no tagged declaration for this item. I read `WeilConjectures/RingTheory/FiniteProjectiveComplexFreeModel.lean`, especially `CochainComplex.exists_finiteFree_model_of_finite_projective`: it gives a quasi-isomorphism from a bounded-above finite-free replacement over an arbitrary commutative ring. It does not give a degreewise isomorphism, preserve a lower support bound, or supply the finite coordinate matrices. It cannot attach to this item.

## WANTED

None. Both Stacks source files and the current blueprint source are present.

## Problems found and changes

The item had an empty proof and no proof dependencies. Its statement is correct, including the lower bound, rank-zero cases and rectangular matrices. There is no STATEMENT-DISPUTED and no statement change. I supplied the algebraic proof rather than replacing the assertion with the weaker arbitrary-ring quasi-isomorphic free replacement. I retained the original source, created fields, chapter, unit and blueprint provenance; `same_as` remains the empty result of the whole-blueprint searches.

## Unfinished work

None in this stage-1 split. No new node remains to be split, no Lean was written, and no compiler/Lake/build command was run.

## Sources and searches

I read `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-lem-int-integral-heart.json`, and the current blueprint `sk-lem-int-integral-heart-local-model.proof.md`, clause (1). The unit's second step and the ancestor's current third proof step need exactly this scalar finite-projective-to-finite-free replacement. This is an ordinary algebra tool within that step; it adds no geometric route.

For the algebra I read Stacks `algebra.tex`, label `lemma-characterize-projective` (Tag 05CF), statement and proof, at lines 18795 onward; and `more-algebra.tex`, label `lemma-dedekind-torsion-free-flat` (Tag 0AUW), statement and proof, at lines 4954 onward, especially part (3). I checked both label/tag associations in `tags/tags`. The coordinate formulas and inverse chain-map calculation are my explicit argument completing the blueprint sentence, so `proof_origin.by` is `agent`, with the blueprint and the two Stacks inputs identified.

The Q72 `msearch.py` calls are all recorded unchanged in `searches.jsonl` and in the item's appended `mathlib_searches`: one LeanSearch, two differently phrased LeanFinder calls, one Loogle, and three grep calls (whole Mathlib, `Algebra/Homology`, `LinearAlgebra`). All services answered. I read the hits as returned, including the full result of the second LeanFinder call. `Module.Finite.exists_comp_eq_id_of_projective` gives a split finite-free surjection, not a coordinate isomorphism. `CochainComplex.of` constructs a complex once the square-zero maps are supplied. `HomologicalComplex.Hom.isoOfComponents` assembles already chosen commuting degreewise isomorphisms. `LinearMap.toMatrix_apply` describes the matrix once bases are chosen. I read the corresponding pinned Mathlib source at `RingTheory/Finiteness/Projective.lean:30`, `Algebra/Homology/HomologicalComplex.lean:507`, and `LinearAlgebra/Matrix/ToLin.lean:621`. These are ingredients, not an exact or one-line-specialized statement of the entire item. No search was invented or recorded as unavailable when it succeeded.

## Not duplicates

There are no new node/existing node pairs because no node is created. Whole-DAG statement searches and `tools/blueprint_refs.py search` with `finite projective scalar complex matrix DVR`, `projective complex`, `matrix`, and `torsion free` found no other blueprint node stating the item. The current parent `det-lem-int-integral-heart-local-model` is geometric and assumes constructibility; it uses this item on the ordinary scalar complexes, rather than duplicating it. `lem-pc-finite-projective-complex-free-model` only promises a bounded-above quasi-isomorphic free replacement and has no two-sided support or strict matrix-coordinate conclusion. `lem-sfb-scalar-matrix-inverse-image` assumes an existing matrix and proves sheaf-pullback compatibility. `lem-sfb-dvr-matrix-smith-powers` diagonalizes one scalar matrix. None states the simultaneous complex-coordinate assertion. The exact needed auxiliary freeness fact was found and reused as `lem-sc-dvr-fg-torsionfree-free`, rather than duplicated.

## Review by Q72

I checked the five steps against every cited node's actual statement, not its proof or title. I also checked the item against the blueprint clause and the two Stacks sources with the source files open. There are no new nodes to source-check.

Step 1 uses the direct-summand characterization explicitly included in `def-weil-pbc-projective-module` (05CF), not merely the word “projective.” Its statement supplies the free module and the two split maps. `def-sc-discrete-valuation-ring` explicitly makes R an integral domain. If r is nonzero and rx=0, every free coordinate of j(x) is killed by r and so vanishes, then sj(x)=x forces x=0. This is a short elementary consequence of those two cited statements; no projective-implies-flat or unrecorded torsion-freeness lemma is used.

Step 2 uses the whole statement of `lem-sc-dvr-fg-torsionfree-free`: DVR, finite generation and torsion-freeness imply finite free. Its hypotheses are respectively the item's hypothesis, the item's degreewise hypothesis, and step 1. I read the cited `def-weil-pbc-free-module`, which defines a basis and the isomorphism from the coordinate direct sum. A finite basis can be enumerated to give R^{n_i}. Outside [a,b] we choose n_i=0 and the isomorphism between zero modules. This choice does not invoke truncation, a projective resolution, completeness, or a change of coefficients. This is the only non-elementary step; its theorem is already a Mathlib leaf.

Step 3 uses `def-weil-matrix` only for the entry family, exactly as that statement defines it. The proof itself supplies the column formula and the finite sum computation; the definition node is not being cited for a matrix representation theorem. Linearity and commutativity of the DVR give the displayed formula on every coordinate vector, including empty sums. The resulting shape has n_{i+1} rows and n_i columns, with the correct column-vector convention.

Step 4 cites no extra theorem. It composes the explicit step-3 identities with d^{i+1}d^i=0 and cancels the injective e_{i+2}; evaluating on a standard vector identifies the (k,j) matrix-product entry. This establishes every entry of D_{i+1}D_i as zero and does not assume a matrix-composition theorem hidden in a definition. It is one routine calculation, written out in the proof.

Step 5 also needs no external lemma: its inverse chain-map equation is obtained by multiplying the step-3 equation by e_{i+1}^{-1} and e_i^{-1}. The two degreewise composites are identities. Thus the conclusion is an isomorphism of complexes with the same two support bounds, not merely an isomorphism in a derived category. All five steps are under 500 characters (the proof totals 1863 characters), so no step above 2000 characters hides a lemma.

I tested P=0 with all n_i=0; a=b (both adjacent terms vanish, so both boundary differentials are zero); a shifted rank-one module; an internal zero degree; the two-term complex [R --pi^m--> R] in adjacent degrees; rectangular maps with unequal positive ranks; and zero rows or columns. For the two-term example the next matrix is zero, and the support boundaries force the other zero products. Noncomplete DVRs also satisfy the proof: no completeness or local-field hypothesis is inserted. A field or the zero ring is outside this project's DVR definition; neither is silently needed. Nonprojective torsion modules such as R/pi are correctly excluded at step 1.

Checklist B: no unsplit/new node, undeclared notion, proof hidden in a new statement, or new leaf missing source lines occurs; TeX is written once; the two Stacks tags match their labels; every search is real; blueprint ancestry and same_as are checked; the full attachment test fails for the reason above. Checklist C: each use is covered by a verbatim excerpt in citations.json; the only non-elementary assertion is the cited DVR finite-free leaf; definitions are used for their stated characterizations only. All five cited nodes are Mathlib leaves, so no off-unit non-leaf tool permission is needed and there is no possible return path to this item through their proofs. Checklist D: the argument stays in the item's own steps, creates no restatement child and no circular induction, and fills the coordinate details omitted by the blueprint. Checklist E: I verified the domain, finite-generation, projective and support hypotheses where each is used; the objects remain scalar R-modules; both compatibility equations are actually calculated; and the edge cases above produce no counterexample or source error. No SGA source is cited.
