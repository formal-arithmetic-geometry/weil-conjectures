# Stage-1 report: lem-sfb-relative-opposite-root-reflection-map

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-opposite-root-reflection-map.json`: item, split into seven steps, statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-rank-one-local-matrix-model.json`: new statement-only structural classification, status unsplit; no Mathlib match.
- `citations.json`: a verbatim statement witness for every step/node citation.
- `searches.jsonl`: genuine msearch.py results, retained unchanged.

The temporary `write_split.py` is sandbox scratch, not a delivery file. No Lean, compiler, Lake, repository write, or direct git command was used. The item had no earlier sandbox copy or report, and no released repair note was present. The live item was unsplit. It is not a key node of the unit, so no unit record is changed.

## Attachments

None. I searched the project source under `lean/WeilConjectures/` for the exact blueprint tag and for coroot, root-exponential, opposite-root, root-subgroup, relative reflection, and semisimple-rank terminology. The group-scheme centralizer-equation declarations are matrix-subgroup facts over fields; they do not state this relative construction. The source contains no declaration matching the entire item or the new relative classification. Existing sorry declarations would not count as attachments.

## WANTED

WANTED: `literature/conrad-reductive-group-schemes.pdf`, Brian Conrad, *Reductive group schemes*, Lemma 4.1.3 (printed pp.108-109), Theorem 4.2.6 and its proof (printed pp.120-126), Definition 5.1.1 and Lemma 5.1.3 (printed pp.136-137), Theorem 5.1.8 and proof (printed pp.139-140), and Corollary 5.1.9 and proof (printed pp.140-142), for the item and the new classification node. I read these online at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf without downloading them. The agent proof_origin records the assembly argument in full. Conrad is the source; no SGA source is used.

## Audit findings and corrections

The original statement is faithful to Conrad and is unchanged. Its empty proof needed an actual construction and arbitrary-ring argument. I first considered adding a separate rank-one centralizer node, then found the existing relative centralizer-normalizer node together with the field rank-one-reflections node already suffices. Thus only the genuinely missing local matrix classification is created. The field classification alone cannot be applied over A, and neither can a geometric-fibre equality of two group-scheme morphisms prove equality over a nonreduced base.

The pairing is fixed by its local matrix normalization, and its overlap uniqueness is proved with dual numbers: coefficients p and q yield equal lower Gauss coordinates 1-p epsilon and 1-q epsilon, forcing p=q over the overlap ring. Once the pairing is fixed, X=(c-1)e and Y=f give every unit c as 1+beta(X,Y), and the unique torus coordinate forces equality of coroots. This avoids assuming that two pairings agree because they agree on fibres. The generator condition on x means its coefficient a is a unit, rather than merely a nonzero element.

During self-review I replaced small-etale representable descent with the existing stronger fpqc descent leaf. That leaf directly supports both ordinary open gluing and equality on matrix lifts of PGL2 points. It removes the need to assert an unproved projective-coordinate identification. All proof_deps were recomputed as the exact union of uses. Every step is shorter than 2000 characters. No statement dispute, target change, or departure from the inherited unit route was needed.

## Mathlib and duplicate searches

The exact commands and actual results are in searches.jsonl and mathlib_searches. The item retains its four inherited searches as required, and adds this run's searches. For the new node I searched the classification in two semantic phrasings (LeanSearch and LeanFinder), searched a centralizer phrasing, ran Loogle and then a valid alternative pattern after the first pattern reported an unknown identifier, and searched both AlgebraicGeometry and all Mathlib for reductive/root-subgroup/semisimple-rank/classification terminology. The new node's id was chosen before these searches. There was no unavailable service. The invalid Loogle pattern is recorded as inconclusive, not evidence of absence.

I read the returned hits. `SpecialLinearGroup.centerEquivRootsOfUnity` (LinearAlgebra/SpecialLinearGroup.lean:425) and `Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity` (LinearAlgebra/Matrix/SpecialLinearGroup.lean:297) compute abstract group centres. `Subgroup.centralizer` (GroupTheory/Subgroup/Centralizer.lean:35, its membership formula) is an abstract subgroup, not a smooth group scheme. `RootPairing.reflection` and `reflection_apply` operate on a supplied root pairing; they neither construct root subgroup exponentials nor a coroot from G. The reductive grep hits in Algebra/Lie/Semisimple/Defs.lean:70-77 are characteristic-zero Lie-algebra terminology. None is a one-line specialization giving the new result or the item.

Whole-DAG statement/source searches included Conrad 4.1.3, 4.2.6, 5.1.8, rank-one classification, rank-one centralizer, opposite-root, and relative root-exponential terminology. Whole-blueprint searches with blueprint_refs.py included opposite-root pairing, three-exponential normalizer, semisimple rank one, centralizer of a torus, rank-one centralizer, rank-one classification, and rank one matrix; no same-statement blueprint node was found. The exact new id is absent in the DAG, latest blueprint and project Lean source. Existing nodes cited in the proof were opened and their statements read.

The ancestor tool returns `None`, as it does for the inherited item chain. I retained that null blueprint.from.node and the inherited via chain, placing the new item at its front only on the new node. The latest blueprint is main-20261024 (ef6f9619fdbffa59e88528fb56483d76c70258c8). I read its direct-images proof (3), together with the item unit and chapter records. The refinement remains below the inherited alteration/root-model prerequisite; it changes no chapter or unit route.

## Not duplicates

lem-sfb-relative-rank-one-local-matrix-model vs lem-sfb-split-rank-one-classification: the existing result is over an algebraically closed field; the new result is a Zariski-local isomorphism over an arbitrary nonzero Noetherian base ring with split maximal torus, including nonreduced and mixed-characteristic rings.

lem-sfb-relative-rank-one-local-matrix-model vs lem-sfb-relative-opposite-root-reflection-map: the new classification concerns every reductive group of semisimple rank one and provides actual group-scheme matrix charts; it asserts no pairing or three-exponential reflection identity. The item constructs and glues those objects and proves their formulas by matrix multiplication.

lem-sfb-relative-rank-one-local-matrix-model vs lem-sfb-relative-torus-centralizer-normalizer: the existing result represents centralizers and normalizers and computes Lie invariants, but gives no reductive rank-one matrix classification.

lem-sfb-relative-rank-one-local-matrix-model vs lem-sfb-reductive-rank-one-reflections: the existing result is over an algebraically closed field and gives the field SL2/coroot/reflection theory. It does not trivialize a group scheme over neighborhoods of points of a general ring.

lem-sfb-relative-rank-one-local-matrix-model vs lem-sfb-local-split-root-data-weyl-lifts: the existing local-root-data statement supplies weights, root lines and normalizer representatives for general reductive groups over local rings. It neither states a group-scheme classification by SL2/PGL2/GL2 models nor gives such local pair isomorphisms; it also depends on the item.

## Review by NS

I read Conrad's statements and matrix proof at the printed pages listed above. For the new node I checked precisely that Theorem 5.1.8 is a Zariski-local classification of the pair, with a split central torus factor, in all three cases, not an isomorphism merely of geometric fibres. Its printed hypothesis is a split triple: Definition 5.1.1 and the proof of Lemma 5.1.3 explain the additional Zariski refinements once T is already split. Over the local neighborhoods the root lines can be made free, the weights made constant, and the coroot characters made constant; the resulting local classification is exactly the form stated in the new node. Choosing the positive matrix root only requires swapping the two diagonal entries. This result is structural input, not any clause of the item's conclusion. Its proof is not stored in the unsplit node. Its eventual proof can follow the three cases in Conrad's Theorem 5.1.8: quotient by the central codimension-one torus, identify the quotient as SL2 or PGL2, split the associated SL2 central extension, and distinguish the central mu2 embeddings to obtain GL2 in the remaining case.

Step 1 uses the explicit Hopf-algebra definition of D_R(M/L) to embed the primitive root kernel, and the tangent-weight base-change statement to know that alpha is a root on every geometric fibre. The finite-type/Noetherian finite-presentation leaf has exactly the algebra hypothesis of the affine G. The relative centralizer statement then gives smoothness, closedness, finite presentation, and base change. I use the field rank-one-reflections statement only on algebraically closed geometric fibres, where its definition of the largest subtorus and of the centralizer is identical. It gives reductivity and semisimple rank one there. Integer row operations and the observation that no integer character of a torus can be nonzero torsion prove the primitive-kernel description; no reducedness of mu_n is assumed.

Step 2 uses the canonical-root-exponential node for equivariance, tangent inclusion and uniqueness, all of which its statement explicitly includes, also after base change. It is applied to H, whose required hypotheses were proved in step 1. The new classification gives the actual group-and-torus isomorphisms. Differentiating the two displayed unitriangular maps gives the root bases, and the coroot h(c) has character c^2 in SL2, GL2 and PGL2. No structure on any other root line is used.

Steps 3 and 4 contain the argument rather than quoting a new pairing lemma. I multiplied both sides of the Gauss formula. The inverse coordinate calculation gives uniqueness of the three factors, including in PGL2 after passing to scalar-equivalent lifts. The fpqc representable-descent statement gives equality detection there. Applying it to dual numbers in step 4 really detects nilpotent differences: epsilon times a scalar is zero only when that scalar is zero, because R[epsilon]/epsilon^2 is free over R with basis 1,epsilon. The argument uses no field, no inversion of 2 and no geometric-point test. Evaluating at (c-1,1) then handles every torus unit, proving the coroot agreement as a morphism.

Step 5 uses only the gluing and uniqueness clauses of the fpqc representable-descent leaf. They apply on the indicated scheme domains after a finite principal-open refinement of the base cover; those are flat quasi-compact jointly surjective families, hence satisfy its fpqc hypothesis. Bilinear and homomorphism identities hold locally and therefore globally by uniqueness. The inverse local duality maps agree since an inverse to a fixed map is unique, proving perfection globally.

Step 6 is the explicit three-matrix product and diagonal conjugation. I checked the signs, the factor chi_alpha(t), and the inverse on the right side, including the PGL2 coroot [diag(c,c^-1)] rather than [diag(c,1)]. The character-square identity makes the displayed torus action an involution, so preservation is equality of subgroup functors. The only external fact used in this step is equality detection by fpqc representable descent, which says exactly that. It works for every further C, so the conclusion is scheme-theoretic normalizing, not just a rational-point assertion.

Step 7 uses the field rank-one-reflections statement only for identifying the already constructed coroot and nonidentity reflection class on geometric fibres. The tangent-weight and exponential nodes give the explicit base-change comparisons and successive compatibility the step quotes. The matrix charts pull back, and the dual-number overlap proof holds over every new coefficient ring, so arbitrary base change requires no new Noetherian hypothesis. This also proves the successive comparison, rather than leaving 'compatibility' implicit.

I tested the item and new node on SL2 over Z, SL2 over F_2 and over F_2[epsilon]/epsilon^2, PGL2 in characteristic two (where the coroot need not be primitive), GL2 with an extra central torus, and a line-bundle twist GL(O plus L). The last case explains why the classification must be local and why no global root basis can be presumed. A disjoint base can use different local types; the new statement permits this. Rank zero yields no nonzero alpha and hence no instance of the item. If B is the zero ring the pulled-back scheme is empty and all required identities hold uniquely. The matrix formulas also handle arbitrary units a, not just 1.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the files. New statements are self-contained with cited or inline definitions; the new node has no proof or proof_deps, genuine recorded searches and a specific blueprint place. Each cited statement gives exactly what the step uses, as witnessed in citations.json. Every remaining operation is either written out or cited; no non-elementary statement is hidden behind 'transport' or 'standard'. The required delivery dry run runs the DAG check and server review on the server. The optional preliminary review was canceled while still queued, after report.md was finished, so there is only one active required dry run. No other agent performed this review.

## Unfinished work

The single new node is intentionally unsplit, as required by the one-level split contract. No part of the item's argument is postponed. Independent maintainer review remains part of landing.

## Delivery validation

The first required dry run reached server preflight after 3709 seconds in the shared queue. It returned a single B4 formatting diagnostic: the valid TeX row separator immediately before the entry b in the lower unitriangular matrix matched the doubled-command-backslash checker. I replaced the two unitriangular matrices in step 2 with I+aE_12 and I+bE_21 and explicitly defined E_ij. This is the same matrix calculation with checker-compatible notation.
