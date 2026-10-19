## Worker report

Item: lem-trf-projective-determinant-exact-sequence. Group NY. Stage 1, 2026-10-18.

### Files written

- dag/nodes/sec-trace-formula/lem-trf-projective-determinant-exact-sequence.json: split into eight steps, using existing nodes only. The mathematical statement is unchanged; a reference to the existing tensor-product definition was added, and that node was added to stmt_deps.
- citations.json: one verbatim statement quotation for every node used by every step.
- report.md. Searches are logged in searches.jsonl; write_split.py is sandbox-only preparation material.

New nodes: 0. New Mathlib leaves: 0. No Lean, compiler, Lake, live-project write, or direct git command was used.

### Attachments

None. Searched WeilConjectures in /home/ubuntu/weil-src-slopmaster2 for the item id, projective/determinant/exact-sequence terms, and exterior-power/determinant terminology. No project declaration states the canonical finite-projective determinant-module isomorphism with its wedge characterization and localization compatibility. Scalar determinants of endomorphisms and determinant representations do not give this item. The item has no existing lean_audit declaration to attach.

### WANTED

None. All sources used are in the repository's literature directory.

### Findings and changes

The source is Stacks Tag 0FJB, more-algebra.tex, label lemma-det-ses, first proof, and section-determinants immediately before it. Its first proof explicitly omits well-definedness and invertibility details; those details are written in the split, rather than moved to a restatement node. The source defines determinant modules by constant-rank product factors, while the existing item already uses the equivalent local-top-wedge construction. Steps 2–3 justify that construction as actual rank-one projective modules, including varying rank and empty overlaps. This follows the same top-exterior construction, with standard module-sheaf descent supplying the local formulation already present in the statement.

The proof constructs a global splitting using projectivity of W, explicitly identifies its inverse, and localizes that isomorphism. It therefore does not conceal an invocation of exactness of localization or a flat-tensor theorem. On free charts it uses the already-existing direct-sum exterior isomorphism, expands changed lifts into the U summand, and proves that every extra term vanishes by repetition of a basis vector. Both maps and inverses are patched using the existing module-cover exactness theorem.

The existing Q55 Mathlib-search records were retained. New NY queries were actually run through msearch.py, with LeanSearch, LeanFinder, Loogle and source grep, and a second semantic phrasing. I read the hits and the declarations in ExteriorPower/Basic.lean at lines 212 and 263 and Determinant.lean at line 811. LinearMap.det_eq_det_mul_det concerns the scalar determinant of an endomorphism of a module with free submodule and quotient; it does not construct the required determinant-line isomorphism for projectives. exteriorPower.alternatingMapLinearEquiv and exteriorPower.map provide constituent operations only. No exact match or one-line specialization was found. All new search records reproduce the logged tool/query strings and identify the actual results.

### Blueprint and existing-node searches

Read the chapter sec-trace-formula, unit sk-i-curve-zero, and the current main-20261015 lem-trf-local-term-locality text. This item is a lower module-theoretic input introduced in the existing determinant-calculus branch; its inherited ancestry and its precise from.place are preserved. The unit's realized fields belong to its key node and were not changed.

Ran blueprint_refs.py ancestor for this item and search for determinant, top exterior, and determinant exact over all chapters. Also searched the whole DAG for 0FJB, determinant short exact sequences, exterior-power bases/localization, standard free covers, and module/sheaf gluing. No imported blueprint node states this module theorem. The constant-rank scheme theorem lem-sc-determinant-short-exact was examined but is not used as a substitute for the requested construction. Existing generic algebra and sheaf tools are reused and declared under split_report.tool_uses where appropriate; they support the existing lower-level branch and do not replace a unit step by another unit's argument. No new-node duplicate comparisons are required.

### Unfinished work

None in the stage-1 split. The underlying existing dependency nodes retain their own stage states; this delivery does not claim that the theorem has been formalized in Lean.

## Review by NY

I checked the item against Stacks Tag 0FJB (lemma-det-ses) and the preceding section-determinants, reading both source constructions. The source assumes a commutative ring and a short exact sequence of finite projectives, exactly as the item's direct-summand hypotheses and explicit injectivity/surjectivity/kernel-image conditions specify. No constant-rank, nonzero-ring, characteristic, or Noetherian hypothesis was introduced. I retained the order U first and W second in the wedge, so there is no unrecorded Koszul sign. There are no new nodes whose sources need a separate review.

For step 1 I opened def-weil-pbc-projective-module: its statement includes lifting every map through every surjection, not just the name of projectivity. This applies to id_W and p and gives ps=1. I wrote the inverse using v-s(pv) in im(i), where injectivity gives uniqueness. The finite standard-cover node explicitly supplies finitely many elements generating the unit ideal and free localizations. Multiplying the two partitions of unity proves that their common refinement still satisfies its covering hypothesis.

For step 2 I read lem-weil-pbc-exterior-power-free-basis, including both rank-one top powers and vanishing above the number of basis vectors. These two clauses also show that differing basis lengths on an overlap force the overlap ring to be zero; no uncited invariant-basis-number theorem is needed. I opened new-v2-generic-exterior-power-localization: it applies in all degrees, over arbitrary localization rings and modules, and prescribes the image of each pure wedge. The exterior-algebra definition is a tensor-algebra quotient, so applying a linear map to every tensor factor constructs the wedge map, and its identity/composition equations follow on the stated spanning wedges. The overlap maps form a cocycle. Zero overlaps are handled separately by their unique module maps.

For step 3 I read the full statements of lem-weil-pbc-spec-module-tilde-sections, lem-weil-pbc-glue-sheaves-of-modules, pqf-def-coherent, lem-weil-pbc-affine-tilde-gamma-adjunction and lem-sc-affine-standard-cover-finite-projective. I checked their source passages: Schemes 01HV (lemma-spec-sheaves), 01IA (lemma-quasi-coherent-affine), 01IB (lemma-equivalence-quasi-coherent), Sheaves 00AM (lemma-glue-sheaves-structures), and Algebra 00NX (lemma-finite-projective). The gluing node supplies both objects and morphisms, not merely a definition of descent. Each chart is affine, each local line is an associated module sheaf, and the cocycle is already proved. The affine-local quasi-coherence definition therefore applies; the counit is used only after this check. The standard-open section formula then identifies the global module's localizations with the original lines. Its finite standard cover gives exactly the hypotheses of the finite-projectivity criterion. The same gluing-morphism uniqueness supplies independence of the cover.

For step 4 I opened lem-sc-exterior-top-direct-sum: its statement gives the canonical free-module isomorphism and its inverse's formula on arbitrary pure wedges. The splitting makes its input genuinely a direct sum of finite free modules with r and s basis vectors. Exterior functoriality is written out through the tensor quotient, including the inverse map induced by t^{-1}. This proves invertibility before the gluing step.

Step 5 uses only the exterior-algebra multilinearity/alternation and the basis theorem. Exactness on the explicitly split chart puts every difference of lifts in i(U_h). Expanding r+1 vectors in a rank-r basis necessarily repeats a vector, so those terms vanish. The step is elementary relative to the cited statements; it does not invoke a hidden lemma asserting the exact-sequence determinant theorem itself.

For step 6 I checked the exterior localization statement again and read lem-weil-pbc-localization-tensor-product against Algebra 00DL (lemma-tensor-product-localization). It allows arbitrary multiplicative subsets, without finiteness restrictions. The tensor-product definition states that pure tensors generate; the exterior-algebra definition states that pure wedges span. These make equality of the displayed maps a literal equality on a spanning family. Basis independence is a multilinear expansion with the same coefficients on both sides, and lift independence was already proved, so compatibility on overlaps does not rely on an assumed global map.

For step 7 I opened lem-weil-pbc-cover-module-exact and read Algebra 00EK (lemma-cover-module). Its statement gives both injectivity and existence/uniqueness for compatible families, exactly what is needed to construct gamma, construct its inverse, and verify both composites. I applied it to P and Q themselves, not to an unsupported Hom-localization identification. The finite cover still generates the unit ideal, and tensor localization identifies its P-components with tensors over the localized ring.

For step 8 I tested ranks (0,0), (1,0), (0,1), and (1,1): the formulas give multiplication R tensor R to R, the unit maps, and the ordered two-vector wedge respectively. Over characteristic two, the proof uses x wedge x=0 directly rather than division by 2. Over R=A times B with U=A times 0 and W=0 times B, the two components have ranks (1,0) and (0,1); both constructions give the componentwise unit maps and glue, so no global constant rank was assumed. Over the zero ring all modules vanish, including the module denoted R, and the determinant is its unique rank-one-free module in the permitted zero-ring sense. Localizing a partition of unity preserves it; hence the final localization comparison is justified by the same uniqueness as the global construction.

Against delivery-errors B–E: there are no new statement-only files, no novel definitions, and no restatement nodes. Every proof citation was read from the cited node's statement, and citations.json contains those verbatim statements. The non-elementary operations (free cover, localization of exterior/tensor powers, gluing, affine counit, finite-projectivity recognition, direct-sum top powers, compatible-family exactness) all have cited nodes. The remaining calculations are written out. Each step is below 2000 characters; none hides a separately assumed comparison theorem. No disputed statement or source error was found. The only correction to the input statement was adding its omitted tensor-product definition reference.

## Validation

The required server checks and delivery dry run are run through the approved wrappers; results are recorded below after completion.

Server review_split: PASS, 0 new nodes. Required deliver.py --no-push: exited successfully with OK at dry-run commit 38d4d8d884; server preflight passed (including DAG and split checks). All citation quotes were accepted. The final push runs the delivery tool's checks again on its packaged commit.
