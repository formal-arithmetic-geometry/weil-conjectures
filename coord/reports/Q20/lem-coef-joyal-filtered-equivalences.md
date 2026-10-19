# Q20 repair: lem-coef-joyal-filtered-equivalences

## Files written

- dag/nodes/sec-six-functors/lem-coef-joyal-filtered-equivalences.json: the returned eleven-step proof with only step 5 replaced, proof_deps updated, status split and split_report updated. The statement, stmt_deps, Lean record and the other ten proof steps are unchanged.
- dag/nodes/sec-six-functors/lem-coef-finite-simplicial-subcomplex.json: statement, exact Mathlib leaf SSet.instFiniteToSSet, Mathlib/AlgebraicTopology/SimplicialSet/Finite.lean:85-90. One new node, one Mathlib leaf.
- citations.json: twenty step/node entries, quoting the actual dependency statements verbatim.
- searches.jsonl: retained the five prior item searches; appended four real searches for the new leaf, all through msearch.py. The node records those exact queries and actual results.

The sandbox initially had only search logs and dispatcher markers, no item or report. I recovered the returned proof from the current shared node and kept the prior Q30 report separately as prior-Q30-report.md; its historical checks and citations are not erased or represented as new Q20 research. repair.py is an editing aid, not delivered as a project file.

## Attachments

None. Searching the read-only WeilConjectures tree for the exact blueprint id, Joyal and categorical-equivalence notions found no project declaration stating this item or the new finite-subcomplex result. The existing stage-2 Lean record is retained exactly; a statement with sorry is not a finished attachment. No Lean was written or compiled.

## Literature wanted

WANTED: archived Cisinski, Higher Categories and Homotopical Algebra, Construction 3.3.1, Definition 3.3.3, Remark 3.3.4, Theorem 2.4.19 and Corollary 3.9.8, for the item. The prior Q30 report records a direct reading of printed pp.92-95 and 134-135 and HTT is the unchanged node source. Fresh online retrieval in this repair failed with HTTP 429; I do not claim a fresh PDF reading. The item remains agent-written, and no missing source was downloaded. The newly added result was checked directly in the installed Mathlib source, not inferred from a search summary.

## What was wrong and what changed

The human's return identifies precisely step 5, 2061 characters: its product finiteness and subcomplex finiteness arguments hide reusable lemmas. I kept the finite-test/small-object route and every other step. For the product argument I found the existing exact Mathlib leaf lem-cbc-finite-simplicial-product, so created no duplicate. For subcomplex finiteness I found SSet.instFiniteToSSet and created an exact Mathlib leaf. The finite interval, trivial-cofibration properties and fibration recognition already occur explicitly in lem-coef-joyal-interval-boundary-tests; no fresh node restates these. New step 5 is 1209 characters and cites those results; it stays non-elementary. The resulting proof has no non-elementary step over 2000 characters. No item statement change or statement dispute is involved, and the stage-2 Lean record stays valid.

## Not duplicates

lem-coef-finite-simplicial-subcomplex vs lem-cbc-finite-simplicial-product: the new leaf concerns an arbitrary simplicial subset of a finite ambient simplicial set; the existing leaf concerns the binary product of two finite simplicial sets. The product leaf is cited directly.

lem-coef-finite-simplicial-subcomplex vs lem-coef-finite-simplicial-hom-filtered-colimit: finiteness of a subcomplex is different from finite presentability of a given finite simplicial set.

lem-coef-finite-simplicial-subcomplex vs lem-coef-joyal-interval-boundary-tests: the interval node supplies a particular finite interval and its Joyal lifting tests, not a theorem on arbitrary finite simplicial subsets.

Whole-DAG searches for SSet.instFiniteToSSet, SSet.finite_of_mono, finite simplicial subsets/subcomplexes and nondegenerate simplices found no node stating the new fact. Keyword hits about finite embedded resolutions, small bisimplicial subobjects and compact support do not state it. blueprint_refs.py searches for finite simplicial, finite simplicial subset, simplicial subset, subcomplex and nondegenerate found no duplicate blueprint statement. No Stacks tag is claimed for the Mathlib result. The new node is neither a clause of the item's categorical-equivalence assertion nor a renamed version of that assertion.

## Review by Q20

I read the standing brief, stage-1 document, delivery-errors B-E, SETUP's three levels, GOAL, dag-sync, the chapter and unit records. I read the ancestor's main-20261015 proof file at sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md: its second paragraph and displayed derived Hom computation explain the existing foundational ancestry. The repair changes only a supporting internal finite-test argument; it changes no unit or coefficient route and uses no SGA source. Current shared main contains the returned eleven-step proof and stage-2 Lean record. The delivery tool overlays split-owned fields onto fresh server main, preserving those maintainer fields. No git command was run in the shared repository.

For the new leaf I read Finite.lean:30-34 and 85-99. Finite means the total set of nondegenerate simplices is finite, not merely degreewise finiteness. At 85-90 the instance has exactly [X.Finite] and A : X.Subcomplex and concludes SSet.Finite A. The adjacent finite_of_mono theorem at 94-99 independently confirms the generality. All four actual searches (LeanFinder, Loogle, grep and LeanSearch) returned this result or its generalization. Since there is an exact match, a second negative phrasing is unnecessary. I also read the existing product leaf and FiniteProd.lean:78-81: both factors finite implies the cartesian tensor finite. It is an existing Mathlib leaf and therefore requires no off-unit tool-use exception.

I reopened the full statements of every node cited in the repaired proof. The citations file copies their statements verbatim, so it also records the formulas supporting each use. I checked the individual steps as follows.

1. The colimit definition supplies its universal property and filteredness; the enhanced-diagram definition supplies simplicial shapes; the nondegenerate-decomposition leaf supplies the unique degeneracy representation. The step itself proves the finite representative/equality calculus by common stages and equalization and then finite simplicial generator relations. I checked the eventual-equality passage in Stacks categories.tex, section-directed-colimits (04AX). The argument allows parallel arrows and noninjective transitions.
2. The Joyal model statement explicitly gives inner horns as trivial cofibrations, fibrancy as quasicategory status and the two weak factorization systems. The step writes the natural horn replacement, finite-stage horn filling and cell-by-cell left lifts; it does not assume the theorem being proved.
3. The colimit universal property is sufficient for the written compatible-family and two-index calculations. Step 1 supplies finite horn presentability. The comparison respects labelled cells, units and the actual diagram arrow, so no unproved arrow identification is concealed.
4. The natural unit square and the model statement's two-out-of-three give the elementary reduction to quasicategories, without imposing fibrancy on original inputs.
5. The interval-tests statement explicitly calls its interval finite, states all displayed maps trivial Joyal cofibrations, and gives the exact lifting recognition between quasicategories. The model statement gives inner-horn trivial cofibrations. Standard simplex finiteness follows from the injective monotone maps already identified in step 1. The product leaf applies with the finite standard simplex and finite V. The new subcomplex leaf then applies to the displayed degreewise union inside that product and to horns inside standard simplices; no dimension bound or ancestor-in-subset argument remains inline. The types are indexed by integers and two endpoints, a small set. At n=0 the displayed domain is one endpoint, and the test is retained. Both quasicategory hypotheses are reserved for step 8.
6. The interval and model statements supply the trivial cell maps and the lifting-class characterization. The step gives its labelled square sets, strict factorization, naturality and recursive lifting argument. Finiteness of domains established in step 5 is exactly what its finite-stage lift uses.
7. The colimit definition supports the universal-property commutations, and step 1 gives representatives of BOTH maps of a square and eventual satisfaction of its equation. The step proves injectivity of label comparison and compatibility with both factorization maps explicitly, rather than assuming closure of arbitrary trivial cofibrations.
8. The inner-horn lifts prove E(f_j) a quasicategory over the already quasicategorical D_j. Only then does the cited interval theorem apply. The model statement supplies two-out-of-three and makes a weak-equivalence fibration lift all monomorphisms, including the empty boundary.
9. Both boundary ends are finite by step 1. Common-stage representatives give a genuine stage lifting square. The relative-boundary-cell Mathlib leaf states precisely the skeletal filtration used to extend lifts to every monomorphism. The model weak factorization system then identifies the colimit map as a trivial fibration. There is no appeal to Joyal filtered-colimit stability in that argument.
10. The strict colimit factorization and the model two-out-of-three/composition property finish the quasicategory case from steps 7 and 9; this is elementary.
11. The natural unit square, step 3's actual-arrow comparison and the model two-out-of-three yield the original assertion. Degreewise union is the stated colimit. All constructions are small after the stated universe enlargement, as the model and interval statements allow. The original item statement and its Lean record are byte-identical to the shared base.

For B1-B10 the new node has a complete standalone statement, inline meaning of subcomplex, a definition dependency, a genuine exact Mathlib match with file and line, no proof sketch or proof steps, and correct inherited chapter/unit and blueprint from/via. Its source is Mathlib, so no invented Stacks tag is needed. Empty subcomplex, empty ambient set, full subcomplex and dimension-zero subsets all satisfy the statement. The misleading alternative 'degreewise finite' was explicitly ruled out by reading Finite's definition. The node is a library leaf required by the human's extraction request, not an unnecessary unsplit elementary lemma.

For C1-C8 and D1-D5 every external assertion of repaired step 5 is now the statement of a cited node; no proof of another node is borrowed. The proof_deps list is exactly the union of uses. The new node points only to the simplicial-set definition, so cannot create a cycle back to the item. The existing product node is a Mathlib leaf. No new off-unit theorem or unit realization change is needed. The remaining ten proof steps are preserved exactly as instructed, and none exceeds 2000 characters.

For E1-E7 I checked n=0, empty simplicial sets, full and empty subcomplexes, products with empty factors, constant diagrams, noninjective transitions, parallel arrows and the nonempty-index condition. In particular the use of the fibration test is restricted to quasicategories and the two factorization endpoints are established fibrant before it. No claim that all Kan weak equivalences are Joyal equivalences occurs. The repair replaces exactly both hidden combinatorial arguments identified by the return and retains all other proof content.

## Validation

The initial interrupted dry runs had no retained final output; no delivery process remained active before restarting. They ran before report.md existed and cannot constitute validation. The completed packet is now submitted to the prescribed stage-1 dry run; its final result is recorded below when available. No local check_dag, review_split, preflight or Lean compiler was run.
