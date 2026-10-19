## Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-coef-quasicategory-labelled-coproduct-equivalences.json`: statement, split; five proof steps; no Mathlib match.
- `citations.json`: nine verbatim cited-statement excerpts, one for every step/cited-node pair.
- `report.md`: this report. The search command also recorded `searches.jsonl`; its six actual queries and results were appended to the item's earlier search records without deleting those records.

## New nodes

None: zero new nodes and zero Mathlib leaves. The horn argument, assembling witness maps, and restricting them are elementary degreewise arguments inside the proof. The non-elementary equivalence criterion is already `lem-coef-joyal-quasicategory-characterizations`, clause (2), which is cited instead of creating a replacement theorem.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id and the concepts `quasicategor`, `categoricalEquiv`, and `categorical_equiv`, and also searched `dag/lean_names_upstream.json`. No project declaration states the item. The upstream master checkout is not evidence for attachment and was not used as a completed proof.

## WANTED

WANTED: archival copy of Cisinski, *Higher Categories and Homotopical Algebra*, revision July 30, 2026, Remark 3.6.5, Corollary 3.6.6 and Theorem 3.6.8, printed pp.114-116 (online PDF pages 130-131, numbered from 1), for this item. Read the online PDF at https://cisinski.app.uni-regensburg.de/CatLR.pdf .

WANTED: archival copy of Lurie, *Higher Algebra*, proof of Theorem B.0.20, printed p.1485, for this item's edge-pullback accessibility application. Read the online PDF at https://people.math.harvard.edu/~lurie/papers/HA.pdf . Neither source is archived in the named literature directory. I did not download files or modify literature; the actual coproduct argument is explicitly agent-written.

## Existing-node and blueprint searches

I read the chapter `sec-six-functors` and unit `sk-prop-sf-biduality-general`, the ancestor blueprint file `prop-coef-integral-exceptional-adjoint.md`, and the retained parent proof of `lem-coef-categorical-pattern-model-calculus`. Its application of this item is to quasicategories indexed by the set of base edges; it explicitly permits empty summands. The ancestry remains the existing one, with no new unit or changes to unit metadata. The `split_report.blueprint` locates the role in paragraph 2 of the ancestor proof and the explicit parent application.

Whole-DAG searches for labelled coproducts, disjoint unions of quasicategories, componentwise categorical equivalences, and quasi-inverses found the item's existing general quasi-inverse dependency. I opened its statement, not just its proof. I also inspected `lem-coef-quasicategory-invertible-interval`, `lem-cbc-enhanced-functor-cone-calculus`, `lem-coef-infinity-cellular-natural-equivalence`, and `lem-coef-cat-infinity-colimits-cartesian-closure`; none is needed beyond the exact characterization and definitions. The latter's coproduct discussion was not used as if its proof were its statement. `tools/blueprint_refs.py search` was run for `quasicategor`, `labelled`, `quasi-inverse`, `coproduct`, and `categorical equivalence`, across all imported blueprint nodes. No blueprint node states this label-preserving iff. `ancestor` confirms `prop-coef-integral-exceptional-adjoint`. All cited statement dependencies were checked to have a transitive dependency closure omitting this item (66 nodes), avoiding a circular application of the model-calculus parent.

## Mathlib searches

The item's own state has no project Lean attachment. I ran the required `msearch.py Q76 <item>` searches, including a second semantic phrasing, and read their results. All services returned successfully; none was recorded as unavailable or falsely as an empty search.

- LeanFinder: `A categorical equivalence between labelled disjoint unions of quasicategories is equivalent to a categorical equivalence on each summand`.
- Loogle: `SSet.Quasicategory`.
- grep, under `AlgebraicTopology`: `coprod.*(quasicategory|categoricalEquiv)|categoricalEquiv.*coprod|coproduct.*quasicategor`.
- LeanSearch: `A label preserving map of coproducts of infinity categories is an equivalence if and only if each component is an equivalence`.
- LeanFinder, second phrasing: `A functor over a discrete set between infinity categories is an equivalence exactly when every fiber functor is an equivalence`.
- grep, under `AlgebraicTopology`: `weakEquivalence.*[Ss]igma|[Ss]igma.*weakEquivalence|WeakEquivalence.*map`.

The direct grep returned no hit; the model-category grep returned `WeakEquivalence (Limits.Sigma.map f)` at `Mathlib/AlgebraicTopology/ModelCategory/Instances.lean:267`. I opened lines 253-270: this assumes every component is a cofibration and only proves preservation. It cannot be a one-line specialization giving detection for arbitrary component maps. I read the quasicategory horn interface in `AlgebraicTopology/Quasicategory/Basic.lean:33-78`, the ordinary category join equivalences in `CategoryTheory/Join/Basic.lean:633-653`, and `Limits/Shapes/Products.lean:540-543` for `Sigma.map_isIso`. The ordinary category and isomorphism results have different objects and notions of equivalence. They do not state this node, and no Mathlib leaf is claimed. Earlier Q71 searches remain intact; fresh searches have their exact actual query strings and raw logged summaries.

## What was wrong or changed

The imported auxiliary statement is correct, including its empty cases. Its proof was empty. I supplied the proof without changing the statement or its statement dependencies. The main point requiring an argument was that a global quasi-inverse need not initially be specified over the labels: evaluation of the counit gives an edge forcing it to preserve the label. I also wrote the restrictions of the inverse edges and their two triangular witnesses; merely saying that the counit has equivalence components would leave coherent witness data unaccounted for.

The source attribution already says the helper is agent-derived, rather than a named theorem in HA. The online HA proof uses equivalences of all edge pullbacks in its accessibility argument; I do not attribute a separate labelled-coproduct theorem to it. No mathematical source error, statement dispute, change of route, or coefficient-category identification is made. There is no use of SGA or of the purity route.

## Review by Q76

I read the item and every cited statement with the source places open. For the source, Cisinski Remark 3.6.5 and Corollary 3.6.6 identify invertible coherent transformations and quasi-inverse equivalences with Joyal weak equivalences between quasicategories. Theorem 3.6.8 compares this with precisely the ordinary homotopy-category functor tests used by `lem-coef-joyal-model-structure`; thus the proof does not silently substitute weak homotopy equivalence for categorical equivalence. The ancestor blueprint's finite-coefficient mapping-complex paragraph and the parent model-calculus application explain why this general categorical tool is on the route. No new node needs a separate source review.

Step 1 cites `def-cbc-enhanced-diagrams-cones` for the exact horn-filler definition. The connectivity argument is proved there in the step: the two-edge inner 2-horn is connected, and higher inner horns contain all edges. Every horn simplex then has the same label as its vertices and can be filled in its summand. This is a direct definition argument, so only this step is marked elementary. It neither assumes connectedness of an entire summand nor imposes a dimension-zero horn condition.

Step 2 cites clause (2) of `lem-coef-joyal-quasicategory-characterizations`, whose statement explicitly supplies a simplicial quasi-inverse and both coherent natural equivalences, and `def-cbc-enhanced-diagrams-cones`, which defines an equivalence edge by an inverse edge and two triangles. Thus every witness selected in this step is actually available in those statements. Smallness of the family permits choosing the witness data simultaneously in the fixed universe.

Step 3 uses the same two statements. It gives the actual degreewise bijection distributing a product with a standard simplex over the disjoint union. Maps, inverse maps, and both triangle maps are assembled along that bijection, and their face equations hold on each summand, hence globally. This supplies precisely the coherent equivalences required by clause (2); closure of the total objects under horns was already proved in step 1. No external coproduct-preservation theorem, model enrichment claim or pointwise-equivalence theorem is assumed.

Step 4 applies clause (2) only to the total quasicategories provided by step 1. Evaluation in the functor simplicial-set definition gives an actual edge in the total target. Its endpoints have equal labels because operators preserve labels. Since f preserves the label, this forces g to preserve it at each vertex; applying a vertex operator to any simplex then forces its whole image to lie in the same summand. This explicitly constructs each restriction, rather than treating essential image containment as a formal factorization assertion.

Step 5 cites the same inverse-triangle definition and clause (2). I checked the restrictions for all witness parameters, including r=2: the vertices of the triangle in the functor simplicial set are the two composite/identity functors, so they already preserve labels. Consequently every image simplex has label i, the triangle maps really do factor through the summand, and their face equations restrict unchanged. Those are inverse edges in the summand functor simplicial sets, not just pointwise invertible edges. Clause (2) then gives every desired categorical equivalence.

For hypotheses and small cases I checked I empty, an empty component on both sides, a map from an empty component to a nonempty one, and disconnected components. The last asymmetric empty case cannot occur under a global equivalence: a vertex of Y_i would yield a vertex of X_i by the evaluated counit, while a vertex of X_i already maps into Y_i by f_i. A vertex-free simplicial set is empty in every degree, so empty restrictions require no arbitrary choice of an object. For disconnected components the proof checks each vertex and simplex separately; no assertion that a component label is a connected component is made. The small coproduct, its maps and witnesses all stay in the given universe. No full-library build or Lean execution was used.

I checked delivery-errors B through E: statements and definitions are self-contained through their cited notions; the existing characterization states exactly the non-elementary fact used; no proof of a cited node is borrowed as if it were a statement; no new node relabels an item clause; and the inverse data and empty cases are explicit. Each of the five steps is below 2000 characters (801, 662, 861, 825, 1434 at initial writing), so no long-step exception or hidden standard comparison is used. The local citations file contains a verbatim statement substring for every cited node in every step.

## Unfinished work

No mathematical part of this item's one-level split remains unfinished. Independent maintainer review and the normal future splitting of its existing dependencies remain the project's next stages. The remote split review and required delivery dry run have passed; final push is performed by the authorized direct-delivery command.

## Validation

`srvcheck.py ... review_split` exited successfully: `lem-coef-quasicategory-labelled-coproduct-equivalences: PASS; 0 new nodes; proof written by an agent`.

`deliver.py Q76 lem-coef-quasicategory-labelled-coproduct-equivalences --no-push .` exited successfully: `OK (not pushed) deliver/Q76/lem-coef-quasicategory-labelled-coproduct-equivalences at fc7e9e1a5c: preflight passed`. This runs the required server preflight, including DAG and split checks. The only edit after that check is this report recording its result. No Lean, compiler, Lake, local preflight or live-project write was run.

## Delivery repair

The prior delivery was returned solely because preparation timed out while fetching the existing remote delivery branch (`git fetch ...` exceeded 180 seconds). I retained the completed split and all required report sections, citations, and search records. This retry performs the required server-side checks and delivery again; no mathematical or DAG change is needed.
