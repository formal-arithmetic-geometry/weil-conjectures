# Worker report: lem-pur-line-unbounded-derived-tensor

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-line-unbounded-derived-tensor.json`: statement, split into eight steps; not a Mathlib leaf. The statement and statement dependencies are unchanged.
- No new nodes, and no new Mathlib leaves.
- `citations.json` records a verbatim statement quotation for every step/node pair. `searches.jsonl` contains this worker's actual search results. `write_split.py` is sandbox scratch work only.

## Attachments

None. The project-source search by `(blueprint: lem-pur-line-unbounded-derived-tensor)` returned none. Concept searches in `lean/WeilConjectures/` found the finite-coefficient Tate-twist preservation declarations and general tensor-resolution declarations, but none states every clause for arbitrary ring sheaves and arbitrary unbounded complexes. In particular the finite constant-coefficient Tate twists are not an attachment for this item.

## Wanted literature

None. All mathematical sources used are available locally.

## Corrections and source audit

No statement dispute or change. The item is a generic ringed-site consequence extracted from proof (3) of `det-def-sp-tate-twist-locally-free`, rather than the unit's key statement. Accordingly no unit record is edited. I read `dag/units/sk-prop-an.json`, the chapter record, and the current main-20261015 Tate-line proof. Its last two sentences give exactly the line/flatness/termwise-tensor/cancellation route retained here.

I read Stacks `sites-modules.tex`, Tags 0B8Q (`lemma-invertible-is-locally-free-rank-1`) and 0B8N (`lemma-invertible`), including their proofs. I supplied the local inverse, its change-of-basis calculation, and both triangle identities that those proofs leave implicit. I read `sites-cohomology.tex` at Tags 06YN, 06YT and 06YU, including the construction before the definition of derived tensor, and `derived.tex` Tag 015F and `homology.tex` Tag 010N. The arbitrary-unbounded comparison is taken from the existing fixed-K-flat-factor theorem, whose statement explicitly supplies a natural comparison on ALL complexes, rather than inferred from the weaker two-resolving-input comparison alone. No SGA source is used.

The item's inherited Mathlib records are retained. Fresh logged LeanFinder searches in two phrasings, LeanSearch, Loogle and grep did not give the full sheaf statement. I read the returned ordinary-module candidate `Module.Invertible.rTensorEquiv` in `RingTheory/PicardGroup.lean`: it concerns modules over a single ring, and does not assert the sheaf or derived comparison. I also read `Algebra/Homology/DerivedCategory/ExactFunctor.lean` at the functor, factorization, shifts, triangulated and linearity declarations; those generic results are already available through existing cited nodes. The initial grep queries with alternation returned zero hits as logged; a subsequent simple `mapDerivedCategory` query returned the exact-functor source, which was then read. These outputs are recorded faithfully, not construed as absence of generic exact-functor results.

## Not duplicates

No nodes were created. Whole-DAG and whole-blueprint searches for invertibility, locally free rank-one sheaves, exact derived functors and tensor-line equivalences were performed before deciding to reuse the existing interfaces. `lem-weil-signed-line-tensor-equivalence` is an ordinary signed-power interface for one specified coefficient-twist line; it does not state flatness, the unbounded derived tensor comparison, cohomology, or the specified inverse-pair identities. `prop-weil-twist-preserves` and `lem-sf-twist-interchange` have special coefficient/constructibility hypotheses and do not replace this generic item. The generic exact-functor and cohomology nodes were cited, not recreated. The newly reused `lem-weil-pbc-kflat-fixed-tensor-triangulated` is declared as an off-unit tool: it supplies homological-algebra infrastructure, without replacing any geometric purity step.

## Review by Q46

I checked the sources with the written steps and each cited node's statement open. In step 1, the sheaf Hom definition really uses maps on the slice, the tensor definition really is sheafified sectionwise balanced tensor, and the tensor-closed lemma supplies the constraints and evaluation adjunction. Thus evaluation has the written local formula and the inverse glues: on overlaps a basis changes by a unit and the dual changes by its inverse. Equality and gluing use the sheaf axiom, not a geometric-stalk conservativity assertion. This is the explicit missing computation in 0B8Q and does not need its own new lemma.

In step 2, the same tensor-closed statement supplies associativity, symmetry and unitors, and the module-sheaf definition supplies the maps' linearity. I checked both displayed triangle composites on pure tensors, including the choice of inverse of ST evaluation as unit and TS evaluation as counit. The argument covers nontrivial gluing because evaluation is basis independent. Step 3 does not just cite the definition of flatness: it proves finite-limit and finite-colimit preservation by the inverse equivalence's Hom bijections and the defining universal properties. Additivity is explicitly in the tensor-closed statement. The small pro-etale skeleton convention supplies the size hypothesis for the module category to be abelian. Flatness is then precisely the cited definition. These three elementary steps contain the written computations rather than an uncited flatness theorem.

In step 4, I checked that the total tensor node's differential leaves only q=0 when the second argument is L[0], with no residual Koszul sign. The cohomology node states the natural exact-functor isomorphism for every complex, not only bounded complexes; it therefore proves acyclicity against every acyclic input as required by the K-flat definition. All terms of L[0] are flat, including the zero terms. In step 5 the fixed-factor theorem's statement is read literally: it assumes a K-flat fixed complex WITH flat terms, supplies both tensor orders and the natural representative isomorphism for arbitrary varying complexes, and states triangle and shift compatibility including the connecting arrow. Step 4 verified both hypotheses. The exact-functor factorization gives the independent termwise functor, and localization parts (2)-(3) give the comparison and its equality under shifts. This avoids assuming the item from an ordinary-module invertibility result or restricting unbounded K to bounded inputs.

Step 6 uses the localization theorem's natural-transformation extension, preservation of compositions and faithfulness, not merely essential surjectivity of the localization. The degreewise evaluations are chain maps by their already checked naturality for each differential. Both triangles and the specified evaluations descend; their shift compatibility is checked before descent. The abstract derived-category definition identifies the complex localization and cone triangles being used. Step 7 uses the full natural cohomology isomorphism of the cohomology node and the abstract cohomology factorization, so it is natural for derived arrows as well as complex arrows. Step 8 uses the actual B-linear derived-category and exact-linear-functor statements; I checked that the former gives linear Q, the latter requires exact additive B-linear sheaf functors (proved in steps 3 and 8), and natural-isomorphism conjugation preserves scalars by bilinearity of composition. Each evaluation component is an R-linear sheaf map, hence B-linear, and remains so after Q. All quoted statements in citations.json are verbatim; full statements are quoted so the relevant hypotheses remain visible.

Edge cases checked: the empty scheme/site, the zero ring (rank one may then be zero), P=R, a nontrivial line with nontrivial basis changes, complexes with terms in arbitrarily positive and negative degrees, and complexes with nonflat cohomology. None of the steps uses nonzero coefficients, local ring stalks, stalkwise descent, flat cohomology or boundedness. All proof steps are below 2000 characters. No clause of the item has been relabelled as a new node, and no new nodes conceal any of these calculations.

## Unfinished work

None for this one-level stage-1 split. The existing dependency nodes retain their own proof obligations. Delivery validation and push are performed with the required launcher tool.
