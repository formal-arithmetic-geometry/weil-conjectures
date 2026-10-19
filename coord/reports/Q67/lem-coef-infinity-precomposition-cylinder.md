# Q67: lem-coef-infinity-precomposition-cylinder

## Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-precomposition-cylinder.json: statement, split by an explicit degreewise argument; not a Mathlib leaf.
- citations.json: one verbatim statement quotation for each of the four proof-step citations.
- searches.jsonl: actual Mathlib searches recorded by msearch.py; inherited item search records are retained in the item.
- report.md: this report.

There are 0 new nodes and 0 new Mathlib leaves. No unit or chapter file changed.

## Attachments

None. Searching WeilConjectures/ in the supplied slopmaster2 source for the exact blueprint tag and for precomposition, quasicategories and simplicial homotopies found no project declaration stating this item. The precomposition hits concern ordinary categories, modules, or scalar operations, not internal simplicial functor objects. No upstream-master sorry declaration was treated as a finished proof.

## Wanted literature

WANTED: Kerodon, Construction 1.5.3.1, tag 0060, https://kerodon.net/tag/0060, an archival copy under literature/, for lem-coef-infinity-precomposition-cylinder. The page was read online on 2026-10-17. It defines Fun(S,T) and evaluation; the parameterized cylinder below is my own degreewise proof. This is a Kerodon tag, not a Stacks tag. I did not download or change literature. Accordingly proof_origin.by is agent.

## Issues and changes

The mathematical statement is correct and unchanged. Its old title referred to a coherent natural equivalence, whereas its hypothesis is only a simplicial homotopy. I aligned the title with the actual hypothesis. No equivalence-edge or core assertion is inferred: that belongs to the existing lem-coef-infinity-core-cylinder-restriction.

The statement's notation (F,t) is shorthand, so a vertex-level formula alone would not prove the result. Steps 1 and 2 give the map on every n-simplex and check every simplicial operator. The source uses Delta^n times S rather than K times Delta^n; our existing definition uses the latter convention, and the proof consistently uses it throughout.

I read the chapter and unit records, the current main-20261015 ancestor file at sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.md, and the ancestor's DAG proof and dependency chain. The main blueprint file states the exceptional-adjoint result without its auxiliary section-space argument. This item supplies a concrete subordinate simplicial calculation through the already-recorded section-restriction chain; it changes no unit-level route or coefficient hypothesis.

## Searches and reuse

Whole-DAG searches used the item tag, precomposition, internal functor, simplicial homotopy, cartesian closed and 0060. blueprint_refs.py searches for precomposition, internal functor and simplicial homotopy found no blueprint node stating this exact cylinder. The ancestor command confirmed prop-coef-integral-exceptional-adjoint. I read the statements of the nearby core-cylinder restriction, equivalence-section restriction, simplicial-derived exponential and marked-homotopy precomposition nodes rather than assuming their titles gave the desired fact.

The existing lem-cbc-marked-homotopy-precomposition contains a more general marked relative cylinder formula and extra component-marking assertions; it does not state this item's target naturality. No duplicate node is created: this inherited item is proved directly from the concrete definition, avoiding the need to introduce marked objects and an overcategory merely to forget them. lem-coef-simplicial-derived-exponential concerns enriched model categories and homotopy-category maps, not the present simplicial set. The core-cylinder node explicitly depends on this item and cannot be cited back.

The new msearch.py log contains LeanSearch, LeanFinder, Loogle and grep searches. Two semantic phrasings were tried, including the more general cartesian-closed formulation. The first returned relative-morphism/model-category homotopies, not a homotopy on a variable internal functor object. The second returned generic currying/evaluation ingredients. I read RelativeMorphism.lean lines 140–159, Monoidal/Closed/Cartesian.lean, Monoidal/Closed/FunctorToTypes.lean, and SimplicialSet/Monoidal.lean. The generic exponential is constructed via natural transformations from representables; identifying it with the concrete simplicial functor object and checking the cylinder's endpoints/naturality is not a one-line specialization of a returned declaration. Thus the item is split rather than marked mathlib.

I recorded the invalid Loogle identifier query as inconclusive, not evidence of absence. An exploratory grep used the nonexistent CategoryTheory/Closed directory; its zero hits likewise prove no absence, and the record says so. The corrected grep in CategoryTheory/Monoidal/Closed returned curry, uncurry and pre. The file-specific Monoidal.lean grep has a formatting limitation in msearch.py's displayed filenames; I read the actual named file and recorded the raw log unchanged. No invented search or unavailable-service verdict is recorded.

## Review by Q67

For the item I read Kerodon 0060 online, specifically its formula for the n-simplices of Fun(S,T) and the diagonal-based evaluation map. I also read the whole statement of def-cbc-enhanced-diagrams-cones, the sole cited dependency. It explicitly supplies standard-simplex coordinates as monotone maps, degreewise products, the concrete functor simplicial set and its parameter-restriction operators. There are no new nodes needing separate source review.

Step 1 uses that dependency for the type of f, t and their coordinates. The displayed equation is precisely the simplicial naturality equation for eta, so g_t really is a simplicial map in its input degree before composing with f. This does not assume a cartesian-closure theorem, horn extension, or naturality theorem for evaluation.

Step 2 uses the dependency's exact operator formula. I checked both composites on a degree-r pair, including the order t alpha a: both have second coordinate alpha a and first coordinate eta_r(k,t alpha a). Associativity then gives the required operator equation for H. This is a direct definition calculation, not a hidden identification or comparison lemma.

Step 3 uses the concrete functor n-simplex definition to identify the two restrictions on all simplices, not only objects. Constant t makes the first coordinate u(k) or v(k) by the actual endpoint hypothesis on eta. For a vertex F, taking its degenerate n-simplex gives the edge F eta; this justifies the statement's notation without assuming eta has invertible tracks.

Step 4 uses the dependency's operator formula to check q_* by associativity and then writes the target-naturality square as an equality on every (f,t). q is any simplicial target map, so no additional preservation theorem or equivalence hypothesis is used. All four cited quotations in citations.json are literal substrings of the dependency's statement and describe the concrete data used.

I tested K empty (the functor simplicial set is terminal and the formula is unique), K a point (the cylinder is constant in the parameter), constant eta, n=0, repeated/degenerate parameter maps, and empty C. For nonempty K and empty C the formula has empty input wherever needed; for empty K it gives the unique map, so no nonemptiness is assumed. The proof only uses simpliciality, hence in particular works for the stated quasicategory targets and needs no extra smallness or fibrancy condition. Products and Hom sets are taken in the fixed containing universes of the dependency.

I checked delivery-errors B–E: no new or restated clause nodes, no undeclared non-elementary fact, no proof-only dependency being used as a statement, no cycle from a dependent core lemma, and no strengthened hypotheses. Every step is elementary because its full argument is a coordinate formula plus a substitution or associativity equation; none exceeds 2000 characters (lengths 704, 605, 644, 609). I corrected the loose object-level description by providing these explicit formulas. All original provenance and inherited search records are preserved.

## Unfinished work

None in this split. The missing archival source is requested above. Remote dry-run and push results are recorded by the delivery tool.
