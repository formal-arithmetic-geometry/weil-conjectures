# Stage-1 delivery: lem-sfb-space-global-sections-amplitude

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-global-sections-amplitude.json`: item, split into four steps; statement and statement dependencies unchanged; inherited searches and provenance retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-qcoh-cohomology-finite-bound.json`: one new statement-only, unsplit node; ordinary quasi-coherent sheaf cohomology vanishes above one integer on a fixed qcqs algebraic space (Stacks 072C). Not in Mathlib after actual logged searches.
- `citations.json`: twelve step/node entries, with literal excerpts of the cited statements (full statements where that makes the hypotheses clearest).
- `report.md`: this report. `searches.jsonl` is the unmodified log written by msearch.py.

## Attachments

None. Searched the project Lean under `lean/WeilConjectures` by the exact blueprint tag, algebraic-space terminology, global sections and finite cohomological dimension. There is no declaration stating this item. The generic theorem `CategoryTheory.Functor.isLE_rightDerivedFunctor_obj` in `CategoryTheory/DerivedCategory/FiniteCohomologicalDimensionAmplitude.lean` is not an attachment: its bound is on every object of the ambient abelian category, whereas here the bound is only on quasi-coherent modules. Its project declaration does not establish the geometric hypothesis needed here.

## WANTED

None. All mathematical sources used are available locally.

## What was wrong or incomplete

The item was statement-only, with no proof. Its statement agrees with 08F7(3) using 072C and 05TC, so no statement dispute or correction was needed. There was no prior sandbox split or report to recover.

The reviewed affine-chart bound depends on this item. Neither it nor the derived space-pushforward bound may be cited to establish the present bound. I followed the maintainer's explicit note there: use 072C directly. The generic product-preserving derived-functor upper-bound node has no dependency path back to this item and is reusable.

The inherited blueprint ancestry contains `from.node: null`: the ancestry command likewise returns None. Its long via chain eventually reaches a declaration name rather than a DAG id. This existing provenance gap is retained and explicitly described, not replaced by an invented ancestor. The new node prepends this item to the inherited via list and records the ordinary-sheaf finite-bound sentence it supplies. I read the latest blueprint direct-images proof, especially paragraph (3), and the current chapter/unit records; this is supporting geometry below the fixed unit route, with no replacement of a unit step. Blueprint searches for 072C, finite cohomological, global sections, quasi-coherent and quasi-separated found no blueprint statement of this ordinary algebraic-space result. The same_as lists are empty.

## Not duplicates

lem-sfb-space-qcoh-cohomology-finite-bound vs lem-sfb-space-affine-chart-uniform-qcoh-vanishing: the existing node concerns one qcqs morphism and a bound uniform over all affine etale target charts, including a comparison to evaluation on an enlarged ringed site; it depends on the present item. The new node is the direct 072C bound on ordinary sheaves on one fixed qcqs space and provides an earlier geometric input.

lem-sfb-space-qcoh-cohomology-finite-bound vs lem-sfb-space-perfect-ext-window: the existing node bounds a window detecting Hom from a perfect derived object and cites this item; it does not state ordinary-sheaf cohomological dimension.

lem-sfb-space-qcoh-cohomology-finite-bound vs lem-sfb-space-global-sections-amplitude: the new node concerns only sheaves placed in degree zero, with ordinary abelian-sheaf cohomology. The item concerns all unbounded quasi-coherent complexes and both upper and lower bounds. Passing from the former to the latter needs the independent 08F7 unbounded reconstruction argument and 05TC, rather than relabelling either clause.

The 072C/tag search in the whole DAG returns exactly those three existing nodes. The scheme-only `lem-pc-unbounded-derived-functor-cohomological-bound` does not apply to a general algebraic space, and the existing `lem-sfb-space-product-preserving-derived-functor-upper-bound` is reused, not recreated.

## Review by Q33

I read Stacks `spaces-cohomology.tex`, Tag 072C, label `lemma-vanishing-quasi-separated`, including the atlas-data existence and alternating-spectral-sequence proof. Its fixed integers d and d_p depend only on the space and chosen atlas data, not on the quasi-coherent sheaf. Its last assertion gives vanishing for q >= max(d_p+p); enlarging that finite bound to C >= 1 proves exactly the new node's ordinary-sheaf statement. I also read the cited global module/abelian cohomology comparison 03FD in `sites-cohomology.tex`, including its separate global and objectwise formulas. The new node deliberately concerns global cohomology, not evaluation at a nonexistent final scheme chart.

I read 08F7 in `spaces-perfect.tex`, including the proof with lower-truncation reconstruction, preservation of derived inverse limits and eventual stabilization. I opened the existing product-preserving upper-bound node and read its statement and proof: it accepts algebraic spaces over an arbitrary scheme, a functor preserving countable products, and a cohomological bound only on quasi-coherent sheaves. It explicitly allows an unbounded-below input. Thus it supplies precisely the non-elementary passage required here without introducing a second copy of that lemma. I read 05TC(1) and its cofinal bounded-below representative argument in `derived.tex`; no bound above or finite geometric dimension occurs in it. I also checked the source's bounded-below injective-resolution existence and the 070J K-injectivity input.

For step 1 I read the statements of `def-pur-ringed-site-zeroth-hypercohomology`, `def-weil-sheaf-of-modules-category` and `def-sp-left-exact-additive`. They give the Hom description of global sections, sectionwise kernels and the criterion for left exactness. The step proves the hypotheses in a few lines: a kernel section family is exactly a section family killed by the map, and maps into a product are families of maps. Countable-product preservation follows directly from the product universal property; no assertion of exactness of products of sheaves is made. Additivity is the additive Hom functor. This is the only elementary step.

For step 2 I read every cited statement: the new 072C bound; `prop-pur-kinjective-resolutions-exist` (small-ringed-site modules are Grothendieck); `lem-weil-pbc-ring-modules-grothendieck-abelian` (applied to integer modules, namely Ab); `lem-sfb-ringed-site-global-module-abelian-cohomology` (the global comparison with no terminal object); and `lem-sp-kinjective-computes` clause (2) (ordinary injective resolutions compute the K-injective derived functor on M[0]). These are exactly the facts taken. The universe convention supplies a small skeleton, the structure sheaf is commutative, and C >= 1 guarantees that p >= C is a nonnegative degree where the comparison applies. No flatness of the structure sheaf over integers or injectivity after forgetting modules is assumed. The global comparison and the K-injective comparison identify R^p F(M) with the vanishing ordinary group in 072C.

For step 3 I checked each hypothesis against `lem-sfb-space-product-preserving-derived-functor-upper-bound`: same space, same module category, additive left exact F, countable products, uniform C >= 1, and quasi-coherent cohomology of E. Its conclusion is m >= t+C. With N=C-1 this is exactly m > t+N for integer m. N depends only on X. A spectral sequence with unjustified convergence for unbounded-below E is not used; that work belongs to the existing 08F7 node.

For step 4 I read `def-sbc-standard-tstructure-derived-category`, `lem-sc-bounded-below-injective-resolution` and `lem-weil-pbc-derived-functor-negative-vanishing`. The first explicitly equates cohomological lower boundedness with a bounded-below representative. The second gives a bounded-below resolution that is already K-injective. Consequently both the bounded-below and unbounded right derived functors use exactly the same complex F(I); there is no unproved identification between two different conventions. The third, applied to the two Grothendieck categories established in step 2, gives vanishing below t and makes no assumption above. It works for all lower-bounded E, so the quasi-coherence hypothesis is harmless here.

I checked B through E of delivery-errors against the written files. The only new node introduces all its objects, cites its notions, has no proof or proof dependencies, and is a genuine geometric input rather than a proof sketch in a statement. Every non-elementary input in the four steps is a cited statement. All twelve citations were checked as literal substrings in the current node statements. I checked the dependency closures of the reused general theorem and the comparison/resolution tools for a path back to this item; none exists. Generic homological-algebra tools outside the unit are explained in split_report.tool_uses; no accepted tool_uses field is written by this delivery. No SGA source is used.

I tested the new statement and assembly on X empty, M=0, affine schemes, a field spectrum and shifted sheaves. Taking C >= 1 handles empty or zero ordinary-cohomology cases without a maximum-over-an-empty-list issue. For an affine scheme C=1 and N=0 give the expected absence of extra upper shift. For M[r], cohomology is concentrated at -r before derivation and the upper output bound is -r+N, confirming the sign. Neither this check nor the proof invokes a Krull-dimension or Noetherian hypothesis. The upper implication permits a tail to minus infinity and the lower implication permits a tail to plus infinity. All steps are below 700 characters, so none crosses the 2000-character hidden-lemma review threshold.

The actual Mathlib searches are retained verbatim in searches.jsonl and the node records. Two semantic phrasings for the new node return scheme restriction/limit lemmas, quasi-coherence data and t-structure support declarations, not uniform space cohomology. Loogle returned zero results for the joint cohomology/quasi-compact query. The geometry grep returned zero results. A second global grep returns only universal-property/right-derived-Kan-extension text. I read the relevant Mathlib t-structure, quasi-coherent-sheaf and right-derived-functor source passages; none is an exact match or one-line specialization. No unavailable service is recorded as a negative search result.

## Unfinished work

No part of this one-level split remains unfinished. The new node is intentionally statement-only and enters the stage-1 queue for its own subsequent split. Server validation and direct delivery are performed after writing this report.
