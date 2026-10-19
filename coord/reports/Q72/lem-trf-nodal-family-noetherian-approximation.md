# Q72: lem-trf-nodal-family-noetherian-approximation

## Files written

- dag/nodes/sec-trace-formula/lem-trf-nodal-family-noetherian-approximation.json: item, statement unchanged, split into eight proof steps.
- dag/nodes/sec-trace-formula/lem-trf-complete-intersection-fibres-limit-descent.json: statement-only generic limit descent of flat locally finitely presented maps with local complete intersection geometric fibres; unsplit, no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-unramified-limit-descent.json: statement-only generic limit descent of locally finite type unramified maps; unsplit, no Mathlib match.
- citations.json: verbatim statement quotations for every citation in every item step.
- searches.jsonl: actual search-command records, retained with the earlier searches; no invented queries.

## Attachments

None. Searches for the item tag and nodal/approximation terminology in WeilConjectures of the read-only slopmaster2 source found no declaration establishing the whole statement without sorry. The new generic limit results likewise had no project declaration to attach.

## WANTED

None. All sources used are in the supplied literature.

## Corrections and route

The item's statement needed no correction. Its unsplit proof needed the actual argument behind the first paragraph of Stacks 0CBY: finite presentation alone does not make a descended family nodal. The eight steps expand the entire use of 0C5F into flat complete-intersection-fibre descent, pure dimension descent, and descent of unramifiedness of the Fitting singular scheme. Two independent generic inputs remain as new unsplit nodes. Neither restates the item or its nodal-family conclusion.

The inherited blueprint ancestor is lem-trf-local-term-locality through the existing nodal chart and alteration chain. The relevant historical input is its nearby-duality/alteration proof (1)--(2), where the nodal local equation is needed. The current sk-i-curve-zero unit follows contracting correspondences; this delivery elaborates the already-created historical input, not a replacement for that route. The item and both new nodes record the inherited ancestor chain and the precise approximation substep in from.place; same_as is empty after the whole-blueprint searches. Generic off-unit inputs are explained in split_report.tool_uses.

No Lean or build command was used. The exact upstream source is reference material, not evidence of a completed proof. No target statement or definition has been weakened.

## Not duplicates

lem-trf-complete-intersection-fibres-limit-descent vs lem-coef-left-cone-restriction-cocartesian: the existing node concerns restriction of functor quasicategories along a left cone and cocartesian edges; its 01UF is explicitly a Kerodon identifier. The new lemma concerns flat local-complete-intersection fibres and inverse limits of schemes, using Stacks 01UF for the syntomic fibre criterion. These identifiers name unrelated sources and assertions.

lem-trf-complete-intersection-fibres-limit-descent vs lem-trf-nodal-family-noetherian-approximation: the new lemma concerns arbitrary-dimensional maps between qcqs models and only flatness with local complete intersection fibres; it gives neither dimension one, the nodal condition, finite type integer models, affine neighbourhoods, nor retention of the singular point. The item's proof must separately descend dimension and singular-locus unramifiedness.

lem-trf-complete-intersection-fibres-limit-descent vs lem-trf-pure-relative-dimension-finite-stage: the existing lemma descends only pure fibre dimension and assumes no flatness or local complete intersection property. It cannot supply the new lemma, and is separately used in step 4.

lem-trf-unramified-limit-descent vs lem-galois-fpqc-descend-unramified: fpqc locality compares a morphism with a faithfully flat base change; the new lemma makes unramifiedness true at some finite stage of a directed inverse limit, whose limit projection need not be faithfully flat.

The whole-DAG and blueprint searches for 0C3L, 0C4W, syntomic descent, and unramified limit descent found no existing node asserting either new result. The Fitting, nodal curve, pure-dimension, approximation, and dimension facts are reused rather than duplicated. Mathlib searches for each new statement used LeanFinder, Loogle, source grep, LeanSearch, and a second semantic phrasing. The syntomic grep was empty; returned flatness/fpqc-descent and FormallyUnramified stability results do not assert finite-stage descent. Exact command records and responses are retained.

## Review by Q72

I read Stacks curves.tex Tag 0CBY, first proof first paragraph, and the complete proof of 0C5F, rather than treating their invocation as a proof. I also read the fibrewise nodal criterion 0C59 and its field-level input 0C4E. For the first new node I checked limits.tex 0C3L in situation-descent-property, together with the syntomic fibre criterion in morphisms.tex 01UF and the field-extension invariance of local complete intersections in algebra.tex. Its hypotheses include qcqs models, affine transitions, and a locally finitely presented initial morphism. Its flatness and geometric local-complete-intersection formulation is the fibre criterion for syntomicity; eventual persistence follows by base change. For the second new node I read limits.tex 0C4W in the same situation: it requires local finite type, not finite presentation, of the initial morphism. This distinction matters for the closed Fitting singular subscheme.

For step 1 I opened the affine basis, open factorisation, flatness and local-finite-presentation definitions, locally algebraic dimension, and smooth-open-restriction nodes. They provide the chosen neighbourhoods, the restricted morphism, the local properties, dimension preservation on component opens, and implication (b) that smoothness after restriction would imply original smoothness at x. Completed local rings are unchanged upon taking an open neighbourhood.

For step 2 I read the affine integer inverse-system node, the object clause of spreading out, qcqs-morphism permanence, and schemes-over-limits. They supply exactly the finite-type integer bases, the finitely presented model, qcqs source models and persistence under base change, and the limit on directed tails. Finite generation over the integers follows by composing the finite sets of algebra generators on a finite collection of charts.

For step 3 the existing nodal-curve criterion explicitly has both the local-complete-intersection and unramified-singular-scheme conclusions. I use only its (1) to (2) implication to obtain local complete intersection geometric fibres. Pure dimension one is an item hypothesis retained in step 1, and the fibres are locally of finite type by the finite-presentation base-change clause. Thus all hypotheses of the new complete-intersection-fibre descent node are available; no nodal condition is being assumed at an intermediate finite stage.

For step 4 I checked that the equidimensional-open node supplies purity to local dimension, the irreducible locally algebraic node supplies equality at generic points and invariance on opens, and the finite-type affine-components node supplies the finiteness needed to remove other components. Conversely, isolating a component at its generic point identifies its dimension with that local dimension. The fibre-dimension base-change node gives precisely equality of corresponding local dimensions. Surjective base change of the field-spectrum map gives a lift of every point. These statements justify passing both ways between ordinary and geometric purity before and after applying the existing pure-relative-dimension finite-stage node. Its qcqs, affine-transition, local-finite-presentation and dimension-one hypotheses have been checked in step 2.

For step 5 I checked all four cited statements. The definition gives the first-Fitting singular subscheme; affine fibre products give the tensor-product algebra; the differential node gives the differential module base-change isomorphism; and clause (2) of Fitting-ideal independence/base-change gives exactly the ideal equality. Their combination proves formation of this closed subscheme commutes with base change even before the finite-stage map is known nodal. I corrected the possible circular shortcut of using the nodal-family singular-scheme theorem at that stage.

For step 6 I read the finite-type-over-Noetherian and nodal-family singular-scheme nodes and the new unramified descent statement. The former makes the integer finite-type schemes Noetherian, hence qcqs; finite-type quotient charts show the singular scheme is locally finite type over the stage base. The nodal-family node is used only for h, whose nodal hypothesis is already known, and gives the unramified limit morphism. The general base-change equality established in step 5 identifies this limit. Thus 0C4W applies without an unjustified finite-presentation assumption on an arbitrary closed subscheme.

For step 7 I opened unramified base change, the reverse nodal-curve criterion, the d-th Fitting smooth-locus theorem, and the discreteness of an unramified field scheme. They give unramifiedness of the geometric-fibre singular scheme, nodality at closed points, equality of its support with the nonsmooth locus (flatness, finite presentation, and geometric purity having been established), and closedness of every singular point. Closedness in the closed singular subscheme implies closedness in the fibre, so the closed-point criterion covers every nonsmooth point. The algebraically closed base field then makes the completed ring exactly the one in the item.

For step 8 I use the nodal-family singular-scheme node only after step 7 establishes its full nodality hypothesis at the selected stage. Its base-change clause identifies the nonsmooth loci and retains the image x0 as nonsmooth. The fibre-product identifications and finite-type/flat/finitely-presented conditions were already obtained, so no extra existence assertion is hidden here.

I tested empty fibres and constant inverse systems: the first new statement permits empty fibres via an empty affine cover, and the descent assertions agree with the constant-stage case. A cusp is a local complete intersection curve, so step 3 alone would not prove the item; step 6 and the unramified singular-scheme criterion are essential. A nonflat model is allowed initially, but eventual flatness is supplied by 0C3L, not assumed. The singular closed subscheme is not presumed finitely presented over a non-Noetherian ring. All eight proof steps are below 2000 characters; the only auxiliary comparisons are written explicitly from the cited generic statements, rather than hidden as standard lemmas. Every cited node statement was read and every citation quote is copied verbatim into citations.json. I checked the delivery-error categories B--E against these files, including noncircular citations, smallness/directedness, complete hypotheses, no clause restated as a new node, and use of source tags without SGA.

## Unfinished work

The two new nodes are intentionally statement-only and join the stage-1 queue. The item has a complete one-level split; there is no unresolved statement dispute.
