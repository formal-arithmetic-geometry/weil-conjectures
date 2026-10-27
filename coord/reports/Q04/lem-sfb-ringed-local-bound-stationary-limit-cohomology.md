# Stage-1 delivery: lem-sfb-ringed-local-bound-stationary-limit-cohomology

Group Q04, direct-delivery worker, 2026-10-24. Only stage 1; no Lean written, no compiler or Lake invoked, and no repository or launcher file edited.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-local-bound-stationary-limit-cohomology.json`: item, now split into seven steps; statement unchanged; original provenance and searches retained, actual new searches appended.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-bounded-below-section-window-comparison.json`: statement-only unsplit lemma; no Mathlib match. A finite cohomology interval for one morphism gives isomorphisms on derived sections in a smaller interval. This is the sole new node, and there are zero new Mathlib leaves.
- `citations.json`: one verbatim statement quotation per cited node per proof step, twelve entries.
- `searches.jsonl`: search-command log, preserved. `write_split.py` is sandbox-only scratch generation code.

## Attachments

None. Searched the project library for the item's exact blueprint id and for stationary/eventually constant cohomology, local bounds, Roos limits and finite-window comparisons. Existing files for abelian-group Roos calculations, general finite cohomological dimension and degreewise term stabilization do not state the ringed-site theorem or the new weak-Serre finite-window comparison. No sorry declaration was treated as a finished proof.

## WANTED

None. All mathematical sources used are present in the read-only literature tree.

## Corrections and scope

The imported item had no proof and no proof dependencies. Its statement is correct against Stacks Tag 0D6T (sites-cohomology.tex, lemma-olsson-laszlo-modified), with the local-bound hypotheses written out from Tag 0D6R. I retained it verbatim. The stronger-looking canonical-map wording is valid: the proof gives the actual projections and then uses tail compatibility to reach every index n at least n_j. No uniform lower bound on the tower and no exactness of sheaf products are assumed.

I avoided applying the existing ringed-space stalk-injectivity theorem to a general site. Instead I expanded the covering argument of the site version, Tag 0D6L. I also avoided using only the existence of a natural Milnor short exact sequence to assert projection equations: the existing boundary-factorization and projection-factorization statements supply exactly the equations and exactness needed.

The new lemma is not a clause of the item. It contains no tower, no inverse limit, and no locally generating collection of covers. It compares a single morphism at one site object using a prescribed finite interval. The source's nontrivial instruction to compare spectral sequences is isolated here; the remaining proof performs the local injectivity and lifting arguments itself. It is not an identification of entire derived objects: a finite-range cohomology comparison cannot in general be replaced by an isomorphism of untruncated derived sections.

## Searches and blueprint

All Mathlib searches recorded for the new node were run through the required msearch.py command and read. LeanFinder was tried with two different descriptions (finite-window weak-Serre comparison and mapping-cone/acyclicity wording); Loogle searched `"rightDerived", "IsIso"`; LeanSearch searched bounded-below hypercohomology with a finite interval; grep searched cohomological dimension/hypercohomology and derived support/truncation comparisons. Hits give support, truncation, universal properties, or ordinary complex limits. They do not give the lemma under a bound restricted to the weak Serre subcategory. The item was independently searched with two stationary-derived-limit phrasings, LeanSearch, Loogle and grep. All services returned successfully. No unrun searches or unavailable services were represented as negative results.

I read Mathlib's HomologicalComplexLimitsEventuallyConstant.lean: its input is eventual constancy of complex TERMS and it concerns ordinary limits, which is different from eventual constancy of cohomology sheaves in an unbounded derived category. The derived-support/TStructure hits likewise do not compute the derived section groups in this claim.

Before creating the lemma I searched the whole DAG by tags 0D6T, 0D6K, 0BKV and 015J and by finite-window/hypercohomology/local-bound keywords, and ran blueprint_refs.py searches for `derived limit`, `sheafification cohomology`, `hypercohomology`, `finite window`, `015J`, `0D6T`, `stationary tower` and `finite cohomological`. The finite-window blueprint result is a Hom-from-constructible truncation statement, not this result. The existing generic hypercohomology node states the convergent spectral sequence, not the finite-window morphism comparison. Neither is an exact or one-line specialization match.

Read the chapter and inherited unit records, SETUP's three levels, and the current latest blueprint unit and its direct-images proof. This item remains a generic lower-level local-bound input to direct-image/descent arguments; no chapter or unit route is replaced. The item's inherited blueprint ancestor is null, and blueprint_refs.py ancestor also prints None. The new node inherits that same value and explicitly extends the item's via chain. Both have same_as = [], after the searches. The inherited place describes its existing ancestry and is retained.

## Not duplicates

lem-sfb-ringed-bounded-below-section-window-comparison vs lem-sfb-ringed-local-bound-stationary-limit-cohomology: the new lemma compares one bounded-below morphism over one object in finitely many degrees; the item concerns a tower with no uniform lower bound and the cohomology sheaves of its derived limit.

lem-sfb-ringed-bounded-below-section-window-comparison vs lem-sfb-ringed-unbounded-descent-criterion: the latter is an equivalence of unbounded weak-Serre derived categories under a ringed-topos morphism and five descent hypotheses; it does not state a finite-window comparison of derived sections.

lem-sfb-ringed-bounded-below-section-window-comparison vs lem-sfb-ringed-local-bound-direct-image-truncation: the latter is an unbounded direct-image preservation/truncation theorem with two ringed topoi; it does not give the new lemma for a single object and a bound only at that object. In particular it requires local bounds on both sites, absent from the new lemma.

lem-sfb-ringed-bounded-below-section-window-comparison vs det-finite-window-reduction: the latter compares Hom from a constructible sheaf into truncations in the specified coefficient categories; the new lemma compares actual hypercohomology maps of arbitrary bounded-below module-sheaf complexes on a general ringed site.

lem-sfb-ringed-bounded-below-section-window-comparison vs thm-sp-truncation-e2: the latter constructs and proves convergence of the generic hypercohomology spectral sequence; obtaining the new lemma still requires taking a cone, checking weak-Serre membership, establishing a strip of cone-cohomology vanishing, and applying the finite-filtration argument. It is an ingredient for splitting the new node, not the same statement.

## Review by Q04

I read the statement and entire proof of Tag 0D6T, including its two different local arguments, and the surrounding local-bound situation. For the new node I read its source paragraph in 0D6T and the bounded-below hypercohomology theorem in derived.tex, Tag 015J, lemma-two-ss-complex-functor. Here is an independent check of the extracted finite-window lemma: the cone C of f is bounded below, and its cohomology lies in S by the exact sequence with cokernel H^q(f) and kernel H^(q+1)(f), using exactly the weak-Serre closure in the statement. It vanishes for a-d-1 <= q <= b. Its convergent hypercohomology sequence has E2^(p,q)=H^p(U,H^q(C)), zero unless 0 <= p <= d. For any t in [a-1,b], all terms on p+q=t vanish because t-d <= q <= t lies in the zero interval. The abutment has a finite filtration, hence H^t(U,C)=0. The long exact sequence of derived sections gives precisely H^r(U,f) invertible for a <= r <= b. This proof is recorded here, not put into the statement-only new node. It also checks the off-by-one endpoints and the role of weak Serre closure.

For Step 1 I opened all four cited nodes. The K-injective-resolution theorem gives representatives even for the unbounded L and gives functorial resolutions; the exact-sheafification node states finite-limit and colimit preservation; the module-sheafification definition explicitly starts with abelian sheafification; the module-sheaf category definition explicitly computes kernels sectionwise and cokernels by sheafification. The kernel/image quotient is therefore a two-line elementary calculation from those inputs, rather than a new lemma. I read Tag 0BKV's same calculation and sites-modules.tex Tag 03CY. Naturality follows on these kernels and quotients, so it applies to the projection maps, not just to objectwise abstract isomorphisms.

For Step 2 I checked that the underlying-sets node applies to abelian presheaves on ANY site, and that the local-sections node explicitly gives both representatives and local equality/zero detection. Its size convention is satisfied by the item's universe condition. Refining a composite cover into the given cofinal system is allowed; I never assumed that an arbitrary intermediate refinement retains the local cohomological bound.

For Step 3 the only cited theorem is the new finite-window comparison. Each composite L_m -> L_N has cohomology isomorphisms on the entire finite interval because N is beyond all its finitely many thresholds. Setting a=j-1,b=j gives exactly the lower endpoint j-d-2 and upper endpoint j+1 in the source. The bound is on all members of every cofinal cover, with the same d_V. Replacing a negative d_V by max(0,d_V) only weakens the vanishing requirement. Each input is bounded below individually, which is all the lemma needs.

For Step 4 I read the whole statement of lem-kun-site-rgamma-derived-limit: it is a ringed-SITE theorem, applies to unbounded objects, preserves the specified product projections and produces a Roos triangle. The derived-limit definition provides the original triangle. Thus the map to the inverse limit is the actual compatible family of projections; no uniqueness of a homotopy-limit object is presumed.

For Step 5 I read all three cited statements. The eventual-isomorphism node concerns arbitrary abelian groups and gives zero R1 lim. The boundary-factorization node states exactness at H^j of the limit and identifies the map to the product; its left term is exactly that zero group. The projection-factorization node gives epimorphy for the map satisfying precisely our component equations. Consequently this specific map is bijective, and the ordinary inverse-limit projection to N is bijective by the explicit recursive tail construction. I read sites-cohomology.tex Tag 0D6K and more-algebra.tex Tag 07KY for the source computation.

Steps 6 and 7 use the established conclusions of Steps 1–5 and write out the remaining covering arguments, rather than citing an extra node for the item's injective or surjective clause. I verified the refinement order in Step 6: first represent the kernel class, next kill its image as a derived-section class, finally refine the composite cover into the cofinal collection where Step 5 applies. For Step 7 the image at the requested n is obtained by first lifting through H^j(L_N) -> H^j(L_n); naturality of the representatives and the original projection compatibility give the required image. The local lifts glue by the already-proved sectionwise injectivity. Thus both steps work on a site without enough points, and the final S-membership uses strict fullness only.

Edge cases checked: zero coefficient ring/S={0}; a=b in the new lemma; a complex supported in one degree; d=0 (exact-on-S section comparison); j negative; all zero complexes; a constant tower; and a tower of finite lower truncations whose lower bounds tend to minus infinity. The window is finite in each case and no common lower bound was used. A negative original bound causes no issue after taking its maximum with zero. Empty coverings force the relevant sheaf sections to vanish by the sheaf axiom, so the local proof also covers that case.

I checked B–E point by point: the new node is self-contained with inline weak-Serre and bounded-below meanings, introduces every object, carries no proof, has the correct tag/label and actual searches, is neither elementary nor a moved clause, and has no unlisted notion dependency. Every node citation has a verbatim quote in citations.json; all non-elementary external inputs are cited. No existing dependency closes a cycle through this item (the server check remains the final mechanical test). Each proof step is under 1000 characters, so there is no non-elementary step above the 2000-character review threshold. Generic off-unit tools are explained in split_report.tool_uses. No SGA source is used.

## Unfinished work

Nothing required for this one-level split remains. The new statement-only finite-window lemma is deliberately left unsplit for the queue. Required server dry run and direct push follow this report.

## Validation

The first dry run requested a longer quote for the eventually-isomorphic abelian-group tower lemma. Replaced that quote with its complete statement, including its hypotheses; the mathematical split was unchanged.
