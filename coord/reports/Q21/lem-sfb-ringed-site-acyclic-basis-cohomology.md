# Stage-1 delivery: lem-sfb-ringed-site-acyclic-basis-cohomology

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-acyclic-basis-cohomology.json — statement, split into nine proof steps; no Mathlib match.
- citations.json — verbatim statement excerpts for all 15 step/node citations.
- report.md — this report.

No new nodes; no Mathlib leaves. The sandbox also contains the recorded searches and the item-specific writing script. Nothing was written to the shared repository or launcher, and no Lean, compiler, Lake or build command was run.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and for acyclic basis, acyclicBasis, AcyclicBasis, hypercohomology and related truncation terms found no declaration stating this arbitrary-ringed-site unbounded result. Ordinary sheaf cohomology and injective-acyclicity declarations cover different assertions.

## Wanted literature

None.

## Findings and changes

The statement is unchanged and agrees with sites-cohomology.tex Tag 0BKZ, lemma-cohomology-over-U-trivial. It includes the canonical linear, natural and degree-zero-normalized comparisons determined by that proof. I read its use in spaces-perfect.tex Tag 071Q, lemma-derived-quasi-coherent-small-etale-site. The existing statement-only item had no proof or proof dependencies. I supplied its proof directly, without moving its conclusion into new nodes.

The previous split of lem-kun-0bkz is useful material, but that statement is for a scheme's small etale site and abelian coefficients. It does not imply this arbitrary ringed-site module statement. Its two supporting site-limit nodes really are stated for arbitrary small ringed sites and module complexes. Those nodes, together with existing general spectral-sequence and group-limit nodes, give the required proof. No specialized constant-coefficient theorem is substituted for a ringed-site assertion.

The source proof begins with reconstruction under a local cohomological bound and then uses the bounded-below spectral sequence on lower truncations. I retained that route. The eventually constant inverse-limit calculation is written out in the item's proof; it is elementary once the existing Roos formula is cited. No unconditional left completeness of a sheaf derived category or unbounded spectral-sequence convergence is assumed.

The latest blueprint's chapter, unit statement and direct-images proof (3) were read under literature/blueprint/latest. This item is a supporting 071Q prerequisite in its inherited direct-image ancestry, not the key node of the unit. Its inherited blueprint.from.node is null, exactly as blueprint_refs.py ancestor reports. I retained its precise inherited from.place and via list and confirmed same_as=[] for this general ringed-site assertion. No chapter or unit record was changed.

## Searches and reuse

The sandbox initially contained no item or previous split. I read the existing item searches and ran fresh msearch queries under Q21, recorded in searches.jsonl and appended to mathlib_searches. All four tools returned successfully. The first semantic search found ordinary Sheaf.H, cohomologyPresheaf and K-injective definitions. The second phrasing found generic derived localizations, the derived quotient, K-injective morphism comparison and ordinary rightDerived. None states the unbounded acyclic-basis theorem or specializes to it in one line. Loogle found no declaration for the quoted SheafOfModules/homology pattern. The grep found ordinary abelian sheaf cohomology. I opened Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean and Mathlib/Algebra/Category/ModuleCat/Sheaf.lean to confirm these are definitions/infrastructure, not the item.

Before deciding that no new node was needed, I searched the whole DAG by 0BKZ, acyclic basis, cohomology-over-U-trivial, sheafification/cohomology, the site-limit statements and their ids, and ran blueprint_refs.py searches for 0BKZ, acyclic basis, cohomology-over-U and acyclic. The one blueprint theorem matching 0BKZ is the specialized lem-kun-0bkz noted above. The existing general limit nodes were reused rather than duplicated.

## Not duplicates

No new nodes were created. lem-kun-0bkz is only a scheme/small-etale abelian specialization; lem-kun-site-truncation-derived-limit reconstructs a complex from its lower truncations under a cohomological bound; lem-kun-site-rgamma-derived-limit preserves already given derived-limit triangles. Neither latter statement supplies the item's acyclic-basis edge isomorphism by itself.

## Review by Q21

I read the complete statement and proof of Stacks 0BKZ in sites-cohomology.tex, its reconstruction input 0D6P (lemma-is-limit-dimension), its evaluation input 0D6K (lemma-RGamma-commutes-with-Rlim), and the displayed exact sequence 0BKX (equation-ses-Rlim-over-U). I also read derived.tex 015J (lemma-two-ss-complex-functor) and its functoriality remark, and more-algebra.tex 07KW (lemma-compute-Rlim), as well as the affine-etale-basis application in spaces-perfect.tex 071Q. There are no new-node sources to audit. I opened the statement of every cited DAG node; citations.json copies exactly what those statements provide.

Step 1 uses the module category definition for sectionwise kernels and module-valued morphisms, the K-injective existence proposition for both Grothendieck categories and functorial degreewise injective replacements, the K-injective Hom/derived comparison to evaluate derived morphisms, and lem-sp-kinjective-computes for agreement with bounded-below right derived functors. The target category is realized as sheaves on a one-object site with coefficient ring O(U); therefore the cited Grothendieck theorem applies without a constant-ring hypothesis on the original site. Forgetting the action changes neither the evaluated complex nor its group cohomology, matching the exact statements of the limit lemmas.

Step 2 cites good truncation for the lower bound and retained cohomology, and thm-sp-truncation-e2 for its E2 page and finite convergent filtration. Both categories and left exactness were checked in step 1. The vanishing in the item transfers to the right derived functors via that step, including the zero cohomology sheaves below the truncation. Step 3 uses the same spectral-sequence theorem's explicit finite filtration and abutment: all nonzero-column pieces vanish, F0 is everything and the finite zero end forces F1=0. The differential endpoints and functoriality of induced kernels, images and quotients are written out. Linearity is checked in the module-valued category rather than inferred from a merely additive group isomorphism.

Step 4 uses precisely the statement of lem-kun-site-truncation-derived-limit: it permits the arbitrary ringed site, requires a covering subset, and needs vanishing only for q<0 and p>d. Our hypotheses imply these with d=0. Its conclusion includes the product triangle and the specified canonical projections; I did not take extra data from its proof. Step 5 uses precisely lem-kun-site-rgamma-derived-limit's projection-compatible triangle, then the natural Milnor sequence in D(Ab). The latter has no scheme or finiteness assumptions. Its right map is the map induced by those same projections, which is needed to identify the final comparison rather than just its source and target groups.

Step 6 uses good truncation for both degrees r-1 and r, with a common threshold N>=max(0,1-r), and the Roos statement for the kernel/cokernel formula. The explicit forward/backward solution proves surjectivity of 1-s even when initial transition maps are not invertible. The kernel is identified by an actual tail projection, so the comparison is canonical and compatible with the maps used in step 5. Steps 7-9 are elementary assembly. Step 7 defines the final map by a tail projection and its module-linear bounded edge, proves independence of N using the actual transition equality, and obtains a linear inverse from bijectivity. Step 8 proves the two naturality squares separately: truncation naturality for a derived morphism represented between K-injectives, and termwise semilinear restriction on one fixed module K-injective representative for V->U. Each commutes with the exact-couple maps and with c_N, so their composites commute. No injectivity of an underlying abelian sheaf or exactness of restriction of sections is used. Step 9 computes the degree-zero edge from the kernel of an injective resolution and verifies it is the identity under the augmentation identification. Its K-injective citation states the agreement with this injective-resolution computation.

I checked delivery-errors B1-B10: no unsplit new nodes, self-contained unchanged statement, definitions correctly cited, valid single-escaped TeX, labels/tags read in the actual sources, no invented Mathlib leaf or search, and completed blueprint duplicate/attachment searches. C1-C8: every non-elementary ingredient is a cited statement, all quotes were read, no proof-internal datum is borrowed, dependency closures do not reach the item, and all generic off-unit tools are declared in split_report.tool_uses. D1-D5: no relabelled conclusion or hidden new theorem; the steps retain the source argument and the finite-tail computation. E1-E7: all bounds and object categories were checked; no source or statement correction was needed. Every step is shorter than 2000 characters. In particular, the naturality step only tracks the already constructed truncation maps and induced quotient maps, not a separate unproved comparison theorem.

Edge cases: on the terminal ringed site with ring A, evaluation is the identity and the result is H^r(K)=H^r(K); this also tests an unbounded complex. For K=M[-r], the retained cohomology and threshold give the expected M(U) in degree r, provided M is acyclic on the basis. K=0 gives zero groups and the unique maps. The zero coefficient ring gives the zero category. A sheaf in degree zero gives the identity, explicitly checked in step 9. A site whose objects are all empty-covered has only zero module sheaves, so an empty covering basis causes no contradiction. Restriction changes O(U) to O(V), so its maps are semilinear, as the statement requires.

## Unfinished work

None for the one-level stage-1 split. Existing prerequisite nodes retain their own proof status and were not changed. Delivery awaits the required server dry run and push.
