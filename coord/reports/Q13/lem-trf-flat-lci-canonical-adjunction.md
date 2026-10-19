# Stage 1 delivery: lem-trf-flat-lci-canonical-adjunction

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-flat-lci-canonical-adjunction.json`: item, split into nine steps; statement and complete blueprint ancestry retained.
- `dag/nodes/sec-trace-formula/lem-trf-lci-cotangent-presentation.json`: statement, unsplit; no Mathlib match. Intrinsic cotangent-complex models, Tor-independent base change, smooth specialization.
- `dag/nodes/sec-trace-formula/lem-trf-two-term-perfect-determinant.json`: statement, unsplit; no Mathlib match. Determinant functor on two-term perfect complexes, including evaluation on a contractible model and coherent pullback.
- `dag/nodes/sec-trace-formula/lem-trf-relative-duality-polynomial-chart.json`: statement, unsplit; no Mathlib match. General coherent relative duality in polynomial charts, with the top-differential normalization and polynomial-refinement comparisons.

The sandbox also contains `citations.json` (22 entries, a verbatim statement for every step/node pair) and the actual `msearch.py` log `searches.jsonl`. Temporary preparation code is not part of the delivery.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and the adjunction, cotangent, determinant, Koszul and dualizing notions found no complete project declaration stating the item. Searches of the read-only upstream master were treated only as reference material. Its unrelated etale/coefficient dualizing constructions are not coherent O-module relative duality. No Lean was written or compiled.

## WANTED

None. All sources used are in `literature/stacks-project/`.

## What was wrong or corrected

The imported item had an empty proof. Its statement is unchanged: no hypotheses were added and no base change or nonseparated case was discarded. The earlier sandbox attempt had three inadequate supporting nodes. In particular it treated the smooth locus as an open in affine space, compared pushforwards into different ambient schemes, and invoked poorly specified transition/base-change assertions. Those draft nodes are removed from this delivery. The new proof takes the intrinsic determinant as the global object, compares line bundles on the source, and handles smoothness through the cotangent quasi-isomorphism. The supporting relative-duality statement defines both the diagonal map and the condition it induces, and is used only on separated opens over a locally Noetherian base.

The initial dry run found search records without corresponding entries in the item's log. The cause was passing a new node's id as the second argument of msearch.py. The corrected searches were actually run with the assigned item's id, the hits were read, and the new nodes' records are now generated from those log entries. Preliminary grep searches had an extra `Mathlib` path component and returned no hits; they were repeated with the correct relative path (or no subdirectory). The final records use the corrected searches, including the actual cotangent hits. The corrected item grep finds only GammaSpecAdjunction.lean:97, the English phrase canonical (bundled), which is unrelated to a canonical bundle. The final source-level audit added explicit citations for ambient localization flatness and the affine flatness criterion, rather than assuming that the definition of a flat morphism directly states an assertion about affine coordinate rings. A server check also caught a nonexistent definition id for separatedness; it is now `def-weil-proper-morphism`, whose statement explicitly defines separatedness by the diagonal being closed.

## What remains unfinished

The item is split at stage 1. The three new foundational lemmas are deliberately statement-only, unsplit nodes for subsequent work, not claimed proofs or Mathlib leaves. No stage 2 or stage 3 work was done.

## Not duplicates

No existing node has the source tags of these three new nodes. I searched the entire DAG both by tags (08T2, 08T3, 08SJ, 08SL, 08QQ, 08R5; 0FJX, 0FJY, 0FJI, 0FJM; 0E2T, 0E2X, 0E9W, 0BV2, 0BZI, 0BZJ) and by notions, and searched the whole imported blueprint with blueprint_refs.py for cotangent, relative dualizing and determinant. The blueprint's relative-dualizing entries concern etale coefficients, and its determinant entries concern Weil representations, neither of which is the O-module statement here.

lem-trf-lci-cotangent-presentation vs lem-weil-pbc-complete-intersection-fraction-field-cotangent-model: the existing node concerns a particular naive cotangent model over a fraction field; it does not state the intrinsic derived cotangent complex on arbitrary schemes, its Tor-independent comparison or its smooth specialization.

lem-trf-two-term-perfect-determinant vs def-mg-determinant-line: the existing definition is a rank-one Weil representation attached to a lisse sheaf, not a determinant functor on quasi-isomorphism classes of perfect O-module complexes.

lem-trf-relative-duality-polynomial-chart vs lem-sc-smooth-proper-relative-dualizing-general: the existing result requires smoothness and properness and identifies its dualizing object with top differentials. The new result is general flat coherent relative duality on separated locally finite presentation charts; it assumes neither smoothness nor properness and asserts neither an invertible cohomology sheaf nor concentration in one degree.

lem-trf-relative-duality-polynomial-chart vs lem-sc-koszul-regular-immersion-derived-hom: the existing node computes RHom for one Koszul immersion with structure-sheaf coefficients. It does not identify that object as relative dualizing over the base or compare polynomial ambient presentations. Conversely the new generic relative-duality input does not compute Koszul cohomology; step 4 does that with existing nodes.

None of the three new statements is the line-bundle conclusion moved into a child node. The cotangent input produces a complex, with no determinant or duality conclusion. The determinant input concerns arbitrary perfect complexes and no morphism's dualizing complex. The general relative-duality input concerns arbitrary flat morphisms, whose dualizing objects need not be shifted invertible modules. The item's rank-one computation, degree n-c, determinant transitions, their agreement with duality comparisons, and arbitrary-base-change construction are arguments in the item's steps.

## Review by Q13

I read duality.tex Tag 0B6V (lemma-lci-shriek) and Tag 0E2Y (lemma-base-change-relative-dualizing), the sources named by the imported item. Tag 0B6V is an invertible-object assertion using local Koszul adjunction; it alone is not a theorem about canonical conormal transition maps. Tag 0E2Y permits arbitrary schemes as new bases, so imposing a Noetherian new base would have weakened the item. The proof here establishes arbitrary base change by the cotangent determinant instead. This is within the local complete-intersection adjunction input of the marked-dualizing construction in the stated blueprint ancestry; it does not change the curve-reduction route.

For the cotangent input I read cotangent.tex Tags 08T2, 08T3, 08SJ, 08SL (including the displayed naive conormal model and its proof), 08QQ, and 08R5. The model needs a Koszul-regular ideal and an ambient smooth polynomial chart; a mere presentation by arbitrary equations would not suffice. The base-change hypothesis is precisely derived Tor independence, not that the map of bases is flat. The smooth conclusion is a quasi-isomorphism to differentials, not an open-affine-space assertion. The statement defines its cotangent and Tor-amplitude terminology inline and cites the existing scheme, derived-category, Koszul, differential and module definitions.

For the determinant input I read perfect.tex Tags 0FJX and 0FJY, and more-algebra.tex Tags 0FJI and 0FJM. These are the proved two-term version of the determinant construction; I did not use the preceding discussion of general perfect complexes which says it will be added later. The source applies to any scheme, without separation or Noetherian hypotheses. Its affine formula is Hom(det E^-1,det E^0), agreeing with the dual-then-tensor order in the item. The contractible identity differential gives evaluation, and affine pullback gives the coherent comparison for arbitrary g.

For the relative-duality input I read duality.tex Tags 0E2T (the full pair and diagonal condition), 0E2X (existence), 0E9W (agreement with coherent upper shriek for flat separated finite-type morphisms), and 0BV2 (local polynomial calculation), together with dualizing.tex Tags 0BZI and 0BZJ and their top-differential footnote and one-variable comparison. The local formula with P[n] alone is explicitly noncanonical; the statement uses Omega^n[n] and records the contraction normalization needed for the comparisons. Local finite presentation over a locally Noetherian base puts each affine restriction in the finite-type Noetherian setting used in those calculations. The pair condition is stated using the closed diagonal, which is why this input is not applied to all of the possibly nonseparated W. It contains no lci or purity-of-dimension assumption and makes no claim of one-degree concentration before the item's Koszul argument.

I checked every step against the complete statements of its cited nodes:

1. The regular-to-Koszul node actually states Koszul exactness for a regular sequence, and the conormal node supplies the specified basis of I/I^2, not only finite generation. The coordinate-differential basis and rank-one exterior calculation are written out. The lengths are c=n-d on each chart; no common codimension is imposed on different ambient dimensions.
2. The cotangent input gives the intrinsic derived object and the exact two-term model used; the determinant input supplies a genuine invertible module on W. Both apply without a separatedness hypothesis. This establishes the alpha_i on the source scheme, not an ill-typed comparison of pushforwards to different ambient schemes.
3. The identity and triple-overlap identities are the displayed cancellation of alpha maps. This is the sole elementary step. No assertion that intersections of affine charts are affine is used.
4. I opened lem-sc-derived-hom-finite-free-model, lem-sc-koszul-regular-sequence-dual-complex and lem-sc-derived-internal-hom-restrict-open. The first permits the bounded finite free Koszul model; the second states concentration in degree c, the induced quotient-module structure, localization compatibility and independence of the generators. The third justifies restriction. Twisting by the ambient invertible module is justified term by term by finite bases and exactness of rank-one free tensoring, not by an uncited derived projection formula. The dual top exterior-power identification is the basis evaluation pairing. This proves both the sheaf Ext clause and the shifted local model.
5. The general duality theorem is used with the flat, separated open chart and its locally finitely presented structure morphism over the original Noetherian base. Its local model and the preceding calculation give Ki[n-c]. I explicitly do not infer a global isomorphism just from local isomorphisms in a derived category.
6. The comparison clause of the general duality input specifies polynomial refinements and their normalization; the Koszul theorem supplies independence of regular generators. For a new coordinate the graph equation t-a contributes a contractible rank-one conormal complex, with the same contraction/evaluation on the determinant and duality sides. The combined-coordinate presentation compares two different ambient dimensions. Ordered tensor signs are those of the Koszul comparison, not an ungraded permutation convention. This identifies the transition maps, and hence the local identifications glue at the line-sheaf level before shifting.
7. I also opened lem-pc-affine-flat-module-localization-preserves-flatness, lem-weil-pbc-localization-away-polynomial-quotient and lem-weil-pbc-flat-morphism-affine-criterion. They justify ambient flatness after localization, its explicit finite presentation by hz-1, and passage from stalkwise flatness of p to flatness of the affine quotient algebra; polynomial flatness itself is the written monomial-basis tensor argument. I opened lem-pur-relative-regular-equations-base-change: it assumes the ambient algebra is flat and finitely presented and its regular-sequence quotient is flat; these are exactly the ambient principal polynomial chart, the given equations, and the flatness of p. Its conclusion is regularity in each relevant local ring even for arbitrary R'. I use that exact conclusion, not a stronger unquoted neighbourhood assertion. Regular-to-Koszul at these stalks, and contraction off the common zero locus, establish exactness of the pulled-back Koszul complex. The conormal basis comparison is stalkwise. This suffices for the Koszul adjunction construction on the new base, and invokes no Noetherian theorem there.
8. The affine flatness hypothesis makes the derived tensor of B with R' ordinary tensor. The cotangent base-change map is therefore invertible. The determinant comparison is natural and compatible with composition, as stated by its node. Locally it sends the pulled-back conormal/differential bases to their new bases, so this is the required adjunction base-change map, not an unspecified isomorphism between two lines.
9. The smooth cotangent specialization comes from its node. I opened lem-sc-smooth-omega-finite-locally-free and checked its relative-dimension hypothesis: on the smooth locus the pure geometric fibre dimension is d. Its conclusion is rank d. Taking the determinant of the degree-zero complex yields the requested canonical top forms.

For B1–B7 each new node has an empty proof and dependency list for proofs, a self-contained mathematical statement, actual local sources with checked tag/label pairs, and no proof disguised inside its statement. Existing definitions are cited for their own meanings; perfect, Tor amplitude, cotangent complex, relative dualizing pair, pseudo-coherence and the normalization are specified inline. For C1–C6 I checked the full statements rather than their proofs, recorded every proof citation verbatim in citations.json, reused the existing Koszul and regular-base-change facts, and checked the dependency directions. The off-unit generic tools are declared in split_report.tool_uses: they supply foundational algebra or sheaf facts, without replacing any step of the curve unit's route. The whole-DAG and whole-blueprint searches described above found no duplicate of the three new facts.

I tested the formulas when c=0 (the identity closed immersion, with wedge^0 C=O), when d=0, and on empty opens. For a hypersurface R[x]/(x^2) the conormal complex has differential 2x; the proof does not incorrectly replace it by Omega[0] on the singular locus. Adjoining t-a gives ranks c+1,n+1 and leaves d and the determinant unchanged. A nonflat base change of a flat hypersurface, k[t] to k with equation xy-t, gives xy and the same conormal generator, illustrating why the argument needs arbitrary base change rather than flat base change alone. Without the flat-quotient hypothesis the claimed preservation would fail: Z/(p) over Z followed by Z to F_p sends the equation p to zero. A non-Noetherian new base causes no problem for the cited stalk theorem or for determinant pullback. Finally every non-elementary step is below 2000 characters; the comparison argument is explicit and uses the stated generic polynomial-refinement comparison rather than hiding a separate line-adjunction theorem.

## Route-pivot audit and repair comparison

I read the complete current `coord/route-pivot-dropped.txt` snapshot (1,351 node
ids, beginning with `def-cbc-bounded-representable-hypercover` and ending with
`lem-pur-system-section-suspension`). The list is the human's 2026-10-18
decision dropping the infinity/dg/model-category machinery and the two Zariski
gluing branch nodes. I compared every id in that list with the item and all
three child records, including each `stmt_deps`, `proof_deps`, blueprint `via`
chain, and explicit split-report references. There is no intersection: the
item uses only ordinary scheme, cotangent, determinant, Koszul, Ext, and
relative-duality statements, and none of those records imports a dropped
module.

I searched the available `coord/repair-notes/` snapshot for the item and each
child id and found no item-specific route-pivot repair note. The applicable
repair instruction is the F1 entry for this item in `coord/returns/Q13.md`:
record the dropped-list check, the absence of an applicable note, and the
historical comparison. No route-pivot machinery is therefore removed from
the proof, and no replacement route is needed.

For the historical comparison, I used the returned delivery recorded at branch
head `8b638c5528` in `coord/returns/Q13.md` and its retained report. That
delivery already had the same nine proof steps, three statement-only children,
statement, sources, blueprint ancestry, and Mathlib search questions; it did
not document the route-pivot artifacts. The current sandbox retains those
node contents and adds this explicit audit to the report. The shared snapshot
still shows the maintainer's unsplit baseline, while this sandbox is the
repaired split; no node statement or proof was changed for this report-only
repair.
