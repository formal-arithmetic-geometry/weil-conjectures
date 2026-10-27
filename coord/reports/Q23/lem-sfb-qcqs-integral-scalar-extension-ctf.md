## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-integral-scalar-extension-ctf.json`: statement unchanged; seven-step proof, existing dependencies, blueprint reference and actual Q23 searches filled. Mathlib verdict: no match for this coefficient/constructibility assertion.
- `citations.json`: one verbatim statement quotation for every use in every proof step.

Attachments: none. A search of `lean/WeilConjectures/` for the exact blueprint id and integral/rational scalar-extension notions found no completed declaration giving every clause under arbitrary qcqs hypotheses. The finite-coefficient constructibility theorem in `SixFunctors/ProEtale/FiniteCoefficient/Derived/ExtendScalars/Constructible.lean` is about discrete rings on finite-type schemes over a field, so cannot attach this item. No Lean was written or compiled.

WANTED: none.

The item was unsplit with an empty proof. Its statement is retained verbatim: it concerns ordinary finite scalar models and ordinary uncompleted derived categories, not Hemo--Richarz--Scholbach's derived-dualizable constructibility. Their Theorem 7.7 is context only. I read Theorem 7.7, section 7.2, and Lemma 7.9 in the supplied PDF, and Bhatt--Scholze Lemma 6.8.2 and Definition 6.8.3. The finite-field localization assertion of Lemma 6.8.2 is the relevant coefficient input. No claim here identifies arbitrary norm-continuous algebraic-closure coefficients with finite-subextension-valued coefficients.

Nothing remains unfinished in this split. Downstream proofs of already-existing dependencies remain their own DAG tasks.

## New nodes

None: all sixteen distinct dependencies already exist. In particular the initially suspected missing coefficient-flatness lemma is `lem-weil-pbc-continuous-integral-scalar-exact`, not a new node. The generic internal/section derived scalar comparison, K-flat single-factor tensor comparison and change-of-rings cancellation also already have nodes.

## Blueprint and duplicate searches

Read `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-prop-sf-comp-coherence.json`, the main-20261015 refinement proof, and `det-sf-comp-coherence-cocycle`. Ran `blueprint_refs.py ancestor` on the item and whole-blueprint searches for `scalar extension flat`, `localization`, `Tor amplitude`, `integral scalar` and `finite constant`. Read the finite-model definition and the existing localization, scalar flatness, exact-functor, internal/section and K-flat nodes returned by whole-DAG keyword/id searches. The item supplies the integral-to-rational D_ctf input to refinement proof (2)'s closed-complement generator devissage; the compactification coherence route does not change.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. Existing generic statements are cited directly, including their full hypotheses; no elementary tensor identity or clause of the item has been renamed as a node.

## Mathlib searches

The original search history is preserved. The five Q23 searches actually run are recorded verbatim in the node and in `searches.jsonl`: LeanFinder queried both flat condensed rational extension with Tor amplitude and localization of DVR module sheaves with finite constant models; Loogle queried `"SheafOfModules", "Flat"`; grep queried `constructible.*Tor|scalar.*extension.*constructible|constructible.*scalar.*extension`; LeanSearch queried flat change of rings for sheaves preserving Tor intervals and finite constant models. All services answered. I inspected the returned signatures. The hits are ordinary module flatness/base change, derived cohomological bounds, solid/LightCondMod infrastructure, Tilde local fractions, or finite sheaf generators. None supplies this theorem. No unavailable service was recorded as a negative result, and no new search was inferred or fabricated.

## Review by Q23

I checked the item against its supplied Hemo--Richarz--Scholbach source and its expressly agent-written finite-model qualification. The proof does not invoke Theorem 7.7 as if its derived-lisse objects were defined by this DAG's finite constant models. I read the full statements of all sixteen cited nodes. I also opened Stacks `sites-cohomology.tex` lemma-K-flat-resolution (06YS) and the construction of derived tensor (06YU), `sites-modules.tex` lemma-flat-change-of-rings (05V4), `derived.tex` lemma-right-derived-exact-functor (015F), and `homology.tex` lemma-exact-functor (010N). There are no new-node statements or sources to audit.

Step 1 uses exactly the finite-limit preservation asserted by `lem-weil-pbc-continuous-integral-scalar-exact` for the actual continuous O_F inclusion, and by `lem-sfb-qlbar-flat` for the finite-subextension-valued algebraic closure. The latter allows every scheme and every finite field F. `sk-def-sfb-change-of-scalars` supplies the left adjoints/right exactness. I wrote the balanced-tensor isomorphism for their composite rather than treating transitivity as an extra theorem. F=E in the finite case is used explicitly; no Noetherianity or invertibility hypothesis is added.

Step 2 uses `lem-weil-pbc-exact-functor-derived-factorization`, whose statement includes unbounded complexes and triangulatedness, and `lem-weil-pbc-exact-functor-complex-cohomology`, whose statement includes the natural kernel/image comparison. `sk-def-sfb-derived-extension-of-scalars` supplies the K-flat computation, so exactness identifies that particular derived functor with termwise extension. The cohomology comparison descends through quasi-isomorphisms; it is not merely a collection of unrelated per-degree isomorphisms between derived objects.

Step 3 cites `lem-sfb-internal-section-scalar-adjunction` for actual ordinary and unbounded derived extension/restriction, and `lem-pd-section-kflat-tensor-comparison` for the actual relative derived tensor. The definition-only module equivalence would not by itself supply these tensor comparisons, so it is not used as a substitute. Their smallness/universe hypotheses are exactly the item's convention. The section calculation is therefore a calculation of the specified internal tensor.

Step 4 uses the finite-model and stratification clauses of `sk-def-sfb-constructible`, the exact inverse-image and coefficient identifications of `sk-prop-sfb-cartesian-coefficients`, and the actual ringed module pullback tensor isomorphism of `lem-weil-pbc-ringed-topoi-module-pullback-tensor`. That last lemma applies to general ringed topoi, including identity-topos coefficient change and the locally closed restriction. I wrote the balanced-generator maps for the two paths. I did not mistake a locally closed stratum for an object of the small pro-etale site or assume intersections of affine opens are affine.

Step 5 is elementary finite-matrix algebra after the cited vector-space basis leaf and the definition of finite constant models. The tensor of a finite scalar presentation is a finite matrix over k=E or Omega; Gaussian elimination gives a finite free cokernel. Reassociating the tensor and applying this finite basis yields the displayed B_U^r. It is a finite scalar model for the same stratum, without descent of all global morphisms to one finite coefficient field. This proves the local finite-free clause even without the Tor-amplitude hypothesis.

Step 6 uses the complete statements of `lem-pc-kflat-resolution` (unbounded, with flat terms), `lem-pur-kflat-change-of-rings-independent` (the actual arbitrary change of rings preserves K-flatness and flat terms), `lem-sf-ringed-kflat-single-tensor-comparison` (one K-flat factor and an arbitrary degree-zero module), and `lem-pur-change-of-rings-tensor-cancellation-independent` (natural cancellation after restriction). I checked the hypotheses separately for R and B and wrote the termwise map, inverse, and differential compatibility. The derived comparison is asserted after restricting the left side to R-modules, exactly where the cited cancellation lands. It does not assign a nonexistent B-action to the right endpoint.

Step 7 is the direct Tor test in `sk-def-sfb-constructible`, for every B-module N, using its underlying R-module. `sk-def-sfb-change-of-scalars` states restriction is exact and unchanged on underlying objects; therefore it reflects vanishing cohomology. The interval [a,b] is retained, not enlarged. Combining this with bounded constructibility proves membership in D_ctf.

I tested the zero complex, empty scheme/stratum, zero scalar model, free integral model A^n, torsion scalar model A/(pi^m), and a mixture of free and torsion models. Rationalization kills the torsion model and yields rank n on the free part, including rank zero. For a shifted object the K-flat computation keeps its degree, so no interval-shift error occurs. The proof also works if the stipulated interval is empty: the Tor test forces the relevant vanishing and no choice of a<=b is needed in the argument. No projective-dimension criterion, flatness of N, enough-points assertion, derived completeness, dimension bound or invertibility of ell was used.

I checked delivery-errors B--E against the actual files: no new nodes needing additional definition dependencies or sources, no new proof hidden in a statement, no relabelled clauses, no statement dispute or silent correction, exact node-use/quote matches, and only elementary balanced-tensor/finite-matrix assembly done inline. Each proof step is below 1000 characters (well below the 2000-character audit threshold). Generic off-unit inputs are declared in split_report.tool_uses for maintainer review; no top-level maintainer tool_uses field was set. The statement and all historical metadata/searches are retained. Only sandbox files were written, and the server tools perform the required checks.
