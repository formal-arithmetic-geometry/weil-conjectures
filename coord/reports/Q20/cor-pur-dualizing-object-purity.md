# Q20 stage-1 repair: cor-pur-dualizing-object-purity

## Files written

- `dag/nodes/sec-smooth-purity/cor-pur-dualizing-object-purity.json`: unchanged statement and statement dependencies; repaired six-step proof and recomputed proof dependencies.
- `citations.json`: current verbatim statements supporting every citation of every step.
- `report.md`: this repair report. The previous report is retained locally as `report.previous-returned.md`; `searches.jsonl` is retained unchanged.

## New nodes

None; zero Mathlib leaves. Withdrawn proposed additions: `lem-pur-section-dnc-affine-local-comparison` and `lem-pur-single-degree-open-isomorphism-gluing`. Neither is in the current shared DAG, and neither remains in the delivery's node directory or dependencies. Existing shared nodes were not deleted or changed.

## Attachments

None. I repeated the read-only project search for the blueprint id and the dualizing/twist/exceptional-image notion. `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_twistShift`, `WeilConjectures/EtaleCohomology/Purity/Smooth/Basic.lean:335`, is existence of an isomorphism on the ordinary etale site, assumes an absolutely separated target, and does not state all canonical normalization and coherence clauses here. Its proof depends on the diagonal/deformation existence interfaces; the diagonal proof even records a TODO about using a trivial bundle instead of the actual normal bundle. It is not an attachment. Upstream master is reference material only.

## WANTED:

None.

## What was wrong / repaired

The retained delivery had a mechanically passing dry-run receipt but had not addressed this mathematical return. I first reran the required dry run without changing its node files: it exited successfully, at `b194a6c2ae`. That does not resolve the review's mathematical faults. I then made the following substantive repairs.

1. C5/D: old Steps 2-3 repeated the existing, reviewed full-domain diagonal theorem. Replaced them by one step applying `thm-pur-diagonal-dualizing-object` to exactly the item's hypotheses, and withdrew both proposed child nodes. No local DNC or gluing proof is repeated here.
2. E5/C3: the map is now the theorem's specified orientation `Pi_f` itself, as named in `def-pur-smooth-purity-map`. The tensor composite uses `1 tensor Pi_f^{-1}`. There is no source-affine orientation, no assertion that two chart constructions are “the same,” and no missing comparison of those maps.
3. Normalization: new Step 4 uses the statement of `lem-pur-projection-purity-agreement`, which identifies the actual diagonal-defined smooth purity map on the separated affine-space model with the explicitly Kummer-normalized iterated affine-line map for every E and n. It uses the statement of `lem-pur-vector-integration-site-comparison` for the actual trace, compact-support restriction, projection and adjoint-transpose equalities. It does not use properties of the withdrawn construction. I did not use `det-sp-orientation-vector-bundle`, whose current statement specializes to E=Q_l and would not justify the general coefficient claim. Projection agreement and integration comparison are in this item's own unit, so no off-unit tool is introduced. No use of `lem-sbc-smooth-relative-dimension-permanence` remains in this item's proof.
4. Recomputed `proof_deps` as exactly the union of the six steps' `uses`, and regenerated `citations.json` from the current dependency statements. Retained the correct reassociation, tensor arrow order, exchange cancellation and composition identity, renumbering their references.
5. Minor B5/B7 findings concerned the withdrawn gluing node. Its incorrect source-place claim and failed-Loogle-as-no-match record are not delivered. The raw historical search log and old report remain untouched as evidence: in that log `DerivedCategory, Sheaf` reports unknown identifier `Sheaf`, not evidence of mathematical absence. No search is newly claimed to have run, and no new Mathlib absence verdict is needed for this repair.

## Not duplicates

Both proposed new nodes are withdrawn. The diagonal theorem already supplies precisely the orientation needed by the corollary, including the finite-type nonseparated domain. No new node, elementary fact, or clause of the item is repackaged as a child. A whole-DAG/blueprint search for the dualizing-object notion confirms the existing theorem; the current corollary proof explicitly names it.

## Review by Q20

I read the returned item and report, the current repository version (the owned fields that differed were proof, proof_deps, proof_origin, status and split_report), `dag/units/sk-thm-smooth-purity.json`, the chapter record, the original master corollary statement/proof, and the main-20261015 corollary and diagonal proof under `sk-prop-sp-orientation`. The current corollary's three-arrow proof takes the orientation from the diagonal theorem. The historical unit's first step is already realized by that theorem; its model paragraph is carried by projection agreement. This repair follows both rather than rebuilding their arguments.

I opened the full current statement of every node used below. Citations quote those statements, never their proof bodies. In particular I read the full-domain statement and the reviewed localization/gluing proof of `thm-pur-diagonal-dualizing-object` to distinguish its stated orientation from the discarded construction. The only use of that proof here is to understand why it supersedes the old work; Step 2 takes only the canonical isomorphism its statement actually supplies.

Step 1 retains the direct complex calculation: `def-coefficient-twists-detailed` gives M(d)=M tensor^L Lambda(d); `def-weil-derived-tensor` gives a K-flat model; `def-pc-tensor-complex-sheaves` gives the total differential; `def-weil-abstract-derived-category` gives the shift. I checked Stacks Tag 012Z, `homology.tex`, `definition-associated-simple-complex`, against the two differential formulas. Since 2d is even and the Tate sheaf is in degree zero, both terms and differentials agree. This is elementary from the cited definitions, including d=0.

Step 2 takes exactly the canonical isomorphism omega_f -> Lambda_X(d)[2d] from the diagonal theorem's statement. Its assumptions are finite-type X,Y, the exceptional-image domain and smooth separated f of pure dimension d. There is no absolute separatedness requirement, so the doubled-origin base does not invalidate the invocation. `def-pur-smooth-purity-map` explicitly names this theorem's map as Pi_f. Using it directly removes the erroneous comparison between source-affine and target-affine maps.

Step 3 takes the stated canonical tensor isomorphism for every bounded constructible finite-Tor K from `thm-pur-cohomological-smoothness`. The definition of the purity map states the very three-arrow composite in this order. Tensoring inverse equations is elementary functoriality; it establishes invertibility of the middle arrow without choosing another orientation. The source is M(d)[2d], the target is Rf!K, and the coefficients remain A_{E,n} on the small pro-etale site.

Step 4 uses projection agreement only on a separated finite-type affine-space model, where that statement applies, and not to assert a global comparison on nonseparated schemes. Its statement explicitly identifies the diagonal-defined smooth purity map, extends the model to all n by choosing an annihilating ell^r, and gives identity for d=0. The comparison lemma explicitly states t_q^p h_q^p=1, identifies actual integration maps and their adjoint transposes, and imposes no e|n hypothesis. These are precisely the properties this step cites. The original Kummer-normalization sentence is thus tied to the specified map rather than an independent construction. `def-pur-smooth-trace` gives the displayed counit composite for every K and introduces no trace-map comparison inferred from object isomorphisms. I read the main projection-agreement proof as source material but rely on its repaired DAG statement, not on its compressed “same computation” sentence.

Step 5 retains the actual definition of the chapter's smooth exchange, e' b e^{-1}, and the commuting square in `thm-pur-smooth-base-change-coherence`. Associativity and cancellation yield e'b. The statement allows arbitrary v between finite-type schemes; neither flatness nor smoothness of v is inserted. This is the defined purity exchange, with no identification with an adjoint mate.

Step 6 uses the exact displayed composition identity in `thm-pur-composition-coherence`, now for the specified maps from Step 3. It gives the order of c_{g,f}^{-1}, the f and g purity maps, and the additive twists and shifts. It is not inferred merely from isomorphism existence. The other smooth morphism has dimension e and target Z in the same domain.

For B1-B10 there are no new nodes to audit: the two unnecessary statements, their source-place defect, and the failed search verdict have been withdrawn from the delivery. All prior searches remain logged; no new search entry or Mathlib leaf is asserted. For C1-C8 I checked every remaining step's non-elementary inputs against its named statements and exact quotations; the proof union is recomputed and the server checks test graph and route admissibility. For D1-D5 the substantive geometric theorem is an existing citation rather than a new child restating a conclusion. For E1-E7 I checked finite coefficient categories, all-E/all-n versus Q_l-only scope, the separated model hypothesis, inverse arrow direction, and the definition of exchange. No step exceeds 2000 characters (lengths 761, 655, 804, 1602, 828, 756), and no localization, gluing or map-comparison lemma is hidden inline.

The edge checks include d=0 and identity/model maps, K=0, empty X, ramified E with e not dividing n, and a nonseparated finite-type base. The proof does not add a frame, a nonempty-cover hypothesis, or absolute separatedness. No new statement needs a separate small-case test. I preserved the item's statement and all maintainer-owned fields; the delivery tool rebases the owned fields on current main. No SGA source is used and no unit/chapter route is changed.

## Remaining maintainer alignment issue

As the return explicitly notes, `def-pur-smooth-purity-map` still introduces X,Y as separated over k, whereas the diagonal theorem, this item, the trace and exchange statements use all finite-type schemes. Its displayed formula is the one used here, with the full-domain Pi_f from the diagonal theorem. I have not edited that other node or narrowed the item; the maintainer's requested alignment remains separate from this delivery.

## What could not be finished

No mathematical repair point remains in this item. The separate definition-domain alignment is reported above as requested. No Lean files, compiler, Lake command, live project file or launcher file was written.
