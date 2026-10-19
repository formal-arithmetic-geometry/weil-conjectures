## Worker report

1. Files written: dag/nodes/sec-six-functors-basics/lem-sfb-integral-model-surjective-closed-reflection.json (statement, split, no Mathlib match), citations.json, report.md and the appended searches.jsonl. No new child node or unit record is delivered.
2. Attachments: none. Project-source searches found no declaration of this exact scalar-local-model equivalence.
3. WANTED: none; both Stacks sources are available locally.
4. Repaired the interrupted affine/global cover argument and cited the exact global cover-refinement and condensed module equivalence results. Kept the statement, source, original blueprint ancestry, imported searches and logged search history. The proof is four short steps; the earlier attempt is retained below as a historical working record.
5. The mathematical split and citation audit are complete; the required delivery dry run and push are the remaining operational checks. No Lean was written or compiled.

## Review by Q148

I re-read the current item, the chapter and unit sk-lem-int-ext records, the parent main-20261015 blueprint proof det-lem-int-ext-formula (1), and proetale.tex at Tag 09BK (lemma-closed-immersion-affines) and Tag 09AB (lemma-thickening). The item statement is unchanged. The first underline A denotes a condensed topological ring; in C_T(P) it denotes the ordinary constant scalar ring. No Noetherian, finite-type, reducedness or uniform-nilpotence hypothesis has been added. The unit's refined-stratum argument still uses this result in the same place.

I found and repaired two citation gaps in the interrupted proof. The affine 09BK node did not itself give the asserted global covering, and a set-topos equivalence plus the closed counit did not explicitly state the required condensed module equivalence. The final proof now cites the existing global cover-refinement and condensed-module equivalence statements, which I opened in full and checked against the requested witnesses and coefficient category. No new nodes are introduced, and neither reused node reaches this item, so this introduces no circular proof. Generic uses outside this unit are declared in split_report.tool_uses.

Step 1 cites the actual pro-etale base-change/inverse-image construction and the strong-monoidal, colimit-preserving site inverse-image theorem. Its finite-limit and covering hypotheses are explicit in the inverse-image definition. The scalar-model comparison is the direct tensor-coequalizer calculation in the change-of-scalars definition, with the cartesian coefficient isomorphism and the module-pullback formula. Constant sheaves are preserved by applying the same colimit-preserving functor to their free abelian presentation. This avoids silently assuming a finitely generated module is free, or that it is flat. All scalar actions and the constant/pulled-back distinction are retained.

Step 2 uses covering-preserving base change and the module composition comparison, then Step 1. These cited statements provide precisely the covering and the two pullback identifications. Thus each original M_alpha supplies a local model of i^*F, including torsion.

Step 3 uses exactly the witnesses in exists_cover_refinement_surjective_closed: T_gamma covering X, beta, W, q, p, r, the cartesian square and the equation r followed by V_beta -> Z equals p. The base-change clause of the surjective-closed-immersion theorem makes q surjective and closed. Both input hypotheses hold for the given i, without assuming affine X or a nilpotent ideal of bounded order.

Step 4 applies the condensed module equivalence to q and the admissible commutative condensed valuation ring A. Its statement quantifies over arbitrary commutative condensed rings, arbitrary schemes, and surjective closed immersions. Module composition identifies the pulled-back F along the two routes; Step 1 identifies the scalar tensor along both routes. Fullness lifts the isomorphism and its inverse and faithfulness proves the inverse identities. The models are obtained separately on each cover member, so no agreement of the independently chosen N_beta or isomorphisms on overlaps is asserted or required.

I tested identity immersions, empty schemes (both sides have vacuous local covers), Spec(k) -> Spec(k[e]/e^2), and P=0, A, A/(varpi), and A/(varpi^2). Torsion remains in degree zero: there is no derived tensor in the item. The base-change lemma and cover-refinement theorem impose no Noetherianity or uniform nilpotence. The reviewed B--E checks give no new nodes, no duplicated clause or renamed whole result, no uncited cover-lifting theorem, and no use of a cited proof rather than a statement. Every final proof step is below 2000 characters. All per-step citations are copied programmatically from the current node statements.

I retained the imported searches and the actual interrupted search log. Two earlier grep calls supplied a redundant Mathlib/ prefix, so their zero results are explicitly marked unusable rather than treated as absence. Corrected msearch.py grep calls inspect AlgebraicGeometry/Sites and all of Mathlib. I read ConstantSheaf.lean:165 (dense-site constant sheaves) and ClosedImmersion.lean:416 (requires reduced target); neither proves this integral pro-etale scalar-model theorem. The earlier LeanFinder and LeanSearch results and second phrasing are retained, and no matching project declaration was found. The delivery has zero new nodes and zero Mathlib leaves. The old self-review below is a retained working record, superseded where it used the affine result globally.

## Earlier interrupted worker report

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-integral-model-surjective-closed-reflection.json` (statement; split; no new nodes; no Mathlib match), `citations.json` (verbatim quotes for every cited step), and `searches.jsonl` (the required Mathlib searches).
2. Attachments: none. I searched the slopmaster2 source for the blueprint id and the local-model/reflection terminology; no sorry-free project declaration states this item.
3. WANTED: none.
4. The item is the statement-only child introduced by the parent split. I supplied its one-level proof rather than moving any clause of the parent filtration into another node. The proof follows Tags 09AB and 09BK: topological invariance, pullback of scalar presentations, and cover lifting followed by local descent. No statement was weakened and no coefficient category was changed.
5. Nothing remains unfinished. No Lean code, compiler, Lake, or build tool was run.

## Earlier interrupted self-review by Q148

I read the item node, the `sec-six-functors-basics` chapter record, the parent blueprint node `det-lem-int-ext-formula`, and the Stacks source `literature/stacks-project/proetale.tex` at Tag 09AB (the thickening/topological-invariance lemma) and Tag 09BK (the affine closed-immersion site lift). I also opened every cited DAG statement. The item keeps the finite extension $E/\mathbf Q_\ell$, its valuation ring $A=\mathcal O_E$, the pulled-back condensed coefficient rings $B_T$, arbitrary finitely generated scalar modules including torsion, and both implications of the local-model equivalence.

Step 1 uses `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`, which says that a surjective closed immersion and every base change are surjective closed immersions and universal homeomorphisms. It then uses `lem-trf-proetale-topological-invariance`, whose statement gives quasi-inverse pro-etale inverse/direct image functors and isomorphisms for the unit and counit. I checked this also covers the base changes used later.

Step 2 uses `def-weil-proetale-inverse-image` for covering-preserving base change, `sk-prop-sfb-cartesian-coefficients` for the coefficient-ring isomorphism and exact module pullback, `sk-def-sfb-module-pushforward-pullback` for the module pullback convention and composition comparison, and `sk-def-sfb-constructible` for the finite constant scalar-matrix model. Pulling a finite presentation back leaves the scalar matrix and the finitely generated module unchanged, so torsion is retained. This proves (a) implies (b).

Step 3 uses `lem-weil-pbc-affine-closed-site-functor-properties` exactly for the Tag 09BK affine lift, its covering-family preservation, and its base-change identification. The resulting $W_\gamma\to B_\gamma$ is a base change of $i$, so Step 1 applies. `lem-weil-pbc-proetale-ringed-closed-counit` supplies the module-valued closed-immersion counit, while the cartesian-coefficients statement transports the $B$-action. Pulling the local isomorphism from $V_\beta$ to $W_\gamma$ and using the resulting full faithfulness identifies $F|_{B_\gamma}$ with the unchanged model $B_{B_\gamma}\otimes_A N_\beta$. The affine lifts cover $X$, proving (b) implies (a).

I checked the edge cases $i=\mathrm{id}$, the square-zero thickening $\operatorname{Spec}(k)\hookrightarrow\operatorname{Spec}(k[e]/e^2)$, the zero module, $A$, and $A/(\varpi)$. The argument uses no uniform nilpotence exponent and no Noetherian hypothesis. The Mathlib searches were rerun in this resumed attempt with two semantic phrasings for LeanFinder, Loogle, and source grep, plus LeanSearch; they found only generic constant-sheaf or étale declarations and no matching theorem. The source and DAG searches found the existing topological-invariance and affine-lift nodes, which are cited rather than duplicated.

## Not duplicates
lem-sfb-integral-model-surjective-closed-reflection vs det-sf-open-closed-pullback-limits: states closed inverse image preserves limits, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs lem-weil-pbc-affine-closed-inverse-image-left-adjoint: states affine pro-etale closed inverse image has an extra left adjoint, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs lem-weil-pbc-affine-closed-site-functor-properties: states affine closed immersion site functor properties, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs lem-weil-pbc-noetherian-stratum-detection: detects morphisms and presentations on a Noetherian stratification, whereas this node reflects finite scalar local models across one arbitrary surjective closed immersion.

lem-sfb-integral-model-surjective-closed-reflection vs lem-weil-pbc-proetale-abelian-closed-counit: states the closed counit on abelian pro-etale sheaves, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs lem-weil-pbc-proetale-immersion-limit-preservation: states inverse images along immersions preserve pro-etale limits, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs lem-weil-pbc-proetale-ringed-closed-counit: states closed ringed counit is invertible, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs new-lem-weil-pbc-condensed-finite-model-immersion-restriction: transfers a locally finitely presented integral model through a change of condensed rings; it does not assert finite constant scalar-module models.

lem-sfb-integral-model-surjective-closed-reflection vs new-lem-weil-pbc-condensed-surjective-closed-equivalence: states equivalence of module categories, not reflection of local covers with finitely generated scalar-module models.

lem-sfb-integral-model-surjective-closed-reflection vs new-lem-weil-pbc-condensed-surjective-closed-local-presentation: concerns ordinary local finite presentation with sheaf-valued matrices, not the specified finite constant scalar-matrix local models.

lem-sfb-integral-model-surjective-closed-reflection vs new-lem-weil-pbc-proetale-surjective-closed-cover-refinement: lifts covers only; it does not descend isomorphisms of integral module sheaves to scalar models.

lem-sfb-integral-model-surjective-closed-reflection vs new-lem-weil-pbc-specialization-closed-site-counit: states invertibility of the affine closed-site specialization counit, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs det-brown-hypotheses-small: states $\dctf(x,\lambda)$ is thick and essentially small, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs det-lem-coefficient-heart-common-stratification: orders stratifications and treats lisse field coefficients, not completed integral scalar models under a surjective closed immersion.

lem-sfb-integral-model-surjective-closed-reflection vs det-lem-int-tensor-shriek: states extension by zero and closed direct image preserve $\dbc(-,\mathcal o_e)$, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs def-exc-closed-site-lift: states lifting affine objects of the closed site, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs lem-exc-closed-cover-extension: states lifting a covering of a closed fibre, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs lem-exc-closed-inverse-image-formula: states a presheaf formula for closed inverse image, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs lem-exc-closed-site-adjunction: states adjunction for the closed-site lift, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs lem-exc-proetale-closed-exact: states exactness of closed direct image, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs lem-exc-proetale-closed-fully-faithful: states full faithfulness of closed direct image, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs lem-sp-proper-open-derived-support: states proper pro-etale direct image preserves extension-by-zero support, rather than equivalence of finite scalar-module local models for integral pulled-back coefficients across arbitrary surjective closed immersions.

lem-sfb-integral-model-surjective-closed-reflection vs i-topology: concerns derived finite-Tor-amplitude categories with the trace-formula coefficient conventions, not this abelian integral scalar-model property.

lem-sfb-integral-model-surjective-closed-reflection vs lem-trf-proetale-topological-invariance: states equivalence of sheaf topoi; no integral scalar-module local-model equivalence is in its statement.

lem-sfb-integral-model-surjective-closed-reflection vs lemma-constructible-universal-homeomorphism-invariance: the existing blueprint statement concerns constant or finite étale sheaves; the new one concerns pro-étale completed integral scalar models, including torsion.
