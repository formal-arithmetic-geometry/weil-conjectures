# Q55 stage-1 repair

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-cohomological-adic-criterion.json: assigned statement, unchanged; four assembly steps, 1854 proof characters.
- dag/nodes/sec-six-functors-basics/lem-sfb-local-integral-perfect-model-cohomology.json: one new statement-only child, not in Mathlib; local exact restriction and cohomology comparison for a supplied perfect scalar model.
- citations.json: verbatim statement quotations for every citation of the assigned item.
- local-model-proof.json and the proof below: the complete natural-language argument for the new child (1623 characters). Its DAG record is unsplit, as coord/brief-stage1.md and the delivery gates require for a new stage-1 statement. The return asks for the argument to be supplied; it is supplied here instead of putting forbidden proof steps in an unsplit child.

The sandbox initially contained only dispatcher marker files: no retained DAG files, report, citations or searches were present. I copied the current live item as baseline and preserved its statement, stmt_deps, sources, pointers and metadata. Its live proof has the same five long arguments named in the return; no prior completed sandbox work was discarded. Delivery rebases the owned split fields onto current server state.

## Attachments

None. The project's integral_cohomological_adic_criterion in lean/Sheaf/Paper/IntegralCohomologicalAdicCriterion.lean:107 has sorry in its proof. The exact tag and notion searches under lean/WeilConjectures/ found no completed attachment. No new Lean was written and no compiler, Lake or build command was run.

## WANTED

None for this repair: the Bhatt–Scholze PDF and Stacks sources used here are present. Historical local-field references wanted by existing coefficient lemmas remain their responsibility; their statements are used as existing nodes.

## Return repaired

The old 4304-character argument is replaced by a 1854-character assembly. Its coefficient-completeness argument is already exactly clause (1) of lem-sfb-integers-profinite-tower (1292 proof characters); its scalar-resolution argument is already lem-sfb-finite-constant-model-two-term-free-resolution (1655 proof characters). Creating renamed copies would violate the duplicate rule. I reused these nodes and extracted the remaining local cohomology comparison. The finite truncation induction is 427 characters and cites the truncation triangles and triangulated closure explicitly. No step exceeds 2000 characters. The new child's full argument below is also well under 3000 characters. The return's Lean module is left untouched because this is stage 1 only.

No statement dispute, source error, change of unit route, extra dimension bound or assumption that ell is invertible was introduced. The item statement is string-equal to the copied live statement, including its existing rendering. I corrected an interface omission in the shortened proof by citing the integral-limit identification explicitly when passing from the pulled-back condensed coefficients of the existing resolution theorem to B_S.

## Proof in words of lem-sfb-local-integral-perfect-model-cohomology

Source: Bhatt–Scholze, Proposition 6.8.11(3), last sentence, using Proposition 6.6.11. The following supplies the details the source abbreviates. Supporting sources read: Stacks Tag 09AA, proetale.tex, lemma-closed-immersion; Tags 093J and 093M, sites-modules.tex, lemma-constant-exact and lemma-completion-flat; Tag 00IK, algebra.tex, lemma-Noetherian-basic; and Tag 010N, homology.tex, lemma-exact-functor.

1. By [lem-pe-constant-left-module-inverse-image], $g^{-1}(R/\pi^n)_X=(R/\pi^n)_S$ canonically, compatibly with the reductions. By [lem-weil-pbc-proetale-immersion-limit-preservation], $g^{-1}$ preserves their small inverse limit, giving exactly the projection-induced $c_g$. The same lemma gives exactness of module inverse image followed by scalar extension along this ring isomorphism. Slice restriction is exact by [lem-pur-site-restriction-module-adjunction-exact]. Thus [lem-weil-pbc-exact-functor-complex-cohomology] identifies $j_U^*g^*H^q(K)$ with $H^q(j_U^*g^*K)$.

2. By [lem-weil-l-adic-extension-integers-dvr] and [lem-weil-pbc-pid-noetherian-normal], $R$ is Noetherian. Constant sheafification is exact by [lem-weil-pbc-constant-module-section-properties](1). The map $R_S\to B_S$ is flat by [det-prop-integral-criterion-constant-coefficients](1), so its scalar extension is exact by [def-pc-flat-sheaf-modules]. Together with exact slice restriction this makes $T_U$ exact. Apply [lem-weil-pbc-exact-functor-complex-cohomology] to obtain $H^q(T_U(P^\bullet))\simeq T_U(H^q(P^\bullet))$. Composing with the cohomology of the supplied model isomorphism gives the asserted isomorphism.

3. The cycle module $Z^q=\ker(P^q\to P^{q+1})$ is finite by [lem-weil-pbc-noetherian-submodule-finite], since $P^q$ is finitely generated. Its quotient $H^q(P^\bullet)=Z^q/\operatorname{im}(P^{q-1}\to P^q)$ is generated by the images of any finite set of generators of $Z^q$. It is finitely presented by [lem-sc-noetherian-finite-module-finite-presentation]. This argument allows torsion and does not require cohomology to be projective.

## Review by Q55

I read Bhatt–Scholze §6.5 (Definition 6.5.1 and Lemma 6.5.3), Proposition 6.6.11, and Definition 6.8.10 / Proposition 6.8.11(3), printed pp. 49, 54 and 60–61. I also read the current integral-criterion and integral-models-stacks blueprint proofs and the chapter/unit records. The new child isolates the calculation behind “follows easily from Proposition 6.6.11”; it neither assumes the adic condition nor concludes the global cohomological criterion, and has no stratification or completeness hypothesis. It is thus a local comparison used by the reverse direction, not a relabelled clause of the item.

For assembly step 1 I opened each cited statement: the DVR theorem gives the maximal ideal and residue field; the PID theorem gives Noetherianity; the profinite-tower theorem gives the canonical ring isomorphism to the inverse limit, not merely topological completeness. These are exactly the coefficient hypotheses of adic-stratified-perfect. The latter's (a) includes both local derived completeness and an actual bounded constructible etale origin with finite Tor amplitude, so it matches (2), including the residue-field and Tor conventions.

For step 2 the constructible definition supplies a finite constructible locally closed stratification with finitely presented scalar modules. The resolution theorem covers integral coefficients and torsion scalar modules and explicitly supplies both the scalar resolution and its exact extension. I checked its coefficient ring is the pulled-back continuous integral ring, and added the integral-limit theorem to identify it with B_S. This gives the scalar perfect complexes required by condition (b), so its implication to (a) applies to F[0]. No claim that a torsion module is free is used.

For step 3 I read the truncation-triangle statement: its three displayed vertices are exactly those used. The bounds make the first truncation zero and the last isomorphic to K. Zero, isomorphism and shift closure and the two-out-of-three clause are all in the adic-stratified-perfect statement. This is a finite induction on q, not a completion of an infinite Postnikov tower.

For step 4 the adic-stratified-perfect statement supplies both boundedness and a finite stratification with scalar perfect models. The new child supplies the restriction/cohomology identification and finite presentation on each of these same covering objects. Consequently the constructible definition applies to each H^q(K). I checked the child uses only locally closed coefficient restrictions, not arbitrary inverse images commuting with infinite limits. I opened all statements used in its proof above: immersion-limit-preservation includes the exact module functor along an isomorphic target ring; localized-module-adjunction-exact gives exact slice restriction; constant-module-section-properties gives exact constants; constant-coefficients (1) gives flatness for every scheme; flat-sheaf-modules defines the resulting exact tensor functor; the Mathlib exact-functor-cohomology leaf gives the actual natural comparison; and the two Noetherian-module leaves give finite cycles and finite presentation. These statements say precisely what the proof takes from them. The constant-ring inverse-image identification is explicitly supplied by lem-pe-constant-left-module-inverse-image, not inferred from a definition.

I tested X empty, an empty covering object U, K=0, P=0, a shifted rank-one scalar module, and the two-term complex R --pi^m--> R. Its degree-zero cohomology R/pi^m is allowed and is not assumed projective; the calculation gives the corresponding torsion completed model. The scheme hypotheses remain arbitrary in the child, while the parent keeps Noetherian X. Tensor products are sheaf scalar extensions; there is no unjustified tensor of section modules, no identification of arbitrary inverse-image completion rings, no choice of an unbounded resolution, and no need for uniform local amplitude in the new comparison. The parent receives its global bound from adic-stratified-perfect.

I checked delivery-errors B–E against the actual statements and sources. The new child is self-contained, uses genuine definitions, has one layer of statement dependencies, and contains no proof sketch in its statement. Its proof is supplied separately in accordance with the new-node rule. All recorded Mathlib searches were run through msearch.py and read, including alternate semantic phrasings and narrower source searches. Generic exact-functor homology preservation is already a Mathlib leaf and is cited, rather than recreated. No Mathlib result found supplies the completed coefficient restriction, finite scalar cohomology and local comparison together. The existing same-tag statements are distinguished below. The retained item's coefficient and residue hypotheses were not changed. I checked dependency paths for the reused profinite tower, resolution, and exactness lemmas: none reaches the item. There is no use of SGA.

## Not duplicates

lem-sfb-local-integral-perfect-model-cohomology vs lem-trf-point-reduction-unit-normalization: The existing statement concerns point coefficient-reduction comparisons are normalized by scalar-extension units; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-condensed-support-projection-formula: The existing statement concerns natural support tensor projection formulas on unbounded condensed modules; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs det-sfb-dc-restricted-functors-closed-image: The existing statement concerns extension by zero and closed direct image preserve integral constructible complexes; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs sk-lem-int-ext: The existing statement concerns continuity and boundedness of ext; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs det-lem-int-ext-bound: The existing statement concerns uniform vanishing of ext between integral constructible sheaves; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-locally-closed-module-extension-coherence: The existing statement concerns normalized locally closed extension on module sheaves; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs det-formal-closed-support-ii-limits: The existing statement concerns closed support commutes with derived limits of sequences; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs sk-lem-formal-closed-support-ii: The existing statement concerns closed support, truncation and derived limits; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-constant-realization-reflects-isomorphism-general: The existing statement concerns constant realization reflects derived isomorphisms and perfectness on a nondegenerate site; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs def-sfb-affine-locally-constructible-proetale-modules: The existing statement concerns affine-local constructibility of pro-etale modules over discrete noetherian rings; it contains no completed-coefficient sheaf cohomology comparison on a locally closed stratum. The new node asserts that comparison for a supplied perfect scalar model.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-proetale-locally-closed-extension: The existing statement concerns pointwise exact locally closed extension; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-constant-realization-derived-scalar-extension: The existing statement concerns derived constant realization commutes with derived scalar extension; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs def-sfb-quotient-kernel-completeness: The existing statement concerns local derived completeness for a ring-sheaf quotient kernel; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-formal-closed-pullback-derived-products: The existing statement concerns closed coefficient-compatible pullback preserves derived products; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-constant-realization-reflects-isomorphism: The existing cohomology comparison is for discrete constant coefficients and nonempty U; the new comparison is for completed B coefficients on arbitrary U, with stratum restriction and finitely presented scalar cohomology.

lem-sfb-local-integral-perfect-model-cohomology vs sk-lem-int-tensor: The existing statement concerns inverse image and tensor product; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs det-lem-formal-closed-support-sheaves: The existing statement concerns sections with support: the sheaf-level adjunction; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-proetale-identified-open-closed: The existing statement concerns exact open and closed extensions with identified inverse-image coefficients; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs det-prop-closed-adjoint-constructible-support: The existing statement concerns sections with support of a constructible complex are constructible; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-finite-constant-model-two-term-free-resolution: The existing statement resolves one finitely presented scalar module in degrees -1,0; the new statement computes every cohomology sheaf of a supplied arbitrary bounded finite projective scalar model. The resolution is reused by the parent.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-proetale-identified-supported-reconstruction: The existing statement concerns normalized supported reconstruction for actual tensor pullbacks; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-proetale-fp-local-models-comparison: The existing statement concerns intrinsic finite local models and fixed coefficient local models; it contains no completed-coefficient sheaf cohomology comparison on a locally closed stratum. The new node asserts that comparison for a supplied perfect scalar model.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-condensed-support-derived-localization: The existing statement concerns open/closed localization for ordinary derived condensed module objects; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-constant-to-continuous-scalar-flat: The existing statement concerns continuous coefficients are flat over discrete constant pid scalars; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-sfb-locally-closed-extension-coherence: The existing statement concerns restriction and composition for locally closed extension by zero; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-proetale-abelian-closed-support: The existing statement concerns closed support for abelian pro-etale sheaves; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs new-lem-weil-pbc-condensed-surjective-closed-equivalence: The existing statement concerns condensedsurjectiveclosedpullback isequivalence; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-locally-constant-finite-values-finite-type: The existing statement concerns locally constant with finitely generated values implies finite type; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs def-weil-pbc-derived-normalization-arrows: The existing statement concerns canonical derived coefficient normalization arrows; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs def-weil-pbc-completed-constant-realization-data: The existing statement concerns completed constant realization interfaces; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-krull-intersection-localization: The existing statement concerns intersection of the i-adic filtration of a finite module vanishes near v(i); it contains no completed-coefficient sheaf cohomology comparison on a locally closed stratum. The new node asserts that comparison for a supplied perfect scalar model.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-condensed-open-closed-recollement: The existing statement concerns open/closed recollement for condensed coefficient modules; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-completed-constant-module-model: The existing statement supplies exact realization and quotient-module identifications in degree zero, explicitly without a derived-complex conclusion; the new statement concerns cohomology of a supplied derived local model.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-completed-constant-algebra-flat-quotients: The existing statement concerns ordinary flat algebra and quotients of a completed constant ring; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-proetale-ringed-closed-counit: The existing statement concerns closed ringed counit is invertible; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs new-lem-weil-pbc-condensed-surjective-closed-local-presentation: The existing statement concerns lfp lowerstar of surjective closed; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-completed-constant-sheaf-reduction: The existing statement concerns completed constant coefficients and finite reduction; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-proetale-ringed-open-closed: The existing statement concerns ringed pro-etale open-closed localization; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-constant-completion-equivalence: The existing statement concerns constant-to-completed coefficients on derived-complete categories; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs stage3-b4-bounded-finite-free-resolution: The existing statement concerns bounded finite free resolution construction; it contains no completed-coefficient sheaf cohomology comparison on a locally closed stratum. The new node asserts that comparison for a supplied perfect scalar model.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-proetale-abelian-closed-counit: The existing statement concerns the closed counit on abelian pro-etale sheaves; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs new-lem-weil-pbc-condensed-finite-model-immersion-restriction: The existing statement concerns finite model on immersion range; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-constant-module-section-properties: The existing statement gives exact constant sections and ordinary tensor properties; the new statement computes cohomology after completed scalar extension and stratum restriction.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-noetherian-submodule-finite: The existing statement concerns submodules of a finite module over a noetherian ring are finite; it contains no completed-coefficient sheaf cohomology comparison on a locally closed stratum. The new node asserts that comparison for a supplied perfect scalar model.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-proetale-restriction-preserves-limits: The existing statement concerns limits preserved by weakly etale pro-etale restriction; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-finite-modules-noetherian-abelian: The existing statement concerns finite modules over a noetherian ring form an abelian category; it contains no completed-coefficient sheaf cohomology comparison on a locally closed stratum. The new node asserts that comparison for a supplied perfect scalar model.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-noetherian-finite-module-acc: The existing statement concerns ascending chain and maximal condition for submodules of a finite module over a noetherian ring; it contains no completed-coefficient sheaf cohomology comparison on a locally closed stratum. The new node asserts that comparison for a supplied perfect scalar model.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-proetale-inverse-image-limits-zariski-local: The existing statement concerns zariski locality of preservation of pro-etale inverse-image limits; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-proetale-immersion-limit-preservation: The existing statement supplies limit preservation and exact inverse image, but gives no perfect scalar model or finite-presentation conclusion; it is used in the new proof.

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-pbc-finite-perfect-adic-canonical-comparison: The existing statement concerns canonical derived quotients as explicit coefficient complexes with compatible finite-free retracts; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-cbc-finite-extension-reduction-cone-bound: The existing statement concerns uniformizer cone comparison and uniform reduction bound; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-sp-constant-pullback-scalar: The existing statement concerns module pullback transports scalar multiplication; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-sf-ring-sheaf-closed-localization: The existing statement concerns closed localization for arbitrary pro-etale ring-sheaf module objects; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sp-constant-inverse-image-section: The existing statement concerns transported global sections and constant quotient kernels; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-weil-finite-free-completed-scalar-comparison: The existing statement concerns finite free completed coefficient extension is ordinary derived scalar extension; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-cbc-extension-zero-stratified-perfect: The existing statement concerns extension by zero preserves stratified perfect local models; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-sf-ringed-closed-kernel-adjoint: The existing statement concerns the support-kernel adjoint for an arbitrary pro-etale ring sheaf; it contains no comparison from a supplied completed scalar perfect model to finitely presented scalar cohomology. The new node asserts that local cohomology comparison, with no completeness assumption on K.

lem-sfb-local-integral-perfect-model-cohomology vs lem-pod-point-principal-reduction-coefficients: The existing statement concerns the completed principal coefficient sequence is short exact; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-pod-point-reduction-coefficient-ring: The existing statement concerns the normalized lifted coefficient quotient is a regular principal quotient; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

lem-sfb-local-integral-perfect-model-cohomology vs lem-pod-completed-integral-scalar-regular: The existing statement concerns powers of the uniformizer are regular on completed coefficient sections; it does not assert the new node's locally closed restriction/cohomology comparison with finitely presented scalar H^q(P).

Additional conceptual comparisons: det-lem-int-integral-heart-local-model has separated finite-type and characteristic assumptions and depends on the assigned item, so cannot be used here. lem-weil-pbc-integral-stratified-perfect-closure-homology has explicit dimension and invertibility assumptions. lem-sc-coherent-ring-perfect-complex-cohomology concerns only scalar modules, with no completed sheaf or restriction comparison. lem-sfb-integral-constant-model-heart-closure is closure of an abelian constructible category under arbitrary sheaf morphisms, not this scalar-complex cohomology identification. lem-sfb-integers-profinite-tower already supplies the old coefficient argument and is reused without a duplicate.

## What remains

The new child's statement enters the stage-1 queue as required; its complete short argument is above. No mathematical obstruction remains for this repair. Server dry-run and delivery results are recorded below after they finish.

## Validation

The required deliver.py --no-push invocation exited successfully: `OK (not pushed) deliver/Q55/lem-sfb-integral-cohomological-adic-criterion at 5ff29c68378: preflight passed`. The server ran the required DAG and split checks. Local source-only validation also confirms statement and stmt_deps equality to current live, proof_deps equal to the union of all uses, 1854 item proof characters, and exactly the assigned node plus one new node in the sandbox DAG. No compiler was run.
