# Worker report: prop-functor-package, Q92

## Files written

- dag/nodes/sec-six-functors/prop-functor-package.json: existing statement, unchanged; seven-step assembly, 1,910 characters in proof text.
- dag/nodes/sec-six-functors/lem-sf-package-coefficient-domain-realization.json: statement; unsplit; no Mathlib match; no proof steps or proof dependencies.
- dag/nodes/sec-six-functors/lem-sf-package-compactified-tower-comparisons.json: statement; unsplit; no Mathlib match; no proof steps or proof dependencies.
- dag/nodes/sec-six-functors/lem-sf-package-localization-projection-realization.json: statement; unsplit; no Mathlib match; no proof steps or proof dependencies.
- dag/nodes/sec-six-functors/lem-sf-package-base-change-domain-realization.json: statement; unsplit; no Mathlib match; no proof steps or proof dependencies.
- dag/nodes/sec-six-functors/lem-sf-package-normalized-orientation-perfect-duality.json: statement; unsplit; no Mathlib match; no proof steps or proof dependencies.
- dag/nodes/sec-six-functors/lem-sf-package-verdier-coefficient-realization.json: statement; unsplit; no Mathlib match; no proof steps or proof dependencies.
- dag/nodes/sec-six-functors/lem-sf-package-exceptional-coherence-realization.json: statement; unsplit; no Mathlib match; no proof steps or proof dependencies.

- report.md: this signed review and verbatim argument-transfer record.
- citations.json: one literal statement excerpt per assembly-step citation, covering every node used.

## Attachments

None. Read lean/WeilConjectures/WeilSheaf/LowerShriekFunctoriality.lean. Its proper-coincidence definitions are proved but cover only part of the item. The open-immersion compactification comparison, composition and base-change declarations still have sorry proofs (in particular lines 174, 194, 213, 229, 256 in the read snapshot). They do not constitute a finished attachment for this package. The item's existing Lean and audit records are retained unchanged. No Lean was written, no compiler or Lake was run.

## Wanted literature

None for this re-split. The current blueprint statement and proof are available at literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.md and prop-functor-package.proof.md. The existing expanded proof is agent-written assembly of the individually cited results. Its route remains the lecture-notes purity route; no SGA source is introduced.

## Return repaired

The human returned the 13,010-character proof to spread its work. The sandbox initially contained only dispatcher brief markers, with no node files, report or search log. I therefore recovered the exact returned 18-step split from the current read repository; its total proof-text length is exactly 13,010. The baseline was compared to the current read-repository item again during the repair and matched. There is no discarded retained attempt or fabricated search history. The preliminary dry run exited with the expected missing-report diagnostic. The final delivery is built/rebased by deliver.py in its own worktree, without any git command in the shared read repository.

Every old step has exactly one new owner in the map below. The new nodes are independent statement-only tasks, all in the parent unit, with empty proof, empty proof_deps and null proof_origin. Their statements include the actual map identifications and domain restrictions that the old argument established, rather than only the parent clause labels. The full original argument, including sources and all cited prerequisites, is retained verbatim later in this report for the next workers. New nodes do not depend on one another or on the parent. The parent statement, statement dependencies and all maintainer-owned fields are untouched.

This human-requested re-split deliberately extracts intermediate multi-stage realizations from an already reviewed assembly; it is not the usual first split that forbids extracting an item's clause. Each task is strictly smaller than the whole item. In particular no task combines base change, purity, duality and all the other operations. The extracted tasks have retained argument sizes 1,610, 2,208, 1,789, 3,468, 1,093, 1,460 and 1,382 characters: multiple workers can start substantial separate arguments simultaneously. The somewhat longer base-change task owns three parallel coefficient-domain verifications, not an undisclosed single replacement of the whole package.

## Argument ownership

| New node | Original steps | Original argument characters |
|---|---|---|
| lem-sf-package-coefficient-domain-realization | 1, 2, 3 | 1610 |
| lem-sf-package-compactified-tower-comparisons | 4, 5, 6 | 2208 |
| lem-sf-package-localization-projection-realization | 7, 11 | 1789 |
| lem-sf-package-base-change-domain-realization | 8, 9, 10 | 3468 |
| lem-sf-package-normalized-orientation-perfect-duality | 12, 14 | 1093 |
| lem-sf-package-verdier-coefficient-realization | 13, 15, 16 | 1460 |
| lem-sf-package-exceptional-coherence-realization | 17, 18 | 1382 |

## Search record

For every new node I ran LeanFinder with two distinct natural-language formulations, LeanSearch, Loogle and grep through the prescribed msearch.py command. searches.jsonl is the unmodified actual command log; the per-node .search-results.txt files preserve full command answers, and mathlib_searches records the exact tool/query strings and returned hit names. All these services answered. Two initial Loogle queries had unknown identifiers, recorded as invalid rather than as mathematical evidence of absence; successful corrected Loogle queries were also run and recorded. No unavailable service was represented as a negative match.

I read the returned candidates: triangulated functor/map_distinguished declarations supply general preservation tools, not the identified adic pushforward towers or recollement maps. SheafOfModules.pullbackPushforwardAdjunction is ordinary module-sheaf adjunction, not constructible exceptional adjunction. IsProper stability and smooth-base-change algebra statements do not state cohomological exchange. AdicCompletion composition concerns ordinary modules, not derived sheaf towers. Module.evalEquiv/IsPerfPair concern module duality and do not supply smooth orientation or geometric Verdier duality. The other hits are condensed-module axioms, algebraic adic completion, local cohomology, topological compactification or unrelated normalization. No new node is an exact match or a one-line specialization of a hit; there are zero Mathlib leaves.

I searched the whole DAG with rg, and the whole imported blueprint with tools/blueprint_refs.py search, for the seven argument topics before writing them. The exact queries and matching file lists are retained as blueprint-searches.txt and duplicate-search-1.txt through duplicate-search-7.txt. A name/concept search in lean/WeilConjectures found no declarations for the new realizations. No new source carries a Stacks tag, so there are no same-tag pairs; substantive nearby statements are compared below. All blueprint.from records point to prop-functor-package with the exact old step positions and topic; same_as is empty because no imported node states the full intermediate realization.

## Not duplicates

lem-sf-package-coefficient-domain-realization vs thm-sf-ctf-stability: the latter supplies constructible stability and amplitude conclusions but does not give the exact common-stage functor/transformation realization with scalar identity, associator and shift equations, exact embeddings and idempotent-complete triangulation.
lem-sf-package-coefficient-domain-realization vs prop-weil-pbc-descent-functors: the latter descends supplied scalar-compatible exact functors; it does not establish constructibility or identify internal-Hom reductions and the actual operation values that furnish this family's inputs.
lem-sf-package-compactified-tower-comparisons vs prop-compactification-coherence-detailed: the latter is the finite-origin refinement comparison, not the integrated reduction/effectivity, identity-open strict transition and all-stage composition realization.
lem-sf-package-compactified-tower-comparisons vs lem-coef-normalized-dvr-effectivity: the latter recovers terms of an already normalized tower without constructibility; the new task also identifies the actual direct-image towers, comparisons and proper composition.
lem-sf-package-compactified-tower-comparisons vs lem-sf-integral-compactification-comparison-bridge: the latter identifies a particular semilinear/constant-tower compositor under explicit system hypotheses; it does not supply finite and field refinement independence, general reduction/effectivity and proper coincidence in this realization.
lem-sf-package-compactified-tower-comparisons vs thm-sf-comp-composition: the latter has finite coefficients and etale-origin witnesses; the new task identifies integral strict-transition towers and their field passage as well as coefficient reconstruction.
lem-sf-package-localization-projection-realization vs prop-sf-open-closed-triangle-all-stages: the latter is the triangle on X before applying f; the new statement identifies every vertex and arrow after compact-support realization on Y and includes projection compatibility.
lem-sf-package-localization-projection-realization vs lem-weil-compact-support-reduction-tower-functor: the latter constructs an exact strict-tower lift; it does not identify the total-limit image triangle, its composition-normalized endpoints and field/Weil passage, or the projection map.
lem-sf-package-localization-projection-realization vs fix-prop-projection-formula: that supplies the projection isomorphism, but not the coherent strict-tower localization image and connecting map.
lem-sf-package-base-change-domain-realization vs fix-lem-exchanges: the latter defines/identifies exchange coherence and smooth exchange on supplied domains; the new task verifies geometric finiteness/compactification hypotheses and realizes all proper, smooth and compact-support isomorphisms with precise higher-coefficient landing conditions.
lem-sf-package-base-change-domain-realization vs thm-weil-pbc-qbar: the latter is one proper base-change coefficient case; it does not give the geometric verification, smooth cases or arbitrary compact-support cases.
lem-sf-package-base-change-domain-realization vs thm-cbc-qbar: the latter treats algebraically closed coefficient compact-support exchange with supplied admissible presentations; it does not supply ordinary proper/smooth comparisons or the common geometric verification across stages.
lem-sf-package-normalized-orientation-perfect-duality vs thm-pur-rational-and-qbar-purity: the latter supplies field purity from a normalized lattice, not the finite/integral trace identification and independent coefficient-point/site-perfect evaluation biduality.
lem-sf-package-normalized-orientation-perfect-duality vs thm-sf-dual-perfect: that gives perfect duality once the orientation is supplied; the new task also realizes the normalized finite/integral/field orientation and its actual counit-defined trace and independent point case.
lem-sf-package-normalized-orientation-perfect-duality vs lem-weil-coefficient-frobenius: coefficient-point duality does not establish smooth orientation, adic reconstruction, or its trace and geometric perfect-duality identification.
lem-sf-package-verdier-coefficient-realization vs thm-fix-general-biduality: the latter is finite geometric biduality; the new task assembles its boundary consequence with actual evaluation-preserving integral and field passage and Verdier exchange.
lem-sf-package-verdier-coefficient-realization vs thm-coef-integral-verdier: the latter is the integral anti-equivalence and its bounds/reductions, not the full finite boundary/constructible exchange and rational/common-stage realization.
lem-sf-package-verdier-coefficient-realization vs thm-coef-qbar-verdier: the latter supplies the last coefficient stage rather than the finite boundary consequence and actual compatible multi-stage realizations together.
lem-sf-package-exceptional-coherence-realization vs lem-sf-constructible-exceptional-adjunction-coefficients: the latter gives normalized coefficient adjunction, but not the D_X f^* D_Y identification together with compactification dimension verification and all proved operation-domain coherence.
lem-sf-package-exceptional-coherence-realization vs fix-prop-coherence: that gives coherence for already proved comparisons; the new task also realizes the constructible exceptional formula and adjunction with the finite dimension bound required for its compactification.

## Review by Q92

I read the current blueprint statement and its entire proof, the chapter/unit route and the 18-step expanded repository proof. For every new task its source is a specified portion of that proof, and the ownership table and verbatim record below show exactly which arguments it inherits. This is an argument-preserving repair of the human return, not a replacement proof route. I checked delivery-errors B–E against the files: all new statements introduce k, coefficients, schemes, operations and input categories; none carries proof steps or proof dependencies; all cited notions have existing definition/domain nodes; sources point to available blueprint passages; and every search entry comes from an actual msearch log record. The parent has only seven citations, all to these new statement-only tasks; citations.json quotes the full claim paragraph used in each, verbatim.

In assembly step 1 I checked the coefficient-domain node actually asserts pullback/tensor/direct-image preservation, both-variable Hom preservation, evaluation-defined reductions, the qualified sharp bound, exact finite extension and the common-stage exact/idempotent-complete descent. It therefore supplies both the opening paragraph and clause (1), without inferring site-perfectness from finite Tor amplitude. Original steps 1–3 and all their cited node ids are retained below for the worker; the distinction between completed integral tensor and discrete non-torsion coefficients is explicit.

In assembly step 2 I checked the compactified-tower statement actually gives refinement independence/cocycle, both direct-image coefficient comparisons, the normalized-tower counit and its separate uniform constructibility requirement, composition unit/associator and proper coincidence, including strict transition maps before limits. Those are precisely original steps 4–6. The identity-open compactification identifies the ordinary and compact-support quotient-transition towers, not just individual levels. Normalization is a hypothesis on a tower and uniform bounds remain additional; no arbitrary tower effectivity is inferred.

In assembly step 3 I checked the localization/projection statement gives all three arrows of the image triangle, their exact strict-tower realization and field passage, as well as the actual projection transformation on K bounded constructible and L finite-Tor. This owns original steps 7 and 11. I read the exact reduction-tower functor statement: it includes natural evaluations on morphisms and quotient transitions, which are the needed inputs for an image of a coherent triangle. Applying a derived limit to unrelated levelwise triangles is explicitly avoided by the new statement. Empty open and empty closed complements give the identity/zero triangles, and field Weil structures require the geometry and input to descend.

In assembly step 4 I checked that the base-change task owns all three original steps 8–10. Its Cartesian square has the same arrow positions and output Y' as the parent, and it explicitly states both exchange maps. Noetherian/quasi-compact/quasi-separated and finite dimension come from finite type over a field; the original argument also verifies a uniform geometric fibre bound by field-extension invariance, including empty fibres. Properness is retained under base change. The smooth theorem's labels are swapped as written in the preserved step. Compatible etale-origin finite reductions, an admissible E lattice, stable common-stage representatives and uniform constructible/interval landing bounds are all retained; no small-etale discrete non-torsion exchange or automatic Qbar constructible landing is added. The compact-support case requires no smooth g.

In assembly step 5 I checked the orientation/perfect-duality statement actually identifies the inverse purity map, the exceptional counit-defined trace, finite-reduction compatibility and the two independent point/smooth-perfect cases. It owns original steps 12 and 14, and follows the finite diagonal/deformation route through the existing purity theorem. I read the coefficient Frobenius lemma: R is not quasi-Frobenius, so its point assertion is DERIVED evaluation, while finite quotient and field ordinary duality are exact. I read the perfect-duality statement: it identifies evaluation biduality under orientation, rather than simply producing some isomorphism with a double dual. On a point r=0 the orientation and formula have no twist/shift. For the empty smooth scheme I made the pure dimension parameter d explicit with d>=0, so no shift uses a possibly negative-infinite Krull dimension. The zero complex and empty scheme then cause no exception. Site-perfect and constructible finite-Tor remain different notions.

In assembly step 6 I checked the Verdier-coefficient task gives the actual constructible exchange, geometric finite anti-equivalence, its boundary consequence and evaluation-defined integral/rational/common-stage biduality. It owns original steps 13, 15 and 16. During review I corrected an initially overbroad boundary-definition reference: def-weil-boundary-exceptional-comparison-data defines a different etale/pro-etale Hom comparison, whereas the claim needed here is the beta_L map i^*D_TL -> D_Z Ri^!L. The delivered statement now writes that map explicitly and cites def-weil-boundary-duality-input, agreeing with cor-weil-boundary-duality-discharge. This is a correction of my new node's notation, not a change of the parent's statement. I also explicitly quantified the locally closed T, the closed immersion i and its input L in the finite constructible category. Boundary discharge is a consequence after geometric duality, never a premise used circularly to prove it. The integral uniform output bounds and actual evaluation maps, then rationalization and retract descent, all remain separate obligations inherited by this task.

In assembly step 7 I checked the exceptional/coherence task gives the actual D_X f^* D_Y formula, adjunction, reduction-identified units/counits and finite compactification dimension bound, plus domainwise coherence and field Weil equivariance. It owns original steps 17–18. Proper p is finite type and Y is finite type over k, so the compactification source has finite dimension; zero is permitted as bound for an empty compactification. No unrestricted ambient pro-etale right adjoint is claimed, nor arbitrary-base-change commutation of Verdier duality. I read the existing constructible exceptional coefficient-adjunction and coherence statements to distinguish their proper scope from this realization task. No new node is used via an unquoted proof or via data absent from its statement.

The long-step audit now finds no non-elementary parent step over 2,000 characters: each step is a short application of a self-contained statement. Every original argument is retained below, including the 3,468-character combined base-change verifications assigned to their own task. These have not been silently deleted or shortened. No statement dispute or new source error was found, and no target statement or definition was changed.

## Validation

A server-side review_split check of the sandbox parent passed. The first full preflight rejected the TeX array row separator in the new base-change statement as doubled backslashes; I replaced the array by explicitly named arrows and the Cartesian equation/pullback identification, preserving the square. The next full dry run passed with receipt 27576953cfe; after the final explicit-dimension/input-quantifier clarifications I ran a fresh final dry run before pushing. Final dry-run and push results are recorded by deliver.py. Local JSON/citation validation confirmed the statement is unchanged, the seven ownership sets partition steps 1–18, every cited statement exists, every quote is literal, the parent proof is below 3,000 characters, and all new proofs/dependency lists are empty. Only the required server checks are used; tools/check_dag.py, tools/review_split.py and tools/preflight_delivery.py were never run locally.

## Verbatim transferred arguments for the new workers

This is the complete former proof, not proof steps in the new node JSON. Each next worker receives a self-contained statement and can recover its original detailed argument and exact prerequisite ids here. The new nodes intentionally remain unsplit so these workers can write their own one-level splits independently.

### lem-sf-package-coefficient-domain-realization

Original step 1; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Opening internal-Hom paragraph.

Establish the finite constructible domains before assembling the clauses. Apply the preservation theorem to pullback, tensor and both direct images. Its site-perfect qualification on the dimension-free Hom bound is retained. Apply the finite constructible-Hom corollary to both finite-Tor inputs and then its general evaluation-defined coefficient comparison. Thus this package does not infer site-perfectness from finite Tor amplitude.

Cited nodes: thm-sf-ctf-stability, cor-weil-finite-constructible-hom, thm-coef-finite-hom.

Original step 2; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Opening integral and field paragraph.

For integral inputs use completed pullback and tensor, not discrete non-torsion etale coefficients. The integral preservation lemmas give bounded constructibility of pullback, tensor, ordinary and compact direct images. The integral Hom corollary supplies preservation and the evaluation-defined reduction map for arbitrary bounded constructible first variables. For the field-stage pullback, tensor and direct images, the operation-reduction statement gives their coefficient-passage comparisons. Exact rational transport and the exact common-stage embeddings of step 3 preserve shifts and these constructible object values. The rational operation theorem supplies the internal-Hom identification; the exceptional and duality assertions are assembled in steps 16–17.

Cited nodes: lem-pur-integral-operations-preserve-constructible, lem-sf-integral-direct-image-constructible, lem-sf-integral-compact-support-constructible, cor-coef-integral-internal-hom, lem-coef-rational-operations, lem-fix-operation-reduction, prop-weil-pbc-rational-transport.

Original step 3; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (1).

Clause (1): finite coefficient-field extension is exact triangulated by the scalar-extension lemma. Given compatible functors and transformations, apply the descent proposition to their unit, associator and shift equations. This produces functors and equations on the common-stage category; its idempotent-complete triangulated structure and exact stage embeddings are supplied by the triangulation theorem.

Cited nodes: lem-weil-scalar-extension-exact-triangulated, prop-weil-pbc-descent-functors, thm-weil-pbc-idempotent-complete-triangulation.

### lem-sf-package-compactified-tower-comparisons

Original step 4; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (2), compactification comparisons.

Clause (2), compactifications: use the canonical proper/open refinement comparisons on the witnessed etale-origin finite domain. The coherence proposition gives identity, transitivity, common-refinement independence and the cocycle. Bounded constructible finite inputs have etale-origin witnesses by the comparison equivalence. For integral and field inputs use the completed and transported comparison statements of the exchange theorem, retaining their finite-reduction, lattice and amplitude domains; its refinement compatibility identifies the comparisons of the chosen compactifications. No comparison on arbitrary unbounded pro-etale complexes is inferred.

Cited nodes: prop-compactification-coherence-detailed, lem-sf-proetale-constructible-origin, fix-lem-exchanges.

Original step 5; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (2), finite reduction and normalized reconstruction.

Clause (2), coefficient reduction: apply operation reduction to derived-complete integral inputs for both direct images. For finite quotients apply the ordinary direct-image coefficient theorem with B=A_{E,m} and the compact-support comparison on the finite-Tor domain. For a coherent normalized tower apply effectivity: its actual counit reduction recovers M_n. If these terms are constructible with supports in a single finite interval, this recovery plus derived completeness is exactly membership in the integral category. Effectivity alone supplies neither these bounds nor normalization.

Cited nodes: lem-fix-operation-reduction, lem-coef-finite-direct-image, lem-fix-compact-support-coefficient-change, lem-coef-normalized-dvr-effectivity, def-weil-derived-complete-integral-detailed.

Original step 6; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (3), composition and proper maps.

Clause (3), composition and proper coincidence: invert the finite composition isomorphism alpha to obtain the displayed direction R(gf)_! to Rg_!Rf_!. Its unit and associativity identities remain the same equations after inversion. The completed and field composition comparisons in the exchange theorem give the same identities on their coefficient domains. For proper f choose the compactification with open factor the identity, so the defining composite is Rf_*; proper coincidence identifies its exchange with the proper exchange. At integral coefficients take the same identity-open compactification at every level. Its terms and quotient-induced transitions are precisely those defining integral Rf_*; hence the compact-support and ordinary-image towers coincide, so their derived limits coincide. The E and Qbar functors are defined by rational and common-stage passage from these functors, which carries this identification to both field stages.

Cited nodes: thm-sf-comp-composition, fix-lem-exchanges, cor-cbc-proper-coincidence, def-weil-integral-rational-qbar-compact-support, def-weil-derived-direct-image.

### lem-sf-package-localization-projection-realization

Original step 7; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (3), localization triangle.

Clause (3), localization: take the all-stage open–closed triangle with its specified counit, unit and connecting map. At finite coefficients apply triangulated Rf_!. At the integral stage choose one compactification c of f and apply the exact R-linear compact-support reduction-tower functor T_f^c to this distinguished triangle. Its evaluations and strict transition maps are exactly Res_n Rf^c_{!,n}(K_n), naturally on morphisms. Apply the exact total derived inverse-limit functor to the resulting triangle in the derived category of towers. By the integral compact-support definition, the resulting functor is Rf_! on these bounded constructible objects, so its three vertices and arrows are the actual integral images. Exact rational transport gives the E-stage image triangle; exact common-stage descent and its triangulation give the Qbar-stage image triangle. Replace Rf_!j_! and Rf_!i_* by R(fj)_! and R(fi)_! using step 6 and proper coincidence for the closed immersion i. This gives the displayed triangle with the transported connecting map. The all-stage triangle and the comparison equivariance retain the stated Weil version. No coherent triangle is inferred from unrelated levelwise choices. A compactification of f exists by [thm-nagata-compactification]: Y is of finite type over k, hence quasi-compact, and separated, hence quasi-separated; X is Noetherian by the finite-type-over-Noetherian theorem, so the open immersion j is quasi-compact.

Cited nodes: prop-sf-open-closed-triangle-all-stages, lem-compact-support-direct-image-triangulated, lem-weil-compact-support-reduction-tower-functor, lem-weil-pbc-ringed-strict-tower-homotopy-limit, def-weil-integral-rational-qbar-compact-support, prop-weil-pbc-rational-transport, prop-weil-pbc-descent-functors, thm-weil-pbc-idempotent-complete-triangulation, fix-lem-exchanges, cor-cbc-proper-coincidence, thm-nagata-compactification, lem-weil-pbc-finite-type-over-noetherian.

Original step 11; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (5).

Clause (5) is the projection theorem applied to the given bounded constructible K and finite-Tor L. Its displayed map has the same direction as the map in this package. Its theorem includes naturality and the composition, compactification, reduction, scalar-extension and proper-coincidence comparisons on exactly these domains.

Cited nodes: fix-prop-projection-formula.

### lem-sf-package-base-change-domain-realization

Original step 8; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (4), proper ordinary base change.

Clause (4), proper ordinary base change: use bounded-below torsion proper base change at finite etale coefficients and its witnessed pro-etale version. For integral coefficients use the constructible-complete corollary, for E its raw rational transport, and for Qbar its common-stage theorem. All schemes in the datum are finite type over k, so the noetherian, finite-dimensional and bounded-relative-dimension hypotheses of these statements apply; the coefficient residue orders are invertible since ell differs from p. Use the specified completed exchange at the integral stage, not the exchange for discrete non-torsion small-etale modules. The finite-type-over-Noetherian theorem applies to Spec k (a field has only the ideals 0 and k), and finite dimension is the finite-type dimension lemma. Finite type gives quasi-compactness; separatedness gives quasi-separatedness because the diagonal is a closed immersion. The uniform fibre-dimension lemma bounds ordinary fibres, and field-extension dimension invariance applied to a finite affine cover of each fibre gives the same bound for geometric fibres, including empty fibres. The proper-base-change stability lemma makes f' proper, as required by the completed and rational proper-base-change statements.

Cited nodes: thm-weil-pbc-bounded-below, thm-weil-pbc-finite-level-proetale, cor-weil-pbc-constructible-complete, thm-weil-pbc-finite-extension, thm-weil-pbc-qbar, lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type, lem-fin-finite-type-fibre-dimension-bound, lem-weil-pbc-dimension-preserved-field-extension, lem-weil-pbc-proper-base-change.

Original step 9; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (4), smooth ordinary base change; domain clarification.

Clause (4), smooth ordinary base change: relabel the smooth-base-change square so its smooth f is the present g, its direct-image g is the present f, its input T is the present X and its output X is the present Y'. The finite etale theorem applies to bounded-below torsion inputs because the coefficient orders are invertible; the finite pro-etale theorem applies to bounded constructible inputs with their etale models. At O_E apply the completed theorem with compatible finite-reduction etale witnesses. At E use a specified admissible lattice; at Qbar use admissible common-stage representatives stable under finite overfields. These yield ambient completed isomorphisms. Retain the explicit uniform finite-level constructibility and interval bounds for a D^b_c conclusion; in particular the Qbar theorem by itself asserts no constructible landing. The exchange-identification statement ensures these are the maps in this package. The finite-type-over-Noetherian theorem applies to Spec k (a field has only the ideals 0 and k), and finite dimension is the finite-type dimension lemma. Finite type gives quasi-compactness; separatedness gives quasi-separatedness because the diagonal is a closed immersion.

Cited nodes: sbc-thm-bounded-below-derived-smooth-base-change, sbc-thm-finite-proetale-smooth-base-change, sbc-thm-adic-smooth-base-change, sbc-thm-e-coefficient-smooth-base-change, sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch, fix-lem-exchanges, lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type.

Original step 10; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (4), compact-support base change.

Clause (4), compact supports: use the finite torsion compact-support theorem and its witnessed finite pro-etale version for arbitrary base change. At integral coefficients apply the completed compact-support theorem to the compatible etale-origin reductions; at E apply its raw rational transport and at Qbar the descended exchange theorem. The isomorphism is on precisely the coefficient categories in those statements; no smoothness of the base-change map is needed. The finite-type-over-Noetherian theorem applies to Spec k (a field has only the ideals 0 and k), and finite dimension is the finite-type dimension lemma. Finite type gives quasi-compactness; separatedness gives quasi-separatedness because the diagonal is a closed immersion. The compactification required by the finite torsion and completed compact-support theorems exists by [thm-nagata-compactification], since Y is quasi-compact and separated (hence quasi-separated); its open immersion is quasi-compact because X is Noetherian.

Cited nodes: thm-cbc-finite-torsion, thm-cbc-finite-level-proetale, thm-cbc-complete-proetale, thm-cbc-finite-extension, thm-cbc-qbar, lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type, thm-nagata-compactification.

### lem-sf-package-normalized-orientation-perfect-duality

Original step 12; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (6).

Clause (6): invert the finite smooth-purity map gamma to obtain Rf^!L isomorphic to f^*L(r)[2r]. For integral inputs apply the adic reconstruction theorem to the normalized compatible finite family; for rational and Qbar inputs use the specified normalized integral lattice and purity transport. The smooth trace is the exceptional counit read through gamma, as specified in the smooth-trace definition. Reduction compatibility includes this trace, so the normalization and the comparison are retained. This uses the lecture-notes diagonal/deformation route already represented by the finite purity theorem.

Cited nodes: thm-pur-finite-coefficient-smooth-purity, thm-pur-adic-reconstruction, thm-pur-rational-and-qbar-purity, def-pur-smooth-trace, thm-pur-finite-reduction-of-purity.

Original step 14; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (7), point and site-perfect biduality.

Clause (7), independent point and perfect cases: apply the coefficient Frobenius lemma using derived evaluation at O_E, and ordinary exact duality at the finite and field stages. For a smooth pure-dimensional scheme and a site-perfect input, use the perfect-duality theorem: its orientation-induced formula identifies Verdier biduality with coefficient-perfect biduality. This supplies these special cases without deriving the general geometric statement from a site-perfect hypothesis.

Cited nodes: lem-weil-coefficient-frobenius, thm-sf-dual-perfect.

### lem-sf-package-verdier-coefficient-realization

Original step 13; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (7), Verdier exchange.

Clause (7), exchange: apply the unconditional constructible Verdier-exchange theorem with the structure morphisms of X and Y. It states the canonical natural map D_Y Rf_!M to Rf_*D_XM for every finite-Tor constructible M, including its coefficient and shift comparisons. This is the constructible version of the formal exchange named in the statement; it does not require the stronger unrestricted ambient exceptional-adjoint admissibility of the older interface.

Cited nodes: thm-sf-verdier-exchange.

Original step 15; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (7), geometric biduality and boundary comparison.

Clause (7), general finite coefficients: apply geometric biduality directly on D^b_ctf at A_{E,n}, where it asserts exact anti-equivalence and the natural evaluation biduality isomorphism. Apply the boundary-discharge corollary for the closed immersions of its locally closed pieces. The latter is a consequence available after geometric duality, not an extra hypothesis used to prove that duality.

Cited nodes: thm-fix-general-biduality, cor-weil-boundary-duality-discharge.

Original step 16; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (7), integral and field anti-equivalences.

Clause (7), integral and field coefficients: apply integral Verdier duality, which includes the equality of the integral bounded constructible and uniform finite-Tor domains, uniform dimension-dependent output bounds, evaluation-defined finite reductions and evaluation biduality. Rational Verdier duality gives the E-linear anti-equivalence by rationalizing those maps. Qbar Verdier duality descends these exact anti-equivalences, evaluations and double-dual maps through finite scalar extension and retracts. Thus the claimed evaluation-defined bidualities are the actual coefficient-passage maps.

Cited nodes: thm-coef-integral-verdier, thm-coef-rational-verdier, thm-coef-qbar-verdier.

### lem-sf-package-exceptional-coherence-realization

Original step 17; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Clause (7), exceptional adjunction.

The exceptional formula and adjunction in clause (7) are assembled with their coefficient domains. For the fixed compactification c=(j,p), p is proper and therefore finite type; since Y is finite type over k, so is its source. The finite-type dimension lemma supplies the nonnegative dimension bound required by the class-relative adjunction theorem (use zero for an empty compactification). At finite stages use the class-relative exceptional adjunction on bounded constructible objects together with the finite formula Rf^!=D_Xf^*D_Y and its quotient cocycle, units and counits. At O_E the integral adjoint theorem gives preservation, the same completed-pullback formula and the reduction-identified adjunction. At E use the rational operation theorem, and at Qbar use the descended constructible adjunction. None of these steps asserts an adjoint on arbitrary unbounded pro-etale objects. The compactification c exists by [thm-nagata-compactification], Y being quasi-compact and separated, hence quasi-separated.

Cited nodes: thm-sf-ambient-adjoint-class, lem-coef-finite-exceptional, prop-coef-integral-exceptional-adjoint, lem-coef-rational-operations, thm-coef-qbar-verdier, lem-kun-dimension-finite-type, thm-nagata-compactification.

Original step 18; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md, Final coherence sentence.

Apply the coherence theorem to precisely the proved comparison maps used above. Its identity, composition, exchange and projection equations, coefficient comparisons and field Weil equivariance give the final sentence. This only collects each established compatibility: it adds no arbitrary-base-change commutation for Verdier duality and does not enlarge any domain.

Cited nodes: fix-prop-coherence.

## Outstanding work

No stage-1 repair remains after successful dry run and delivery. The seven newly created unsplit tasks intentionally remain for future workers; no proofs of those tasks are claimed by this delivery.
