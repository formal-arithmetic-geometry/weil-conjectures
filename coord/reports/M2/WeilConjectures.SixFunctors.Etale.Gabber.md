## What changed

The Gabber module now proves two of the four sorries on the current base, with unchanged signatures:

- `AlgebraicGeometry.Etale.bijective_cohomologyMap_zero_of_henselianRing`: identify the quotient-spectrum image with V(I), apply the already proved Stein connectedness theorem to every finite cover, apply the new general abelian sections criterion, and conjugate the resulting sections bijection using the already proved `cohomologyMap_zero_eq_globalSectionsUpperStarMap` and the canonical H^0/global-sections identifications. The geometric connectedness argument and both directions of the bijection are real Lean.
- `AlgebraicGeometry.Etale.exists_cohomologyMap_eq_zero_of_isLimit`: obtain a cohomology colimit cocone from a new categorical comparison lemma. Use injectivity of its limit isomorphism, Mathlib `IsColimit.eq_iff'`, compatibility of the stage restriction maps, and the stage isomorphism to extract a zero class at a finite stage. This proves the elementwise vanishing conclusion from a colimit universal property.


Added proof imports are Mathlib's concrete filtered-colimit equality API, HenselianConnectedness, the proved degree-zero pullback formula, and the two new modules. No public import, public definition, existing signature, or target changed. The existing Gabber induction stays intact. The relevant node proof records now describe the implemented arguments. All three sandbox modules compile with no errors or warnings through lcompile; the final delivery dry run supplies the server/preflight checks.

## Proved and sorry left

The two declarations listed above no longer contain sorry. This is a stage-3 reduction, not a claim that their transitive axioms are already closed: the new geometric comparison lemmas and preexisting infrastructure still rest on named sorries.

Original sorries left untouched in Gabber:

- `AlgebraicGeometry.Etale.exists_isFinite_cohomologyMap_eq_zero_of_henselianRing` — `lemma-weil-pbc-finite-cover-killing`.
- `AlgebraicGeometry.Etale.exists_mono_map_eq_zero_of_henselianRing` — `lemma-weil-pbc-gabber-effacement`.

New sorries, each the entire proof of one public theorem in its own module:

- `AlgebraicGeometry.Etale.exists_cofiltered_etale_cohomology_cocone` — `lem-weil-pbc-cofiltered-etale-cohomology-cocone`, in `Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyCocone`.
- `AlgebraicGeometry.Etale.isIso_abelian_globalSectionsUpperStarMap_of_finite_connected_closed_intersections` — `lem-weil-pbc-etale-abelian-h0-finite-connected-criterion`, in `Sheaf.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion`.

Each new node and docstring contains its source and complete construction/proof in words. The colimit lemma quantifies over all source classes and supplies a full colimit universal property, stage groups and comparison isomorphisms; it does not assume that a class vanishes. The abelian sections criterion concerns an arbitrary qcqs scheme and a closed immersion with a finite-cover topological condition; it has no henselian-pair or cohomology hypothesis. Thus neither is the original theorem renamed or a vanishing/bijectivity hypothesis repackaged. Edge cases checked mathematically include degree zero, the zero sheaf, empty schemes, one-object index categories, I=0 and the zero coefficient ring. Cofilteredness includes nonemptiness, and IsConnected includes nonemptiness.

## No longer needed

No inherited public import was removed: these are part of the module's exposed interface. Every newly added proof import is used.

- The Gabber comparison proof no longer needs `lemma-weil-pbc-etale-degree-zero` or its module `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero` as an input. Its affine degree-zero case is assembled from Stein connectedness and the general abelian sections criterion. The proper degree-zero theorem remains needed elsewhere in the project.
- `def-weil-pbc-cohomology-pullback` and `def-weil-pbc-etale-cohomology` were also removed as separate proof dependencies of `prop-weil-pbc-gabber-pair-comparison`: the degree-zero comparison lemma packages their compatibility. Their definitions remain used in the unchanged signatures and are not claimed to be globally pruned.
- `lem-weil-pbc-pullback-cohomology-long-exact-ladder` / `Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder` is unnecessary for the existing induction: its naturality is already proved by the local `cohomologyMap_comp_extClass` and `cohomologyMap_comp_mk₀`, and its exactness is Mathlib's Ext sequence. The node now records the generic Mathlib leaf `lem-weil-pbc-ext-long-exact-second-variable` instead.
- `lemma-weil-pbc-etale-cohomology-continuity` / `Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity` is no longer a direct input to finite-stage killing. Its torsion-only signature does not fit that theorem. The replacement cocone node uses the arbitrary-abelian-sheaf directed continuity node `lem-weil-pbc-etale-cohomology-limit-of-schemes`, plus cofinal reindexing.
- The approximation proof landed while this worker was active. Its existing imports `Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass`, `Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues` and `Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality` and its proof are preserved verbatim. My independently compiled duplicate approximation proof and private naturality helper were removed from the delivery. They add no further work or dependencies.

No blueprint unit statement or unit proof step was bypassed. The unit record `sk-thm-p1` stays unchanged. Generic categorical/cohomological tools of other units are used as tools, especially directed-to-cofiltered reindexing and Mathlib Ext exactness.

## Where the brief, the DAG or earlier work was wrong

The assignment started from a module with five sorries. During this session, the read-only clone refreshed to a newer base where the constructible approximation had already been proved. I preserved that landed proof instead of replacing it, dropped my duplicate helper, and rebased the scope of this report to the current four-sorry base. The delivery closes degree zero and finite-stage killing, leaving the two positive-degree sorries unchanged. No approximation node is delivered.

The finite-stage-killing Lean theorem has no torsion hypothesis. Its original dependency `cohomology_continuity_of_isLimit` requires `F.IsTorsion`; it cannot be applied to arbitrary G. Stacks 09YQ is for arbitrary abelian sheaves, so the new categorical comparison takes that route without adding a hypothesis.

The existing finite-connected sections criterion is stated only for `ModuleCat Λ`, with Λ at the prescribed coefficient universe. It does not directly apply to the abelian sheaf G in Gabber's degree-zero statement. The new abelian criterion isolates exactly this missing coefficient case, following the same spectral/Gabber route; the quotient-spectrum connectedness and H^0 transport are proved here.

The degree-zero Gabber declaration previously had no separate matching node in the module's audit. Its proof is now described in the first step of `prop-weil-pbc-gabber-pair-comparison`.

The two untouched positive-degree lemmas need further glue: finite-cover killing of an arbitrary constructible module class is not the existing finite-constant-sheaf killing theorem alone; and the general-Λ effacement theorem cannot simply apply the finite-Λ approximation lemma, since it has no `[Finite Λ]` assumption. No coefficient hypothesis was added and no statement was weakened.

## New nodes

`lem-weil-pbc-cofiltered-etale-cohomology-cocone` is the categorical comparison part of finite-stage killing. Its node records the canonical stage diagram, cofiltered-to-directed reindexing, the constant compatible limit sheaves, Stacks 09YQ and cofinal transfer, followed by pullback compatibility. The original Gabber module proves the separate zero-at-a-stage argument.

`lem-weil-pbc-etale-abelian-h0-finite-connected-criterion` is the sheaf-theoretic criterion part of the affine degree-zero comparison. Its node records spectral restriction on finite covers, Gabber's Zariski-to-étale sections criterion, and the natural passage from set-valued to abelian sheaves. The original module proves the henselian connectedness condition and the H^0 conjugation.

Both are in chapter `sec-proper-base-change`, unit `sk-thm-p1`, and each is stated in its own new Sheaf module with exactly one theorem. No change record is needed: all existing interfaces and node statements are unchanged. Sources were checked at the primary Stacks pages https://stacks.math.columbia.edu/tag/09YQ, https://stacks.math.columbia.edu/tag/09ZF and https://stacks.math.columbia.edu/tag/09ZG. Recorded Mathlib searches include unavailable LeanSearch queries, actual LeanFinder/Loogle results and local Mathlib grep; no unavailability was treated as an absence verdict.

## Second reading by M2

1. **Existing interfaces: pass.** Compared the full Gabber diff with the current
   repository version and ran the delivery declaration comparison: no existing
   statement changed, no definition changed, and no declaration was removed or added
   in Gabber. Only the two reported proof bodies and five plain proof imports differ.
   The already landed constructible approximation and the induction are unchanged.
2. **Proof and axioms: pass.** Compiled all three modules in import order through
   lcompile, with no errors or warnings. The only direct sorries are the two reported
   untouched Gabber theorems and the two named new theorems. No forbidden declaration
   form or hollow definition was introduced. A separate scratch import checked
   `#print axioms` for both repaired declarations, both new lemmas, and the final
   Gabber comparison: only propext, Classical.choice, Quot.sound and sorryAx occur.
   This is a reduction with open dependencies, not an axiom-free final proof.
3. **Split statements: pass.** Read the Lean signatures, node statements and complete
   docstring constructions against Stacks 09YQ, 09ZF and 09ZG. Cofilteredness supplies
   nonemptiness and common predecessors, so the composite map to S is independent
   of the stage; a connected constant diagram has the required colimit. The finite
   cover condition applies to closures of points and includes nonemptiness via
   IsConnected. Checked zero sheaves, empty schemes, degree zero, the identity closed
   immersion and singleton index categories. Neither split is a renamed vanishing
   or henselian cohomology-bijectivity statement. Independent LeanFinder searches
   using specialization/sections and inverse-system/colimit wording, together with
   rg over both library roots, found no exact existing statement. The nearby module
   criterion fixes ModuleCat coefficients; the nearby continuity statement is
   torsion-only, and the general directed continuity theorem requires the diagram
   construction and cofiltered reindexing isolated here. Neither new proof can be
   closed in a few minutes from those interfaces.
4. **Route, imports and pruning: pass with report correction.** The degree-zero proof
   uses Stein connectedness, the abelian sections criterion and the proved H^0
   transport formula. The finite-stage proof uses Mathlib filtered-colimit equality,
   with the smaller diagram-index universe handled explicitly. All added imports
   are plain imports and used; no new proof-only public import was introduced.
   Compared the old/new dependency sets and checked the unchanged sk-thm-p1 realized
   record: no unit statement or step is bypassed. Added the two omitted definition
   dependency IDs to No longer needed, distinguishing dependency-edge removal from
   pruning their still-used definitions.
5. **DAG agreement: pass.** Read all four delivered node files; existing node changes
   are limited to proof, proof_deps and proof_origin. The proof-step uses have exactly
   the recorded union, and the new nodes have sources, searches, origin, provenance,
   chapter/unit and verbatim normalized Lean signatures. The cocone node records
   geometric continuity plus reindexing; the original node records the separate
   elementwise zero argument. The sections node records the coefficient bridge;
   the original node records the henselian application and H^0 transport.

Changed only this report: completed the removed-dependency inventory and recorded
this independent second reading. No Lean or node repair was necessary.
