# Stage-1 report: lem-sfb-etale-proetale-ringed-square-realization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-proetale-ringed-square-realization.json: item, statement, split into five proof steps. No exact Mathlib match.
- citations.json: every step citation, with verbatim text from the cited statement.
- searches.jsonl: actual search-command records, retained and read.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. The whole WeilConjectures tree was searched for the item tag and ringed-square terminology. The existing comparison functors in SixFunctors/ProEtale/Comparison/Defs.lean give inverse-image adjunctions but do not state every clause, in particular the constant-ring square and equality of the specified derived comparisons. They are not an attachment.

## WANTED

None. All sources used were read in the supplied literature.

## Statement correction and other findings

STATEMENT-DISPUTED: the last sentence introduced a:F_Xu ≅ vF_Y in ordinary uncompleted derived categories and called it the comparison of lem-weil-pbc-comparison-pullback. That cited statement is an ordinary sheaf comparison, not itself a natural transformation on derived categories. The domains do not type-check literally: a module sheaf and a derived object are different objects in different categories. I repaired this by specifying that a is its termwise localization. This retains all original hypotheses and the full equality of specified natural isomorphisms, rather than silently treating existence of an isomorphism as map equality. The source's geometric square and the standard exact localization construction give the intended reading.

No added finiteness, qcqs, nonempty, field, invertibility, boundedness or cartesianness assumption. In particular, 09A6's qcqs hypothesis belongs to its pushforward theorem and is not needed for the geometric square preceding it (09A5).

The split reuses the existing general results; it does not create nodes restating the item's clauses. Blueprint searches for constant ring, ringed square and comparison-pullback, the DAG statement/title searches and the ancestor query located the general constant-module theorem, ordinary comparison and existing localization tools. There is no blueprint node stating this full normalization. The unchanged ancestor is det-thm-sfb-proper-base-change-finite, its transport and paragraph (3). This is not the key node of the unit, so no unit realization file is changed.

## Not duplicates

No new nodes were created. Candidate reuse decisions: lem-pe-constant-left-module-inverse-image provides arbitrary geometric constant-ring preservation and exact scalar transport; lem-weil-pbc-comparison-pullback gives the ordinary etale/proetale comparison; lem-weil-pbc-ringed-topos-square-transport is about equivalences of presentations (nu need not be an equivalence); lem-weil-pbc-ringed-square-localization concerns a cartesian scheme square with coherent coefficients, whereas the current mixed-site square is not assumed cartesian. The latter two were therefore not substituted for this item.

## Mathlib results read

Actual commands used LeanFinder twice with different formulations, LeanSearch, Loogle and grep. No search was invented. Loogle's SheafOfModules.pullbackComp and conjugateEquiv_pullbackComp_inv were read in Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:167-182; these are generic module pullback compositors. LeanSearch's constantCommuteCompose was read in Mathlib/CategoryTheory/Sites/ConstantSheaf.lean:184-191; it concerns forgetting coefficients, not the four-site square. The second LeanFinder returned mapDerivedCategoryFactors, read in Algebra/Homology/DerivedCategory/ExactFunctor.lean:36-45. These last generic tools already have DAG nodes. None specializes in one line to the whole item, since the constant-ring and specified map identifications still require the argument in steps 1-4. Other returned hits concern discrete condensed modules, free pullbacks and structure-sheaf morphisms, not this theorem. Grep returned zero hits for its recorded pattern. The earlier Q87 searches in the live item were preserved as historical records, not represented as searches run by Q131.

## Review by Q131

I read the current chapter and unit records and the main-20261015 unit statement and finite-case proof. The relevant route is finite-coefficient transport in paragraph (3). I read proetale.tex, section-morphism (09A5), especially the displayed square immediately before lemma-morphism-comparison (09A6): it gives the comparison for arbitrary scheme maps. I also read sites.tex example-constant-sheaf (0H7J) and proposition-functoriality-algebraic-structures-topoi (00YV), including the fixed-ring scalar-endomorphism argument; sites-modules.tex lemma-pullback-module (03D2), lemma-adjoint-push-pull-modules (03D3), and section-constant (093I); categories.tex lemma-transformation-between-functors-and-adjoints (0B65); and derived.tex lemma-right-derived-exact-functor (015F). The ring/module normalization argument is my explicit assembly of these sources, hence proof_origin.by is agent. There are no new nodes needing further sources.

For step 1 I opened the statement of lem-pe-constant-left-module-inverse-image: it explicitly supplies a canonical constant-scalar-preserving ring isomorphism and an exact module lift for any geometric morphism, including nu. I used lem-weil-pbc-comparison-pullback for the specified underlying geometric square and lem-weil-pbc-constant-sheaf-maps-global-sections for uniqueness of the adjunct maps. The latter assumes a final object: the small scheme sites have their identity scheme as final object. Thus it applies also for X empty. The coefficient universe is the common one fixed in the item.

For step 2 the ring equation is checked on constants after identifying the source with the constant ring by the already established invertible left path. Naturality c_R L1(a) = L2(a)c_1 verifies the right path on those same constants; the terminal-object comparison is unique. The cited constant-sheaf Hom bijection gives equality, rather than a mere local heuristic. Naturality with ring operations gives a ring map. def-weil-pbc-ringed-topos-morphism supplies exactly the interface being checked, and no claim about topos cartesianness is imported from it.

For step 3 the equivalence lemma explicitly identifies fixed-ring sheaves and constant-ring module sheaves with their underlying additive sheaves. The constant inverse-image lemma supplies transported scalar actions and exactness, while lem-weil-pbc-ringed-topoi-derived-pullback states the actual tensor extension formula for ordinary module pullback. The written tensor maps are mutually inverse by balancing. The formula is r tensor m mapped to c_w^{-1}(r)m in the inverse-image module; all terms therefore have the correct scalar ring. Insertion of 1 is invertible since c_w is an isomorphism. Naturality with each lambda_a, with +, and with 0 proves the operation equations; a product comparison is fixed by its two projections. This is the elementary verification attached to the existing non-elementary constructions, not a new lemma hidden under the word transport.

For step 4 I read the whole statements of the composite adjunction and conjugate-isomorphism unit-equation nodes. The latter gives exactly uniqueness for R1(c) eta1 = delta eta2. Both composites of direct images evaluate to N(X times_Y W), with the same constant scalar action. The normalized module theorem says the forgotten units are the abelian units; the comparison inclusion uses the same base-change objects and arrows. Hence the geometric and module comparisons satisfy the same unit equation. Applying the cited uniqueness result and faithful forgetting establishes equality with the specified fixed-coefficient comparison. It does not take a normalization theorem from an uncited node's proof.

For step 5 I read both exact-derived node statements and the localization universal property. The first says an exact functor takes quasi-isomorphisms to quasi-isomorphisms and is computed termwise on every complex, the second identifies this with the actual left derived functor. The localization node explicitly states unique descent of natural transformations, preservation of composition and equality after precomposition with Q. Thus termwise b and b inverse descend to inverse natural isomorphisms on the entire unbounded category. The direction theta:vF_Y to F_Xu is opposite to a:F_Xu to vF_Y, so theta is a inverse. The corrected statement now names the localization being compared. No K-flat replacement, boundedness shortcut, per-cohomology comparison or completion is used.

I checked B-E of delivery-errors point by point: no new statement-only nodes to hide proofs or duplicate clauses, actual queries and results retained, every citation opened and quoted verbatim, all proof uses in proof_deps, explicit map formulas instead of unexplained transports, and no SGA reference. Every step is below 2000 characters. Small cases checked: A the zero ring; identity p; X empty; Y empty (which forces X empty); disconnected schemes with nonconstant locally constant sections; and unbounded complexes. Constant-ring uniqueness is through the sheafification adjunction, so it does not incorrectly assume all sections are globally constant. Empty sites give zero ring/module objects and all maps are the unique maps; no nonzero-ring hypothesis is used. Identity p makes the geometric/direct-image comparisons identities and the final inverse equality consistent.

## Unfinished work

None within this one-level split. Existing general dependencies retain their independent DAG statuses. Server dry run and push results are recorded by the delivery tool.
