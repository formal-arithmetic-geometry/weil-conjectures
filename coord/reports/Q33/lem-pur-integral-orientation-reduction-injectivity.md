# Q33: lem-pur-integral-orientation-reduction-injectivity

## Files written

- dag/nodes/sec-poincare-duality/lem-pur-integral-orientation-reduction-injectivity.json: statement, now split; no Mathlib match for the geometric statement.
- citations.json: one entry for every step/node pair; the quotes are verbatim complete statements of the cited live nodes, allowing the reduction and domain clauses to be read together.
- No new nodes; no new Mathlib leaves. The existing leaf lem-weil-pbc-derived-single-fully-faithful supplies exactly the required general categorical fact.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for orientation/reduction, integral orientation, and rank-one notions. The nearby EtaleCohomology/Purity/Smooth/Adic.lean declaration exists_iso_realization_twistShiftPullbackLevel supplies reconstruction with assumed normalized systems and finite compatibility; it does not state this actual-proetale-tower Hom injectivity statement. No completed declaration states all clauses here.

## WANTED

None. The necessary blueprint sources and existing DAG statements are present.

## Findings and changes

The item was unsplit, with no earlier sandbox proof/report. No released repair note exists. The statement, statement dependencies, original source and blueprint provenance are retained. No statement dispute was found. The chapter is sec-poincare-duality and unit sk-lem-finite; I read their records and the three-level rule. This item is a generic comparison used by the prop-weil-operations descendants, not the unit key theorem, so no unit record is changed. The smooth-purity diagonal/tower route is retained. No SGA source is used.

The important restriction is that arbitrary derived tower evaluations need not detect morphisms. Here both ends become the same sheaf tower in one common degree after conjugating by the specified actual tower orientation. The proof writes that operation and uses full faithfulness in both the tower category and each coefficient-module category. It never replaces actual derived towers by a diagram in separate derived categories. Nor does it assume that h is an isomorphism.

Fresh searches were executed with the required msearch.py wrapper and their results read. LeanSearch returned smooth integration and real-linear orientations, which have different objects. The two LeanFinder phrasings returned chain-complex extensionality and Ext descriptions; neither constructs this geometric comparison. Loogle DerivedCategory.singleFunctor returned its full and faithful instances. I read Mathlib/Algebra/Homology/DerivedCategory/FullyFaithful.lean lines 29–54: the instances at lines 37 and 45 are already recorded in lem-weil-pbc-derived-single-fully-faithful. The wrapper grep found no purity/tower or orientation/reduction match. Existing imported searches were preserved; all fresh exact queries are recorded from searches.jsonl. No search was invented and no unavailable result was called absence.

Before considering a new node I searched the whole DAG by tower/degree-zero/rank-one/component-detection concepts and ran blueprint_refs.py searches for tower sheaves, fully faithful, and orientation reduction, as well as its ancestor query. The strict-line-heart-assembly node constructs a tower orientation from compatible finite isomorphisms; our item assumes that orientation, so using or reproducing its lifting assertion is unnecessary. The source-tower comparison and single-functor leaf already exist. Component extensionality and cancellation are elementary steps, so I created no nodes for them. No split step exceeds 2000 characters.

## Unfinished work

None in the one-level split. The existing cited nodes retain their own proof obligations.

## Not duplicates

No new nodes, hence no new/existing-node pairs. Reused the existing source reduction comparison, tower orientation, Hom bijection, tower category and derived-single leaf.

## Review by Q33

I read the item's source, main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, especially clause (1)'s degree-zero rank-one tower uniqueness. I also read the normalization/bijections/purity source of det-sp-integral-adjunction-bijection and prop-weil-operations.proof.md at the item's blueprint ancestor. The source's tower orientation is used as a whole-tower isomorphism, not merely as separate finite isomorphisms. There are no new nodes needing independent source attribution.

Step 1: I opened lem-sp-twisted-pullback-reduction-tower and checked that its statement supplies an isomorphism of entire derived towers, including all quotient transitions, for arbitrary m,s. With K the coefficient unit, m=d and s=2d it supplies q; pullback of the unit is the unit. Its hypotheses exactly match the finite extension, separated finite-type schemes, smooth separated pure-dimensional map and completed integral category already fixed by the item. The common Tor bound on the unit and its twisted shift is a singleton interval; d is finite. I read def-coefficient-twists-detailed: its nonnegative twists are tensor powers of module sheaves, so L is an actual sheaf tower. I read det-sp-tower-gamma (1): it gives the required actual tower isomorphism a with precisely these finite orientations. These are the statements copied in citations.json, not assertions borrowed from their proofs.

Step 2: I read det-sp-integral-adjunction-bijection's displayed chain and its explicit naturality in M,K. Applying contravariant naturality to u:T→H1 and the identity proves beta(u)=lambda r(u), with the correct direction. I read det-sp-coefficient-towers-abelian (2): evaluation is exact and is the specified derived level functor. Thus evaluating the composite gives the ordinary reduction with exactly the target comparison fixed in the item's definition of rho. No extra compatibility theorem is assumed. Delta is used as the fixed invertible comparison; the unique-adjoint theorem is already among the unchanged statement dependencies.

Step 3: Equal finite reductions give equal evaluated b by Step 2. I checked the types: q^{-1}:L[s]→rT, b:rT→V, a^{-1}:V→L[s], so their composite is an endomorphism of L[s]. The definition node def-weil-triangulated-category explicitly makes shifts autoequivalences. Removing s preserves and reflects equality; evaluation commutes with this literal complex shift. This is an elementary manipulation of the fixed isomorphisms, not a claim that all derived evaluations are faithful.

Step 4: I opened det-sp-coefficient-towers-abelian (1), which says the strict coefficient-tower category is Grothendieck abelian. The existing derived-single leaf explicitly gives a bijection of sheaf Hom and degree-zero derived Hom for every abelian category, so it applies first to towers, then to the abelian module-sheaf category at each n. The latter application is needed: equality in the derived level category must imply equality of the actual sheaf maps. I read sk-def-sp-coefficient-towers: a morphism is exactly a compatible family and composition is componentwise. Thus equal z_n imply equal z by that definition; no separate lemma or new node is warranted. This is the full elementary component argument after the non-elementary fully-faithful input.

Step 5: I checked that only injectivity of the stated bijection and inverses of the fixed q,a,delta are used. None of these cancellations uses an inverse of h or h'. The retained Hom domain and target are the ones in the item.

I tested d=0 (no shift, identity smooth map allowed), an empty X (all Hom sets reduce to the unique zero map), the zero h, and a nonunit scalar multiple of an orientation over a geometric point. The proof works for the noninvertible and zero maps as well as isomorphisms. Finite ramification causes no mismatch: the existing entire-tower comparison explicitly treats the ell^n levels by cofinal uniformizer powers. Nonproper f is allowed throughout; no properness or additional base-change assumption has been introduced. I checked delivery-errors B–E: statements/dependencies preserved; no statement-only-node proof leakage; no duplicate or restated-clause node; all non-elementary inputs are cited and their statements actually give the required facts; no source-tag substitution for a node; no ill-typed transports or hidden normalization assumption. Off-unit comparison uses are declared as generic tools in split_report.tool_uses, while the Mathlib shift and single-functor tools are leaves.
