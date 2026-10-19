# Q19 stage-1 delivery: lem-pur-finite-dnc-normalization-reduction

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-finite-dnc-normalization-reduction.json`: statement node, now split in six steps. The complete statement is unchanged. Mathlib verdict: no match; logged grep, LeanSearch, Loogle and two LeanFinder phrasings were read.
- `citations.json`: one entry for every node cited by every proof step, using verbatim parts of the statement. Some entries quote a whole statement because multiple clauses are used together.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit file is changed: this is a created sublemma of the unit's finite-reduction statement, not its key node.

## Attachments

None. The exact id and the concepts sectionInvariant/deformationToNormalCone/dncInvariance were searched in the read-only slopmaster2 project. `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone` in `WeilConjectures/EtaleCohomology/Purity/Smooth/Deformation.lean:63` has `sorry` at line 68 and only states existence at one coefficient ring; its TODO explicitly omits uniqueness and base change. The finite-coefficient reduction compatibility is explicitly unavailable in the header of `Smooth/Transport.lean`. Neither states this item with every clause. No Lean was written or compiled.

## WANTED

None. All sources used are present. This is an agent-written cancellation argument based on already stated nodes; it is not presented as an additional theorem of the literature.

## What needed attention

The item's imported statement and hypotheses are retained. Its formerly empty proof needs two things beyond the existence of DNC isomorphisms: identification of the specified quotient coefficient maps, and compatibility with the actual coordinate-localization arrows. The existing node `lem-pur-dnc-coefficient-transport` supplies these for a cyclic initial ring, not directly for a general quotient of a ramified coefficient ring. I use it separately for R to A and R to B and derive the quotient square by the coefficient cocycle and cancellation. In particular I do not rename that existing theorem as a new node, nor assert its statement for an ineligible initial ring.

The common initial ring is R = Z/ell^n, where n is the original quotient exponent, not an incorrectly assumed integral value of n times a valuation. The equality ell = varpi_E a implies ell^n A = 0 even for ramified E and n not divisible by its ramification index. This avoids the unrelated disputed Kummer-level conventions.

No change of coefficient category is made: all the applications are at finite constant coefficients on the small pro-etale site and in the bounded constructible finite-Tor domains. No geometric-stalk argument for equality of arbitrary derived maps, no descent of arbitrary derived morphisms, and no SGA route is used.

## Not duplicates

No new nodes were created. `lem-pur-dnc-coefficient-transport` is reused: it treats Z/ell^N to an arbitrary finite target, with family/fibre and localization comparisons. The item instead treats A_{E,n} to A_{E,m}; this is obtained from two applications of that existing theorem. `det-sp-reduction-compatibilities` is reused only for its coefficient-composition clause (2); its purity conclusion (3) is not invoked. DAG statement searches across all chapters and blueprint_refs searches for DNC coefficient, coefficient-transport, coefficient localization and reduction-exceptional were read. The blueprint ancestor is `thm-pur-finite-reduction-of-purity`; the item's exact place is filled with its Step 3 DNC gluing passage and same_as remains empty.

## Review by Q19

I read the worker contract, delivery-errors B through E in full, the unit `sk-thm-purity-transport` and chapter record, GOAL.md and dag-sync.md. For the item I read the current main-20261015 `thm-pur-finite-reduction-of-purity.proof.md`, especially Step 3, and `sk-thm-dnc/thm-pur-dnc-invariance.proof.md`. I also read `sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md` (2), the proof of coefficient composition in `sk-lem-sp-reduction-compatibilities.proof.md` (2), and the counit-transpose statement in `sk-lem-sp-reduction-exceptional.md`. The argument follows their diagonal/DNC normalization route. There are no newly created source obligations.

Step 1: I opened the statements of `def-weil-l-adic-coefficient-extension`, `lem-weil-l-adic-extension-integers-dvr`, `lem-weil-valued-dvr-finite-quotients` and `det-sp-scalar-extension-functor`. The first defines the extended absolute value, maximal ideal and uniformizer. The second gives the DVR and finite residue field hypotheses needed for the third's finite quotient assertion. Membership ell in (varpi_E) proves the annihilator claim by taking nth powers; it requires no extra valuation theorem. The scalar-extension statement really gives the target-ring action, finite-Tor preservation without flatness, and the natural associator on morphisms. These are exactly the assertions used.

Step 2: I read the entire statement of `lem-pur-dnc-coefficient-transport`, including the normal-bundle and etale-localization clauses. Its source ring is cyclic: therefore it is used with R = Z/ell^n, once with target A and once with target B. Both are finite unital R-algebras by Step 1. The smooth-map, closed-section, separated finite-type and dimension hypotheses are those of the item; the normal-bundle comparison is explicitly included in the tool. I opened `lem-coef-finite-exceptional`: its counit formula identifies the quotient comparison as a mate, rather than merely some isomorphism. `det-sp-reduction-exceptional` defines the same counit mate. `lem-fix-compact-support-coefficient-change` says that the quotient comparison comes from the tensor comparison, and `det-sp-reduction-direct-image` pins this as the proper-counit mate followed by the open-extension comparison. These statements justify using the same map at a common compactification. The equality of the right-adjoint maps follows by the injectivity of the adjunction bijection. `lem-fix-operation-reduction` includes the pullback/tensor comparisons and their associativity/counit coherence, so the equality survives the section pullback. This checks the prescribed q maps, not just their isomorphism classes.

Step 3: I opened the statement of `det-sp-reduction-compatibilities`; clause (2) explicitly says that the exceptional comparison for a composite coefficient map equals the composite comparisons, with the associators displayed. It applies to smooth maps and arbitrary finite ell-primary rings, so both pairs and R to A to B satisfy its hypotheses. I cite the existing DNC transport node for the normal-bundle pair's eligibility as well. The pullback/tensor coherence statement of `lem-fix-operation-reduction` and the associator naturality of `det-sp-scalar-extension-functor` give the actual equation t_B = q Q(t_A). No argument from the proof of a cited node, and no purity compatibility conclusion, is used as a premise.

Step 4: The existing DNC transport statement explicitly gives delta_D t_D = t_D^N T_D(delta_R), and says its normalized chart comparison is the identity constant-family comparison. I opened `thm-pur-dnc-invariance` and checked that uniqueness is stated for precisely the eligible A_{E,r} coefficient rings. Thus its uniqueness identifies the tool's direct maps with the delta_A and delta_B in this item's statement. I do not apply that fixed-coefficient uniqueness statement to an arbitrary coefficient ring. This is the same normalized DNC arrow, with its direction checked against the inverse of the t=0 family comparison.

Step 5: I checked the domains of the displayed composites: each starts at Q T_A C_R(G), identified with T_B C_R(G), and ends in C_B(N). Naturality of the scalar associator is literally clause (4) of the cited scalar-extension statement. After the two DNC equations and the two coefficient cocycles are substituted, both sides have the same invertible right factor Q(t_A^G); cancellation gives the claimed square. This is elementary algebra on morphisms from earlier steps, not a separate lemma.

Step 6: I checked the localization clause in `lem-pur-dnc-coefficient-transport`, including its standard-pair value. It asserts that t_A and t_B respect these etale localizations. Apply the same coefficient cocycle also to the standard pair P. The two localization squares and naturality of the scalar associator yield the displayed chain, then cancellation of Q(t_A^H) gives lambda_B^H q_H = q_P Q(lambda_A^H) for each H = G,N. This proves the additional clause, which would not follow just from existence of comparisons or from arbitrary equality tests on stalks. The pullback/tensor comparison is cited where a base localization is made.

I checked small cases: for m = n, the coefficient comparison is the identity after unitors and the equations reduce to the same DNC map; for d = 0, the same section invariants and cocycles apply with shift zero; empty schemes have their unique zero objects and the same cancellation formulas; for ramified E with n smaller than the ramification index, ell already vanishes in A and the chosen Z/ell^n still maps to it. No division by a coefficient or by a rank is present, and no flatness of the quotient map is used.

Against B--E: statements stay self-contained and unchanged; no new proof-only or elementary nodes were created; every non-elementary fact used is a cited node statement; citations.json is checked as a literal substring of each statement; the non-elementary steps are all shorter than 2000 characters; no clause has been moved into a newly named copy; the reused initial-ring transport is a strictly prior tool. I checked dependency reachability from the existing transport and coefficient-composition tools: none reaches this item, so they introduce no cycle. The generic coefficient tools outside the unit's route are declared in split_report.tool_uses with the precise reason for each. The underlying mathematical route remains the unit's DNC finite-reduction step. There are no statement disputes or missing clauses.

## What could not be finished

Nothing in the mathematical split. The server dry run and push are recorded below once complete.
