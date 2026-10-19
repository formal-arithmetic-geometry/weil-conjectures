# Stage-1 report: thm-sf-verdier-exchange

## Files written

- `dag/nodes/sec-six-functors/thm-sf-verdier-exchange.json`: existing statement, split into four steps; no new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quote for every citation of every proof step.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 source by the exact item id, blueprint tag, `verdierExchange`, and the Verdier-dual declarations. `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_dualizingComplex` (TensorHom.lean:380) and `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerShriek` (TensorHom.lean:397) have sorry-free bodies. They give `Nonempty` isomorphisms for finite coefficients on ordinary small etale derived categories with explicit compactification hypotheses. They do not give the item's full four-stage canonical natural exchange and its coefficient/shift clauses. The package field only reuses these declarations. No exact attachment was found. Upstream master is not used as evidence of a finished proof.

## WANTED

None. The source for the item is available in the current blueprint. This is a formal consequence of the specified six-functor datum, not a new geometric existence theorem requiring a Stacks tag.

## Errors and corrections

The earlier sandbox used `thm-sf-comp-composition` at every coefficient stage, but that node's current statement is explicitly finite-level and etale-origin. The repaired proof uses the composition comparison supplied by A4 of the assumed six-functor datum at every coefficient stage. This is the same composition/mate route as the current source, whose Step 1 expressly invokes A4. No finite-level theorem is silently promoted to integral or field coefficients.

The earlier citation of A6 to justify the dualizing object's finite-Tor membership did not quote the needed assertion and would obscure the source's independence from biduality. Step 1 now starts with the coefficient unit (Tor interval [0,0], uniformly over the integral reductions), then applies the finite-Tor-typed right adjoint in A1. A6 is unused.

The existing Mathlib leaf `lem-sf-mate` still includes the obsolete explanatory parenthetical identifying the A1 adjoints with restrictions of strong ambient adjoints. This is inconsistent with the current constructible-adjoint convention. I have not edited another worker's node. The actual premise used is its three explicitly specified finite-Tor adjunctions, and its conclusion is the generic conjugation of their composition comparison. Its recorded Mathlib declaration `CategoryTheory.conjugateIsoEquiv` (Mates.lean:425–435, read directly) takes only two adjunctions and an isomorphism of left adjoints, with no ambient/geometric premise. The repaired proof explicitly specifies the constructible adjunctions, so no strong ambient hypothesis is assumed or inferred. This dependency wording should be corrected by its owner.

The imported item's opening depended on the setting of another node. I retained the earlier self-contained expansion: global coefficient parameters, separated finite-type schemes, structure maps, and constructible exceptional inverse image. The formula now distinguishes the coefficient unit Lambda_s. `def-sf-pf` and `def-weil-finite-tor-amplitude` supply the dual and finite-Tor notation. This makes the intended setting explicit; it does not change the coefficient categories or add ambient admissibility. The blueprint provenance parenthetical and `fix-cor-verdier-exchange` dependency were omitted because that node restates the exchange; the proof here carries the composition-mate/tensor–Hom argument itself.

## Review by Q17

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the three levels and tool rule in SETUP.md, delivery-errors B–E in full, GOAL.md and dag-sync.md, the chapter and unit records, and the current main-20261015 statement and proof of this item. The imported `blueprint_update` agrees with that current source; all imported blueprint/update metadata is preserved. The old master proof path claimed by the earlier report is absent, so the proof-step and proof-origin references now point to the actual current proof file. I also read TensorHom.lean:330–404 and the statements of every cited node. No new node was created, so no source or search for a new child is outstanding.

For Step 1 I checked `def-weil-finite-tor-amplitude`, `def-sf-datum`, and `def-sf-pf`. The first gives the uniform integral-reduction condition and the two field-stage equalities; the second imposes A1 on the finite-Tor domains; the third identifies the unit and Ra_T^! of that unit with omega_T. Tensoring the rank-one unit with a degree-zero module is the identity, so its Tor interval is [0,0] at every finite level, independent of n. The point's unit at the other stages is the specified integral/rational/common-stage unit. Applying the given typed right adjoints therefore supplies omega_X and omega_Y in the required categories. Applying the given typed left adjoint supplies Rf_!M. This is a direct domain check in the axiomatic setting, not an assertion that a definition proves the concrete geometric preservation theorem.

For Step 2 I checked the entire A1/A4 context of `def-sf-datum`, the composition-conjugation conclusion of `lem-sf-mate`, and the formula in `def-sf-pf`. Both structure maps are separated finite type because X and Y are so over k, and a_X=a_Y f is their specified composite. A4 supplies Ra_X! -> Ra_Y! Rf!, conjugation gives Ra_X^! -> Rf^! Ra_Y^!, and inversion gives the direction needed for c_f. Evaluating at Lambda_s is legitimate by Step 1. The categorical Mathlib source confirms this conjugation needs only these three adjunctions, which resolves the erroneous ambient parenthetical as explained above. I checked the finite-only composition node as well and removed its invalid use rather than changing it.

For Step 3 I checked both hypotheses of `lem-sf-tensor-hom`: M is the input in the statement and N=omega_Y is Step 1's finite-Tor object. Its displayed isomorphism has the reverse of the desired first-arrow direction, so the proof explicitly inverts it. Applying the actual functor Rf_* RHom(M,-) to the isomorphism c_f supplies the second arrow. The two endpoint identifications are exactly `def-sf-pf`'s Verdier-dual formulas. No definition of ordinary tensor dual is substituted for Verdier duality.

For Step 4 I checked the explicit naturality/coefficient/shift clauses in `lem-sf-tensor-hom`, the pasted-unit/counit assertion of `lem-sf-mate`, and A5's stage-specific compatibility in `def-sf-datum`. The proof writes the required argument: a permitted coefficient comparison carries the units, composition map and counits in the conjugate expression to their counterparts, so substituting gives the same c_f. This is why the square for the second arrow commutes. It does not assert arbitrary base-change compatibility of Verdier duality. A shifted first variable applies the same degree-zero c_f under RHom(M[r],-)=RHom(M,-)[-r]; the first arrow's shift clause then gives the result for the composite. Naturality is the same bifunctorial calculation.

I checked B–E against the final files: every object is introduced; each statement dependency defines the notion it is used for; every non-elementary proof input is a cited existing node; every use has a verbatim statement quote; the steps carry the argument rather than relabeling the conclusion; and no new node duplicates a clause, an elementary calculation, a blueprint node or a Mathlib result. I searched the whole blueprint and DAG for Verdier exchange, obtaining the existing `fix-cor-verdier-exchange` and `sk-thm-sf-verdier-exchange`, recorded in `same_as`. The current unit route is preserved: composition, its mate, and tensor–Hom. The item is not the separate sketch key node, so no unit record is edited.

Small-case checks: for f=id, A4 and the pasted adjunctions give the identity mate and the exchange is the usual identity internal-Hom comparison; for M=0 both endpoints and arrows are zero-object isomorphisms; empty X causes the same zero-object case. At n=1 and at non-field A_{E,n} the argument uses the free coefficient unit, not a claim that every constructible object has finite Tor amplitude. Integral coefficients use one uniform interval for the unit's reductions. The field stages remain the specified rationalized/common-stage categories and are never replaced by discrete coefficient sheaves or by condensed module objects. No purity, SGA, general biduality or arbitrary ambient right adjoint is used.

The recorded earlier searches have matching entries in the sandbox's existing msearch log; I ran fresh semantic searches with two phrasings, grep, and Loogle as well. The semantic hits concern ordinary sheaf adjunctions, exponentiable morphisms or linear/order duals. The successful Loogle query finds generic conjugation, already carried by the existing Mathlib leaf, not the full geometric theorem. The Mathlib source was read at that match. No search was invented and no failed service was recorded as a negative result.

## Not duplicates

No new nodes were created.

## Unfinished

No mathematical step remains for this one-level split. Server dry-run validation follows; delivery is reserved for the fresh second reader.

## Second reading by Q17

- Item statement: checked against the current main-20261015 blueprint statement and its `def-sf-datum`, `def-sf-pf`, `def-weil-exceptional-inverse-image`, and `def-trf-admissibility` definitions; all coefficient, scheme, morphism, constructible-adjoint, dualizing-object, naturality, and compatibility clauses are present with no ambient-admissibility hypothesis.
- Step 1: checked against the finite-Tor definition, A1 of `def-sf-datum`, and the unit/dualizing notation of `def-sf-pf`; the degree-zero free unit has interval [0,0] at finite and integral stages and the field categories are defined as constructible, so the domain check is valid and elementary.
- Step 2: checked against A1 and A4 of `def-sf-datum` and `def-sf-pf`; the explicit Hom-adjunction chain now constructs the mate from the all-stage A4 comparison, so it does not apply the finite-level `thm-sf-comp-composition` theorem at integral or field coefficients.
- Step 3: checked against both hypotheses and the displayed direction of `lem-sf-tensor-hom` and the Verdier-dual notation of `def-sf-pf`; inversion of the stated tensor–Hom arrow and application of `c_f` give exactly the claimed exchange.
- Step 4: checked against the naturality and compatibility clauses of `lem-sf-tensor-hom` and A5 of `def-sf-datum`; the coefficient argument uses the explicit unit–composition–counit chain from Step 2, and the shift calculation is written out.
- New nodes: none; there are no new statements requiring source, edge-case, duplicate, or Mathlib-leaf review.
- Small cases: rechecked $f=\mathrm{id}$, $M=0$, empty $X$, $n=1$, and the integral and field coefficient stages; each remains covered by the typed unit and zero-object arguments.

Changes made in this second reading: removed the `lem-sf-mate` proof dependency and its citations because that existing node is tied in its statement to the finite-level composition theorem; replaced it with the explicit all-stage adjunction Hom calculation from A1/A4, and rewrote Step 4 to refer to that calculation. No node statements were changed and no new nodes were created.
