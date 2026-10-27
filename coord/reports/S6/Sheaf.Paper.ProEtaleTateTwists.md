## What changed

Filled nine theorem proofs in `lean/Sheaf/Paper/ProEtaleTateTwists.lean`. Finite local
freeness and Kummer existence specialize clauses 1 and 2 of the existing
`Scheme.tateTwist_locallyFree`; uniqueness uses the proved scalar-extension
pure-tensor extensionality theorem. The two Kummer coherence proofs remain unchanged named holes.

The integer-ring comparison uses equality with the spectral norm. Finite quotient
finiteness uses compactness of the closed unit ball and continuity of the existing
ell-power reduction map. The reduction and transition ring-map instances use the
existing sheaf-of-rings construction. Nested ideals follow from divisibility of
successive powers. Rational identity and composition implement the DAG's four
successive uniqueness arguments (integers, finite quotients, integral limits,
rational scalar extensions).

Added proof-only imports `Sheaf.Paper.ScalarExtensionBinaryCoherence` and
`WeilConjectures.NumberTheory.Padics.IntegersModPow`. All public signatures,
definitions, attributes and public imports are unchanged. Updated the two node
copies for the finite quotient route and the reduction ring-map dependencies.

## Proved and sorry left

Closed 9 of the original 21 holes; added 0 holes and split off 0 statements.
All names below are in `AlgebraicGeometry.ProEtale`.

Closed:

- `spFiniteTwist_locallyFree`.
- `spIntegers_eq`.
- `spEllQuotient_finite_continuous`.
- `spEllPointReduction_isMonHom`.
- `spTateEllIdeal_succ_le`.
- `spEllPointTransition_isMonHom`.
- `spRationalTwistMap_id`.
- `spRationalTwistMap_comp`.
- `spFiniteKummer_existsUnique`.

Remaining unchanged named theorem holes:

- `spIntegralLevelTransition_existsUnique` — `lem-sp-integral-level-transition-unique`.
- `spIntegralTwistLevel_comparison` — `sk-def-sp-tate-twist`.
- `spIntegersMap_existsUnique` — `lem-route-sp-integers-map-exists-unique`.
- `spEllMap_existsUnique` — `lem-route-sp-ell-map-exists-unique`.
- `spIntegralTwistMap_existsUnique` — `lem-route-sp-integral-twist-map-exists-unique`.
- `spRationalTwistMap_existsUnique` — `lem-route-sp-rational-twist-map-exists-unique`.
- `spRationalTwistMap_semilinear` — `lem-sp-rational-twist-transition-semilinear`.
- `spQbarTwistAction_existsUnique` — `lem-route-sp-qbar-twist-action-exists-unique`.
- `spFiniteKummer_id` — `sk-def-sp-tate-twist`.
- `spFiniteKummer_comp` — `sk-def-sp-tate-twist`.
- `spTwists_locallyFree` — `sk-def-sp-tate-twist`.
- `spTwists_commonCover` — `lem-route-sp-twists-common-cover`.

The rational coherence proofs use the existing four named existence-and-uniqueness
theorems, whose holes remain listed above. They do not assume a new coherence
statement. The finite proofs use the already proved local-freeness theorem.

## No longer needed

No existing public imports or modules were removed. The finite-quotient proof no
longer uses `lem-weil-l-adic-extension-integers-dvr` or
`lem-weil-valued-dvr-finite-quotients`: properness and compactness prove finiteness
without uniformizer factorization. These nodes remain needed elsewhere in the
library; no withdrawal is claimed. The quotient node now records properness and
the elementary continuity argument already formalized upstream.

Removed `lem-route-sp-rational-twist-map-comp` and
`lem-route-sp-rational-twist-map-id` from the reduction ring-map node's
`proof_deps`; neither is used by its proof steps or by its Lean proof. Both
rational coherence theorems remain used by the rational twist diagram and were
proved in this delivery.

## Where the brief, the DAG or earlier work was wrong

The reduction ring-map node listed rational transition identity and composition
as proof dependencies although its three proof steps only use continuous
postcomposition and ring objects. Removed those two extraneous edges. No statement
was found false or changed. The unit's finite Kummer route is preserved; its
non-finite local-freeness work remains open.

Kummer coherence was attempted but not included: the tested proof caused expensive
elaboration around scalar-map transports. The original statements and their named
holes are preserved; no helper or extra import from that attempt is delivered.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
