## What changed

Completed all eight remaining proofs in `Sheaf.Paper.CompleteCoefficientDatum`.
The existing public statements and definitions are unchanged. New private helpers
construct scalar-extension units, the identity-on-sections comparisons for restriction
along a composite or identity, and the balancing map and its inverse. These use the
existing sectionwise module adjunction and sheafification helpers. Transposition proves
the inverse identities and reduces coherence to the specified local tensor formulas.
The resulting families give actual chain isomorphisms and transition chain maps.

For `adicReductionUnderlying_tensor`, specialize the already proved
`SheafOfModules.exists_changeOfRings_tensorCancellation` to the quotient coefficient
unit, compose with the left unitor and braiding, and use its naturality to obtain a
chain isomorphism. `CochainComplex.mapBifunctorSingle₂Iso` identifies the termwise
tensor with the total tensor against the quotient module in degree zero. Localizing
this chain isomorphism gives exactly the existing `derivedTensorRing` object.
The cancellation lemma is an existing tool from `sk-def-sf-operations`; its statement
covers independent site object and morphism universes and requires no flatness.

Updated the main node's proof, proof dependencies and proof origin to record these
constructions and the cancellation specialization. Updated `adic-unit-exists-data`
to record the explicit transposition argument and the correct Modules on Sites source
for Section 03EK. The unit's realized statement
and steps are preserved. No new public declaration, new node, statement repair,
consumer adaptation or change record is required.

Validation: the complete delivered module compiled through `lcompile.py` in 38.3 seconds,
with no errors or warnings, after removal of the five unused imports below. Both added
imports passed `tools/import_direction.py may`. All Lean lines are at most 100 characters.
The constructions apply unchanged to zero rings, zero modules, zero/unit ideals,
equal quotient indices, and arbitrary unbounded complexes; no completeness, quotient
flatness or boundedness hypothesis was introduced.

## Proved and sorry left

Closed 8 of the original 8 holes; added 0; split off 0. No `sorry` remains in the module.
The closed declarations, with namespace `AlgebraicGeometry.Scheme`, are:

- `adicBalance_exists` — `def-weil-pbc-complete-coefficient-datum`.
- `adicTransitionComplex_exists` — `def-weil-pbc-complete-coefficient-datum`.
- `adicBalanceHom_naturality` — `def-weil-pbc-complete-coefficient-datum`.
- `adicTransitionComplex_naturality` — `def-weil-pbc-complete-coefficient-datum`.
- `adicNormalization_cocycle` — `def-weil-pbc-complete-coefficient-datum`.
- `adicUnit_exists_data` — `adic-unit-exists-data`.
- `adicNormalization_unit` — `def-weil-pbc-complete-coefficient-datum`.
- `adicReductionUnderlying_tensor` — `def-weil-pbc-complete-coefficient-datum`.

Every added private theorem and every proof field of a private construction is proved.
No other module is delivered and no hole is added elsewhere. This is a proof delivery,
not a decomposition.

## No longer needed

Removed these unused proof imports:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsGeneral`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`.

The concrete comparison uses the existing K-flat model on both sides, so its proof
does not need the universal derived-change-of-rings functor or comparisons between
arbitrary resolutions. Removed `lem-pur-derived-change-of-rings` from `proof_deps`
and the obsolete top-level `tool_uses` approval. Its statement dependency is retained:
the mathematical definition of reduction still describes derived change of rings.
`KFlatResolutionGeneral` remains needed for `adicKFlatModel_exists`; the intrinsic
Mathlib sheaf restriction API remains publicly imported. The independent-universe
replacement APIs and the fixed-ring sheaf restriction presentation are not used here.
These are per-module import removals; global target reachability is left to the ledger.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The auxiliary unit node
previously located Section 03EK in `sites-cohomology.tex`; its proof-source and
proof-origin records now correctly name `sites-modules.tex`. The existing dependencies supply
the scalar-extension constructions, but do not themselves state the required balancing
coherence. The explicit adjunction and generator argument supplies it without adding
intermediate holes. The earlier split `adicUnit_exists_data` is now proved directly.

The reduction comparison can use the already proved tensor-cancellation theorem
specialized to the coefficient unit, rather than rebuilding scalar-extension versus
sheaf-tensor comparison at the small site's unequal universes. This tool is now named
in the main node's proof dependencies. Searches through `msearch.py` used Lean Finder,
Loogle and grep; Mathlib's `ModuleCat.extendScalarsId` and `extendScalarsComp` concern
section modules, so the sheafification and chain-level argument still had to be written.

The inherited naturality block's profiler and increased-heartbeat wrappers were
removed. Giving generator equations explicit arguments and using injectivity of
transposition avoids repeated inference through nested `adicChange` definitions;
the whole file checks within the unchanged compile limit at default heartbeats.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
