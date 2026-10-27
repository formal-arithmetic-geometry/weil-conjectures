## What changed

Proved `CategoryTheory.principalKoszul_dual_tower_comparison` with the original
statement and hypotheses. The explicit term maps remove the positive tensor unit,
project to the unique surviving Hom factor and evaluate at one. The finite
calculations identify the differential, both successor transitions and the unit.
Chain and strict-tower assembly, the existing signed cochain braiding, and
transposition give the requested augmentation-compatible comparison for arbitrary P.

Three new modules contain the explicit finite construction and its fully proved
component calculations. They are mathematical parts of the argument, not outstanding
obligations. No new proof hole, axiom or arbitrary unproved witness is introduced.

The existing principal cone now names its unchanged scalar chain map as
`principalKoszulScalarComplex`. The unit evaluation API exposes its specified
projection component and naturality. Named proofs cache the existing sheaf-composition
instances locally. Existing signatures, reducibility attributes, mathematical data
and target statements are preserved. No adopted-source module is edited.

The four principal consumers `KoszulRoosProjectionComparison`,
`RegularRoosKoszulUnit`, `PrincipalConeKoszulRoosComparison` and
`PrincipalKoszulStrictReplacement` use the shared scalar parameter in their proofs.
The two evaluation consumers `RingedCechKoszulHomLimitComparison` and
`FlatRingedIdealCompleteEquivalence` use the proved naturality API with local opacity.
The endpoint, principal-cone and flat-equivalence files serialize elaboration with
`Elab.async false` to avoid concurrent reductions of the concrete constructions.
Kernel checking and transparency checks remain enabled.
All adapted modules are unclaimed; no forced adaptation of another group's module
is delivered. The change records list the textual users and effects.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.principalKoszul_dual_tower_comparison`.

Added 0 holes. All declarations in the three new modules are proved, including
`CategoryTheory.PrincipalKoszulDualTerms.finiteDualTerm_nonzero_differential` and
`CategoryTheory.PrincipalKoszulDualTerms.finiteDualTerm_transition_unit`.
There is no `sorry` in any delivered Lean module. The main theorem and both finite
calculation lemmas have exactly the axioms `propext`, `Classical.choice`, `Quot.sound`.

Clean compilation: finite terms 15.4 s, differential 27.3 s, endpoints 45.5 s,
main comparison 31.6 s; the unchanged evaluation construction with its API 24.8 s,
Koszul system 22.2 s. Adaptation checks passed: Koszul projection 46.2 s, principal-cone comparison
55.8 s after the final scheduling, scalar API and opacity repair, strict replacement 2.1 s,
regular Roos unit 0.7 s, Cech Hom-limit comparison 25.0 s and flat equivalence
61.1 s reported elapsed time (accepted by
the compile tool, which separately enforces the 60-second Lean check).

Nine evaluation consumers passed with their original source; those identical
validation copies are omitted from the packet. The existing Roos-intrinsic consumer
is mathematically valid but already exceeds the time limit against the published
library (118.7 s). It remains unchanged; tests with the refactor were also
mathematically valid (99.7 s and 102.7 s). This pre-existing performance issue is
recorded in the scalar-map change record; no Roos or intrinsic definition is changed.

## No longer needed

No existing node, module, declaration or unit-route step is withdrawn. The original
item's public imports are retained; it had no named proof dependencies to prune.
All three new supporting modules are used. The tensor symmetry is already proved
in the adopted source library; no separate braiding obligation is added.

## Where the brief, the DAG or earlier work was wrong

The original single proof step omitted the concrete chain, transition and unit
calculations and the exchange of the two tensor orders. The revised node describes
these calculations and their assembly. Its statement remains unchanged.

Repeated expansion of preferred single-functor coherence and chosen Hom projections
made the direct presentation exceed 60 seconds. Sharing the actual scalar map,
exposing the existing evaluation component and using generic transport identities
makes the new proof modules compile within the limit without weakening transparency.

## New nodes

- `def-pur-principal-koszul-dual-terms`: explicit component isomorphisms,
  projection invertibility, zero components and map equations.
- `lem-pur-principal-koszul-finite-dual-differential`: the sole supported
  differential equation for these specified maps.
- `lem-pur-principal-koszul-finite-dual-endpoints`: both supported transition
  equations and the degree-zero unit equation.

All three nodes are fully proved. The finite equations omit the coefficient complex,
total tensor, strict tower, chain-isomorphism existence and final augmentation assembly.
They are strictly smaller parts of the argument; no `sorry` was split off.

Change records:
`coord/changes/principal-koszul-scalar-parameter.md` and
`coord/changes/ringed-hom-unit-component-api.md`.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
