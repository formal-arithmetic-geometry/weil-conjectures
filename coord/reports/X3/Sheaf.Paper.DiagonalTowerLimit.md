## What changed

Reduced `AlgebraicGeometry.ProEtale.diagonalTower_limit` to two separate calculations:
normalized limit endpoints and finite quotient comparison. The combining proof
recovers the strict-system Ext class through the existing
`normalizedBoundarySystem_iff_target`, preserves its finite Cartier normalization,
and uses the existing complete-scalar restriction argument to construct the unique
completed arrow. Uniqueness uses the whole underlying map.

Reused the existing coefficient-transport and scalar-restriction proofs through
new `Core` theorems requiring only their two derived-category instances. Their
original modules are restored verbatim from their current quarantine archives,
including their complete proofs. Original theorem
signatures, universes, visibility, docstrings and public imports are preserved.
`DiagonalTraceLocalizations`, its fields, instances and defining module are
unchanged. X3 claimed both comparison rework items for this repair.
See `coord/changes/X3-diagonal-complete-scalar-imports.md`.

Named, explicitly typed versions of the repeated finite objects, class and
normalization functions keep kernel checking local. The proved
`diagonalLimitSpec_of_typed` gives the original specification by definitional
equality. No existing shared definition or target statement is changed. Generic
assembly, strict witness recovery, finite-equation conversion and completed
compatibility are checked separately. Named strict input and output specifications
keep the witness types shared between those checks. A proved typed-assembly
module combines the strict and completed data before the original item applies
the specification-compatibility theorem.

The assigned source was initially quarantined. Its complete archived source was
restored; the shared mirror subsequently restored the same source. No archive,
existing declaration, module or Lean attachment is withdrawn.

## Proved and sorry left

Closed the one original item hole:
`AlgebraicGeometry.ProEtale.diagonalTower_limit`, node
`det-prop-diagonal-tower-limit`. Its proof combines strictly smaller statements;
this is a decomposition, not a net reduction in the sorry count.

Added exactly two holes, each a whole named public theorem in its own module:

- `AlgebraicGeometry.ProEtale.diagonal_limit_endpoints`, node
  `lem-sfb-diagonal-limit-endpoints`, in `Sheaf.Paper.DiagonalLimitEndpoints`.
  This gives the normalized ordinary and derived endpoint comparisons and
  endpoint completeness. It constructs no arrow and asserts no finite map equation.
- `AlgebraicGeometry.ProEtale.diagonal_limit_finite_reduction`, node
  `lem-sfb-diagonal-limit-finite-reduction`, in
  `Sheaf.Paper.DiagonalLimitFiniteReduction`. This gives quotient comparisons and
  their unit and naturality equations for the simultaneous reduction of an
  integral derived map. It asserts neither existence nor uniqueness of a lift.

All other declarations in the delivery have complete bodies, including the
coefficient cores and restored original proofs, generic assembly, finite equality conversion,
strict normalization, completed-data assembly and specification compatibility.
The two other public theorem proofs in the assigned module remain proved.
Every added definition is an explicit existing object or formula; none contains
sorry or selects arbitrary data from an unproved existence assertion.

Validation: the final cleaned repair compilation passed all 18 modules against
the current server build, each below 60 seconds. Finite input took 44.6 seconds,
finite conversion 40.2 seconds, named strict specifications 51.4 seconds, strict
witness recovery 51.7 seconds, strict normalization 30.2 seconds, typed assembly
42.3 seconds, and the assigned module 31.9 seconds. The restored original
coefficient-transport and scalar-restriction modules passed at 52.3 and 18.2
seconds. Both restored modules have zero sorry. Both unchanged direct consumers
were also checked against the exact restorations earlier (5.9 and 8.0 seconds);
their temporary copies were removed. Exactly two named theorem holes remain.
No profiling options are included; all three original theorem signatures were
compared with the current source and remain identical.

The original dry-run missing-source failure is resolved: the dependency chain and
comparison modules are live on the server. An earlier repair dry-run commit
(e39483c054b) passed preflight, class CODEX. That run deferred its related-module
overlay check to landing after a compile-service fault, while the delivered
modules compiled. Subsequent per-file budget failures were repaired by sharing
the finite formulas and separately checking strict witness recovery, finite
normalization and the final typed assembly. All these helpers are fully proved.
Delivery repeats compile and preflight against the freshly fetched base.

## No longer needed

No module is globally pruned or withdrawn. No source-library declaration is
removed. The direct use of `sk-lem-integral-models` in the old plan is replaced by
`lem-sfb-diagonal-complete-scalar-restriction-core`, which gives precisely the
required hom-set bijection on complete underlying objects without choosing an
integral lattice. The proof uses its given cycle system rather than proving it
again.

The finite input predicate imports `DiagonalLimitNormalizations` directly,
removing its unnecessary import of `DiagonalLimitSpecificationAPI`. The unused
proved helper `diagonalStrictData_of_system` is removed from the new generic
assembly module; `diagonalStrictData_map_finite` is the operation actually used.
Unused completed-localization binders are removed from the new strict helpers.

The assigned module now imports the proved typed assembly instead of directly
importing `DiagonalCompletedDataAssembly`, `DiagonalLimitCompletedData` and
`DiagonalStrictLimitData`; all three remain necessary dependencies of that
assembly. No mathematical node is pruned by this import organization.

The new coefficient cores do not import `DiagonalTowerTracePresentations`; that
import caused the cycle. The original modules retain all original public imports, statements and complete
proofs by verbatim archive restoration. Milnor epimorphic limits, closed
exactness, finite completion reduction and the constant/completed comparison are
still needed inside the endpoint and finite-comparison obligations. The signed
twist and direct-image proofs retain their existing dependencies.

## Where the brief, the DAG or earlier work was wrong

Returned delivery 9ce8fbdb6ff was approved by reviewer C-9ce8f, but landing failed
because DiagonalCompleteScalarRestriction had been quarantined after the delivery
base. Its dependency DiagonalCompletionCoefficientTransport was quarantined in
the same upstream-import red build. Both rework items are now claimed by X3 and
restored verbatim from their current archives, with every original declaration
and full proof preserved. This is a source restoration beyond rebasing the packet;
no module is withdrawn and no archive is deleted. The fresh delivery uses the
current sheaf-dag base through the delivery tool.

The source's absence was quarantine, not withdrawal; the rework archive and
attachment were preserved. The existing comparison proofs needed two localization
instances, while their module imports required the trace-presentation bundle above
the limit theorem. The explicit-instance cores make the same proofs usable below
that theorem while preserving their original interfaces.

The expanded strict-normalization statement alone required about 69 seconds of
kernel checking. Naming the repeated data and equations avoids rechecking large
function arguments. The compatibility theorem checks the original assertion;
this repair changes proof organization, not the meaning of the limit statement.
A subsequent loaded-server check exceeded 60 seconds for the combined strict
proof. Separately named strict specifications and separately checked witness
recovery and finite normalization remove that combined check. No new mathematical
obligation is introduced by this proof split. The assigned module then took
70.9 seconds; profiling located 38.5 seconds of kernel checking in its final
combining proof. That proved combination is now separately checked in
`DiagonalLimitTypedAssembly`, with the original item retaining only the proved
specification-compatibility application. Profiling options were removed.

Edge cases considered: the empty scheme, prime two, arbitrary normalized quotient
presentations and the absence of a global root basis. For the empty scheme all
objects and maps are zero. The root-tower isomorphism is input, so no compatible
global primitive root is chosen. The signs and positive-exponent convention are
inherited from the supplied Cartier boundary and cycle system.

## New nodes

- `lem-sfb-diagonal-completion-coefficient-transport-core` and
  `lem-sfb-diagonal-complete-scalar-restriction-core` carry the existing complete
  proofs with two explicit localization instances. Their original nodes retain
  their original declarations and proofs verbatim.
- `lem-sfb-diagonal-limit-endpoints` and
  `lem-sfb-diagonal-limit-finite-reduction` are the two remaining obligations.
  Their docstrings and nodes give their sources and complete proofs in words.
- `lem-sfb-diagonal-completed-data-assembly`,
  `lem-sfb-diagonal-limit-completed-data`,
  `lem-sfb-diagonal-strict-limit-data` and
  `lem-sfb-diagonal-limit-finite-conversion` contain proved assembly and equality
  conversions. `DiagonalStrictDataSpec` is an explicit proposition containing
  exactly the strict witnesses and equations.
- `def-sfb-diagonal-limit-finite-objects`,
  `def-sfb-diagonal-limit-normalizations`,
  `def-sfb-diagonal-limit-specification-api` and
  `def-sfb-diagonal-limit-input-finite` give existing expressions shared names and
  explicit result types. Specification compatibility is proved.

- `def-sfb-diagonal-strict-limit-specification` names the existing strict input
  and output witness propositions; `lem-sfb-diagonal-strict-limit-input` proves
  witness recovery independently of finite-equation conversion. The generic
  assembly module proves their witness-preserving finite-predicate map.

- `lem-sfb-diagonal-limit-typed-assembly` contains the proved combination of
  strict and completed data in the existing named specification.

Mathlib and the project were searched with the supplied search tools and source
and DAG searches. The existing complete-scalar restriction theorem is reused;
no duplicate full-faithfulness obligation is added.

## Related modules compiled before delivery

19 related module(s) compiled against this delivery by deliver3.py: 16 OK, 3 SLOW.

```json
{"capped": false, "direct": 6, "left_out": 0, "own": {"Sheaf.Paper.DiagonalCompleteScalarRestrictionCore": "00f4223b7d6984c973dc92759d9bcefa8bf371e3", "Sheaf.Paper.DiagonalCompletedDataAssembly": "309fa78f8dc39723f996ce169315e2630d249d76", "Sheaf.Paper.DiagonalCompletionCoefficientTransportCore": "6843b8d5e972d91f330f3e49ead38928b2343ca2", "Sheaf.Paper.DiagonalLimitCompletedData": "5e8add3ef53b70a2da962199a2365343e74e27e6", "Sheaf.Paper.DiagonalLimitEndpoints": "d4c6bfc644a5066bd01f86a6a389b559265a6483", "Sheaf.Paper.DiagonalLimitFiniteConversion": "e79b1e5ecbd4a5cc883412ba649b5a02d689043d", "Sheaf.Paper.DiagonalLimitFiniteObjects": "de30c5971cf6039c8faca7a6fcbf135be1c507ab", "Sheaf.Paper.DiagonalLimitFiniteReduction": "ac8381244b474f177b0d5ca7c26e923828f9f17a", "Sheaf.Paper.DiagonalLimitInputFinite": "72f4f9c63eae5b89c293a0d60478f475e0f98f2a", "Sheaf.Paper.DiagonalLimitNormalizations": "911fc14aaac224bf6686868adc707d351113f2c5", "Sheaf.Paper.DiagonalLimitSpecificationAPI": "9218533c1fb37f9e2c7cbb57ece0aa6ef5791f31", "Sheaf.Paper.DiagonalLimitTypedAssembly": "075a2bbe19f51c9feefcde5ee3a789470df1bd31", "Sheaf.Paper.DiagonalStrictLimitData": "962332a4ca97e9351f54d40a7f36986932503e2c", "Sheaf.Paper.DiagonalStrictLimitInput": "367aa37853df2e2d2b9146b35f6159dc89cc6bab", "Sheaf.Paper.DiagonalStrictLimitSpecification": "654f4c93a97e6e22071e1e54c3efff5f827eec90", "Sheaf.Paper.DiagonalTowerLimit": "e2f536226717231fc05552a0cda9024340570962"}, "results": {"Sheaf.Paper.CanonicalDiagonalRightDerived": {"hash": "88c425d865b8fb260ed064c0d0e4e3ad12eb32ed", "status": "OK"}, "Sheaf.Paper.CompletedCoefficientRealization": {"hash": "e55ff779a2bb139216130d08375c56d10c467ec7", "status": "OK"}, "Sheaf.Paper.ContinuousQbarExceptionalPreservation": {"hash": "89a09a6d02133f2fc29d671bcac62bb0c467a82d", "status": "SLOW"}, "Sheaf.Paper.DiagonalCoefficientFiniteRealization": {"hash": "854a9e92ea75f8d7b8bf2bb9c76f91526dc12456", "status": "OK"}, "Sheaf.Paper.DiagonalCoefficientReference": {"hash": "38c1e5e40668d8f52931782019aeb73a0912517a", "status": "OK"}, "Sheaf.Paper.DiagonalCompletionCoefficientTransport": {"hash": "5a50b0e280fb752d629bc96d2e8170994ab9171e", "status": "OK"}, "Sheaf.Paper.DiagonalFiniteIntegralEndpoint": {"hash": "504ce95d706b70088177fff074d18f305f97024e", "status": "OK"}, "Sheaf.Paper.DiagonalTowerTraceLimit": {"hash": "1e8765ce84df027ec21641dd4635c8dcb356abfb", "status": "SLOW"}, "Sheaf.Paper.DiagonalTowerTraceModels": {"hash": "f11a93fec947d9b49cf94edb58afa33cd3b73cd0", "status": "OK"}, "Sheaf.Paper.DiagonalTraceComparisonPartial": {"hash": "d4dc322a23b1c516f8287c6e54ca6e20c3152518", "status": "OK"}, "Sheaf.Paper.DiagonalTraceLineIdentification": {"hash": "9318bf5b0766709aa18276bae3db35215dbe0394", "status": "OK"}, "Sheaf.Paper.DiagonalTraceResidueRestriction": {"hash": "b192a8222ffb34acd9e26180a906c1cbfa02ee03", "status": "OK"}, "Sheaf.Paper.DiagonalTraceRestrictedPushAcyclic": {"hash": "26a884e80ee4dd07255c540f71a9f059dc6e8e4b", "status": "OK"}, "Sheaf.Paper.DiagonalTraceRestrictionRingedModels": {"hash": "c30291e0012d9c0375e8da148eb54130f79812f5", "status": "OK"}, "Sheaf.Paper.DiagonalTraceSources": {"hash": "41de08af575782576cafa2504e0a8dccae02af78", "status": "OK"}, "Sheaf.Paper.ExceptionalInverseImageExistence": {"hash": "e047ddc64ca96bb191cbf95acc82e09bbcecd38a", "status": "SLOW"}, "Sheaf.Paper.ProjectiveDiagonalComposition": {"hash": "4465c42b189a471e7b847b9725b82582010cbc11", "status": "OK"}, "Sheaf.Paper.RationalP1Triangle": {"hash": "d1e2d798a7453c8ae09756e0efc410fa7b065150", "status": "OK"}, "Sheaf.Paper.RestrictionLocal": {"hash": "658122de2458d148406ded36cd6c7651bbf95f19", "status": "OK"}}, "seconds": 178, "time": "2026-10-28T01:39:57+0800", "transitive": 13, "version": 1}
```

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
