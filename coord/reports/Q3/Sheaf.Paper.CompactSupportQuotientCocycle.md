## What changed

Both original theorem statements are retained verbatim. Their proof bodies now combine
ordinary quotient maps, universal derived computation isomorphisms, normalized
adjunctions and compact-support naturality.

The eight original coordinate declarations move to the publicly re-exported
`Sheaf.Paper.CompactSupportQuotientCocycleData`. Their names, signatures and visibility
are retained. Five bodies are verbatim; the two restriction comparisons factor their
original constructions through canonical coefficient presentation aliases.
`CompactSupportQuotientModuleSpec` factors
its section equations through two reducible generic formula abbreviations. The first
uses HEq between canonically identical restricted and unrestricted section carriers;
`heq_iff_eq` recovers the old equation. The scalar actions and tensor maps are unchanged.
The definition refactor and its consumer check are recorded in
`coord/changes/compact-support-quotient-module-formulas.md`.

For representatives, the proof establishes invertibility of each actual universal
computation map directly from `scalarReductionDerivedExistence`. The ordinary quotient
transformation is the transpose of the final unit; its balancing transformation is
Mathlib's canonical comparison of composed left adjoints. Their module-section formulas
are proved through the ordinary normalized units and scalar linearity. Naturality gives
chain maps, and componentwise invertibility gives an isomorphism of complexes. Identity
component isomorphisms provide the original HEq witnesses. The parent combines these
proved constructions with the separate comparison-square theorem for the given maps.

For the cocycle, the derived quotient adjunct is the canonical left-adjoint composition
isomorphism, and its unit equation is the inverse Hom equivalence identity. The output
identity and composition are actual naturality/functoriality calculations from the input
laws and the normalized coefficient squares. The composition square uses the existing
`sfCompactSupportRestriction_comp`, the quotient-factor equality and the image of the
unit prime in each stalk of Y.

`CompactSupportCoefficientPresentation` names the general finite-coefficient restriction
functors and their actual identity, composition and compact-support comparisons in
canonical category types. The two original quotient restriction comparisons specialize
these aliases, retaining exactly their original constructions and equality casts.

`CompactSupportQuotientNative` gives the same finite-level functors, restriction functors,
quotient maps and comparison isomorphisms explicit canonical constant-coefficient source
and target types. Every value is literally its existing declaration. This avoids repeated
normalization of equivalent category presentations; the original public statements use
their original expressions. The module-map API similarly separates real constructions
from their section formulas. The final assembly rewrites the intrinsic/ambient compact-support presentation
using a proved private equality over an abstract coefficient ring. No shared
definition outside the item is changed.

The legacy options disabling transparency checks have been removed.

No definition has a hole. The named ordinary adjunction alias uses the already specified
adjunction with its normalized unit, which determines the adjunction; it introduces no
choice of an arbitrary witness from a mere existence statement.

## Proved and sorry left

The two original holes are closed by decomposition:

- `WeilConjectures.compactSupportQuotient_representatives`: computation-map invertibility,
  ordinary quotient and balancing chain maps, their formulas and balancing invertibility
  are proved. Only the two universal derived comparison squares remain a dependency.
- `WeilConjectures.compactSupport_quotient_cocycle`: quotient adjunct invertibility, its unit
  equation, and transport of the input identity/cocycle to compact support are proved.
  Input coherence and identity coefficient normalization remain dependencies.

Six new holes remain, each in its own new module, with a source, full proof in words
and a node:

- `WeilConjectures.compactSupportQuotient_computation_squares`, node
  `lem-coef-compact-support-quotient-computation-squares`: the two derived squares for
  GIVEN chain maps satisfying the section formulas. It asserts neither existence nor
  invertibility of these maps.
- `WeilConjectures.compactSupportQuotient_input_laws`, node
  `lem-coef-compact-support-quotient-input-laws`: input identity and composition for any
  scheme and unbounded integral object, with no compact-support functor.
- `WeilConjectures.compactSupportRestriction_identity`, node
  `lem-coef-compact-support-restriction-identity`: the normalized identity coefficient
  square for compact support over any finite commutative ring, including the prescribed
  equality cast. It has no integral object or quotient cocycle assertion.
- `WeilConjectures.compactSupportQuotient_raw_input`, node
  `lem-coef-compact-support-quotient-raw-input`: conversion from canonical native
  input laws to the original scalar-reduction presentation.
- `WeilConjectures.compactSupportQuotient_raw_output_identity`, node
  `lem-coef-compact-support-quotient-raw-output-identity`: conversion from ambient
  compact-support identity to the original intrinsic presentation.
- `WeilConjectures.compactSupportQuotient_raw_output_composition`, node
  `lem-coef-compact-support-quotient-raw-output-composition`: conversion from ambient
  compact-support composition to the original intrinsic presentation.

There are zero holes in the original module, two original holes closed and six new
holes added. This is a decomposition, not a claim of net hole reduction or of an
axiom-free final target proof. All other delivered declarations have complete bodies.

## No longer needed

The original direct proof imports
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Paper.KFlatRingedToposPullback`,
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, and
`Sheaf.Algebra.Homology.CochainTensorUniverses` are removed from the parent. Its proof
calls none of their declarations. K-flat resolution, K-flat scalar extension and derived
change of rings remain dependencies of the new comparison-square and input-law plans.
No existing node or module is claimed as globally pruned or withdrawn. No declaration
of the adopted source library is changed or removed.

The K-flat balancing route is no longer needed for the derived adjunct invertibility
clause: the definition by twice transposing the unit gives the canonical adjunction
composition isomorphism directly. The representative theorem and its actual tensor
formulas are still required and retained. No realized blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No original mathematical statement is weakened or disputed. The current blueprint's
finite-level comparison paragraph is the final paragraph of
`lem-coef-integral-compact-support.proof.md`; the older expanded six-step DAG plan
supplies the representative and normalization arguments used here.

The original plan used balancing on a K-flat representative to establish invertibility
of the derived adjunct. Its normalized adjunction definition gives a shorter categorical
proof of that clause. The remaining representative and coherence obligations are
separated explicitly in the DAG.

The original concrete section equality and repeated integral/constant category
presentations caused kernel timeouts despite quick elaboration. The equivalent HEq
section specification, named module maps and canonical typed wrappers address those
presentation costs without altering the mathematical constructions.

## New nodes

`def-coef-compact-support-coefficient-presentation`: Canonical coefficient restriction comparison types. Its Lean module is `Sheaf.Paper.CompactSupportCoefficientPresentation`.

`lem-coef-compact-support-finite-coefficient-cocycle`: Coefficient comparison square with a prescribed composite. Its Lean module is `Sheaf.Paper.CompactSupportFiniteCoefficientCocycle`.

`lem-coef-compact-support-ordinary-quotient`: Ordinary quotient and balancing section formulas. Its Lean module is `Sheaf.Paper.CompactSupportOrdinaryQuotient`.

`lem-coef-compact-support-quotient-adjunct`: Invertibility and unit equation of the derived quotient adjunct. Its Lean module is `Sheaf.Paper.CompactSupportQuotientAdjunct`.

`lem-coef-compact-support-quotient-chain-formulas`: Concrete quotient chain maps with tensor formulas. Its Lean module is `Sheaf.Paper.CompactSupportQuotientChainFormulas`.

`lem-coef-compact-support-quotient-comparison-laws`: Normalized quotient coefficient comparison squares. Its Lean module is `Sheaf.Paper.CompactSupportQuotientComparisonLaws`.

`lem-coef-compact-support-quotient-computation-squares`: Universal derived comparison squares for quotient chain maps. Its Lean module is `Sheaf.Paper.CompactSupportQuotientComputationSquares`.

`lem-coef-compact-support-quotient-coordinates`: Quotient factors and canonical coefficient computation coordinates. Its Lean module is `Sheaf.Paper.CompactSupportQuotientCocycleData`.

`lem-coef-compact-support-quotient-input-laws`: Identity and composition for the input quotient reductions. Its Lean module is `Sheaf.Paper.CompactSupportQuotientInputLaws`.

`lem-coef-compact-support-quotient-model-maps`: Ordinary quotient and balancing chain maps. Its Lean module is `Sheaf.Paper.CompactSupportQuotientCocycleRepresentativesData`.

`lem-coef-compact-support-quotient-module-maps`: Named ordinary integral quotient maps and balancing isomorphisms. Its Lean module is `Sheaf.Paper.CompactSupportQuotientModuleMaps`.

`lem-coef-compact-support-quotient-native`: Canonical constant-coefficient presentation of the integral reductions. Its Lean module is `Sheaf.Paper.CompactSupportQuotientNative`.

`lem-coef-compact-support-quotient-output-composition`: Compact support transports the input quotient cocycle. Its Lean module is `Sheaf.Paper.CompactSupportQuotientOutputComposition`.

`lem-coef-compact-support-quotient-output-identity`: Compact support transports the input quotient identity. Its Lean module is `Sheaf.Paper.CompactSupportQuotientOutputIdentity`.

`lem-coef-compact-support-quotient-output-transport`: Pairing the transported quotient identity and cocycle. Its Lean module is `Sheaf.Paper.CompactSupportQuotientOutputTransport`.

`lem-coef-compact-support-quotient-transport`: Invertibility of the twice-transposed unit. Its Lean module is `Sheaf.Paper.CompactSupportQuotientTransport`.

`lem-coef-compact-support-restriction-identity`: Identity coefficient normalization of compact-support restriction. Its Lean module is `Sheaf.Paper.CompactSupportRestrictionIdentity`.

`lem-coef-compact-support-quotient-raw-input`, `lem-coef-compact-support-quotient-raw-output-identity`, and `lem-coef-compact-support-quotient-raw-output-composition` are presentation-conversion nodes for the original target expressions.

All new nodes are in `dag/nodes/sec-six-functors/`. The definition change record is
`coord/changes/compact-support-quotient-module-formulas.md`.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
