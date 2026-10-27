## What changed

The item theorem keeps its complete signature. Its proof now combines a proved
adjunction tower with one remaining tensor-quotient section comparison. It imports
AdicPerfectQuotientSectionComparison privately; its original public imports stay.

AdicPerfectSliceSections constructs constant module sheafification and terminal
sections on a slice, proves their adjunction, compares slice realization with
restriction of global realization, and compares its sections with ordinary constant
fixed-module sections. It proves the general unit/counit mate unit identity.

AdicPerfectQuotientSectionRealization cancels the completed coefficient extension
using the cone equation, constructs the concrete sections right adjoints, and
transports the scalar/constant-module adjunction to the actual quotient functor.
Existing proved presentation, scalar adjunction and scalar/slice helpers from
AdicPerfectModelCompleteReduction are reused in theorem proofs.

AdicPerfectQuotientSectionModel constructs successor mates and proves their unit
equation. It bundles the functors, adjunctions, successor maps and unit proof into
SectionModel using the generic SectionModel.ofAdjunctions constructor, proves its
Nonempty theorem by the concrete construction, and exposes
the fields of a selected record. Every selection uses a theorem proved here,
without sorry. The selected right adjoints are uniquely isomorphic to the concrete
sections adjoints; the unit identity characterizes the successor mates.

AdicPerfectQuotientSectionComparison is the remaining obligation: identify constant
algebraic quotient sections with realization followed by the selected right adjoint,
compatibly with successor maps. Its source and proof plan explain the tensor quotient
calculation, equality of sheaf maps on generators, and transport by the unique
right-adjoint isomorphisms. No existing module besides the item is changed. No
target statement or existing definition is changed. All writes stay in this sandbox.

Remote compilation passed for all five files: SliceSections 26.6 s,
QuotientSectionRealization 55.9 s, the optimized QuotientSectionModel 30.7 s,
SectionComparison 26.6 s, and the item 44.7 s. No diagnostic options remain. Compilation and axiom checks also passed in the
second delivery attempt; its preflight rejected only structure-signature metadata,
now corrected to stop before `where`.
The original item signature was compared literally and is unchanged.


## Proved and sorry left

This is a decomposition, not a complete proof: one original hole is replaced by
one strictly smaller comparison obligation (net zero holes). The original
AlgebraicGeometry.Scheme.adicPerfectQuotientSectionAdjunction now has a complete
Lean proof from that comparison and the constructions proved in this delivery.

New sorry: AlgebraicGeometry.Scheme.adicPerfectQuotientSectionComparison,
node lem-sfb-adic-perfect-quotient-section-comparison. This is the only sorry in
the delivery. It does not assert existence of adjunctions or the unit equation;
those are constructed and proved independently.

Proved without sorry in this delivery, in namespace
AlgebraicGeometry.Scheme.AdicQuotientSections:
localRingUnit_injective, localRingUnit_surjective, constantPresheafAdjunction,
localAdjunction, localConstantMap_fac, localConstantMap_isIso, localConstantIso,
changeOverIso_exists, fixedConstantUnit_injective, fixedConstantUnit_surjective,
fixedConstantMap_isIso, fixedConstantIso, sectionsIso, balancingMate_unit,
quotientAdjunction_exists, realizationIso_exists, rawAdjunction_exists,
rawAdjunction, SectionModel.ofAdjunctions, sectionModel_exists, and step_unit.
The other declarations construct the actual functors, maps and packaged data.

## No longer needed

No existing public import is removed; no module is withdrawn. No whole-library
pruning is claimed. The exploratory Mathlib.CategoryTheory.Adjunction.Mates import
was removed after using the direct unit/counit formula instead of TwoSquare.

The former direct proof dependency lem-weil-pbc-site-constant-restriction is
replaced by localConstantIso, proved by sheafification on the slice. The former
direct dependencies lem-sfb-adic-finite-reduction-data and
lem-sfb-constant-realization-derived-scalar-extension remain needed through the
new realization and comparison nodes. The fixed unit route is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement repair is claimed. A coefficient-linear slice
adjunction required an actual module sheafification construction: constantSheafΓAdj
alone has a different module category. Once adjunctions are constructed, the first
successor identity is the unit/counit mate identity. The second identity still needs
tensor normalization and equality of sheaf morphisms before evaluation on all
locally constant sections; checking only global constant sections is insufficient.

Profiling found expensive specialized equation elaboration and then kernel
normalization of the concrete scalar implementations in the final existential
assembly. Scalar functors are kept irreducible locally, mate arguments and quotient
map/functor interfaces are explicit, and the construction is exposed through a
SectionModel structure selected from a completely proved Nonempty theorem. Its
fields provide the interface without exposing nested scalar implementations to
consumers. The generic constructor keeps the right adjoints and adjunctions as
parameters when applying the unit proof. The general slice construction and concrete scalar normalization are
separate self-contained modules after these improvements. No transparency check
is disabled and no limit is raised. No unproved theorem selects data.

## New nodes

- def-sfb-adic-perfect-slice-sections: proved slice constant realization, sections,
  adjunction, comparison isomorphisms and the general mate unit identity;
  AdicPerfectSliceSections.
- def-sfb-adic-perfect-quotient-section-realization: proved completion cancellation
  and concrete quotient sections adjunctions; AdicPerfectQuotientSectionRealization.
- def-sfb-adic-perfect-quotient-section-model: proved successor unit identity and
  SectionModel construction exposing its abstract fields;
  AdicPerfectQuotientSectionModel.
- lem-sfb-adic-perfect-quotient-section-comparison: the remaining tensor quotient
  section identification and successor compatibility;
  AdicPerfectQuotientSectionComparison. The adjunctions and first unit equation
  have already been proved, so this omits that part of the original obligation.

Change record: coord/changes/R2-adic-perfect-quotient-section-local-attributes.md.
It documents the local irreducibility attributes flagged by preflight and the
unchanged interface seen by the sole direct consumer, AdicPerfectUnitHom.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
