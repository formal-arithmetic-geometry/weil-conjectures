## What changed

Repair of returned head `54acfcee1b8`: removed the unused `warn.sorry` option from
`DncCoefficientTransportData`. The source ledger interpreted the option's final name
component as an unattributed hole at line 28. The data module contains zero proof holes;
the packet's only two holes are the named supporting theorems listed below.
The retained packet is compared with the current shared source; the delivery tool rebuilds
the commit on freshly fetched `sheaf-dag`.

The main theorem `WeilConjectures.dncCoefficientTransport` is assembled from the actual
ordinary coefficient maps, the actual Rees-family fibre squares, and the fixed site
realization. The transported B comparison is explicitly qF inverse, scalar(kappaR),
scalar/pullback balancing, and a* q. Its normalization, uniqueness, coordinate formula
and zero-specialization identity are proved by categorical calculation and shifted-line
rigidity. No coefficient-flatness hypothesis is added.

`FiniteSectionFamilyConstancy` proves the actual fibre-map invertibility and unique
normalized comparison for arbitrary finite coefficients killed by an invertible N.
It specializes the existing local dualizing and shifted-line descent declarations.
`ScalarSectionCompositor` supplies scalar balancing with canonical section cancellation.
Two smaller coefficient-theory interfaces are isolated in `FiniteSmoothDualizingScalar`
and `SectionScalarBaseChange`.

Existing data declarations move verbatim to `DncCoefficientTransportData`, publicly
reexported from the original module to avoid a circular import by the supporting
coefficient lemmas. Their names, types, bodies and visibility are retained. The geometry
theorem remains in the original module with its existing complete proof. Consumer audit
and exact old/new code are in
`coord/changes/P2-dnc-coefficient-data-relocation.md`. No source-library file changes.

## Proved and sorry left

Closed the original module’s one hole: `WeilConjectures.dncCoefficientTransport`.
The original theorem now has a complete Lean proof; two supporting holes were added.
The delivery reduces that theorem to strictly smaller coefficient-coherence statements.
This is a decomposition, not a claim that the target import closure is sorry-free.

New proved theorems:

- `AlgebraicGeometry.Etale.NoetherianSectionSpecialization.finite_family_constancy`
  (node `lem-pur-finite-section-family-constancy`).
- `AlgebraicGeometry.Etale.scalar_section_compositor`
  (node `lem-pur-scalar-section-compositor`).

Remaining supporting holes:

- `AlgebraicGeometry.Etale.finite_smooth_dualizing_scalar`
  (`lem-pur-finite-smooth-dualizing-scalar`): ordinary counit scalar comparison and chart value.
- `WeilConjectures.DncCoefficientTransport.section_scalar_base_change`
  (`lem-pur-section-scalar-base-change`): exceptional coefficient square and section pullback.

The source `geometry` proof remains complete. No definition contains sorry. All scheme
objects and all comparisons are the published constructions. After the landing repair,
all six modules compiled successfully in the server's import-ordered packet run.
The source ledger also reports zero unattributed holes and exactly the two named
supporting holes listed above; its missing-hole gate passes for every delivered module.
The only local transparency changes protect large canonical coefficient/chart maps
from accidental unfolding; they do not alter public data.

## No longer needed

The explicit passage through E=Q_ell is unnecessary: the existing ordinary shifted-line
descent proves constancy for any finite coefficient ring with invertible annihilator.
Thus the main proof does not use `prop-pur-dnc-family-constancy` through its upstream
`DeformationToNormalConeData` interface. It uses the actual noetherian specialization
interface and its general finite-ring argument instead.

Direct proof imports removed from the original module:
`Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`,
`Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`,
`Sheaf.AlgebraicGeometry.PurityAffineLineComponents`,
`Sheaf.Paper.IntegralFinitePullbackComposition`,
`Sheaf.Paper.PurLisseMorphismRigidity`, `Sheaf.Paper.PurityDncComparisons`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.SecSmoothPurity.MixedBaseChange`,
`Sheaf.SecSmoothPurity.ScalarExtensionFunctor`, and
`WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation`.
The coefficient and mixed-base-change arguments remain dependencies of the two new
supporting statements. This is not a claim that their source modules can be withdrawn.
The standalone A1-components, lisse-rigidity and sheaf-Hom-gluing imports are replaced
by the already proved shifted-line normalized descent API; any transitive use by that
API remains needed. No module is withdrawn.

The former direct DAG proof dependencies are accounted for as follows.
`det-sp-mixed-base-change`, `det-sp-reduction-exceptional`,
`det-sp-scalar-extension-functor`, and `lem-asd-etale-finite-twist-pullback`
are retained through the new coefficient interfaces.
`lem-pur-dnc-section-geometry` is replaced by the existing proved `geometry`
argument and its actual Rees/normal geometry API.
`lem-pur-a1-components`, `lem-pur-lisse-morphism-rigidity`,
`lem-pur-sheaf-hom-cover-gluing`, and `lem-weil-pbc-derived-single-fully-faithful`
are subsumed by the proved shifted-line descent API, including its private rigidity
lemmas; their transitive mathematical uses remain.
`lem-weil-pbc-proetale-derived-pullback-composition` and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` are used through the canonical
scalar/pullback and section-compositor interfaces. `prop-pur-dnc-family-constancy`
is replaced by the proved general finite-ring ordinary-family theorem.
No DAG node or module is claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The geometric and intrinsic declarations in the old plan do not directly expose all
ordinary equations of Assertions. In particular, the reduction-exceptional declaration
is existential on intrinsic constructible right adjoints with explicit realization data;
the desired theorem uses the specified ordinary rightDerivedUpperShriek counit mate.
The new ordinary dualizing statement records precisely this remaining realization/chart
bridge. The mixed-base-change statement likewise needs its canonical section-compositor
transport, which the new section coefficient square isolates.

No statement is disputed or weakened. The finite B-ring, zero ring, empty base, and
relative dimension zero are included. The family comparison over B is formed independently
in the original data; its proof then identifies the normalized comparison by conjugation.

## New nodes

`def-pur-dnc-coefficient-transport-data` owns the relocated actual data, except the two
coefficient maps already owned by `def-pur-dnc-coefficient-section-maps`; that existing
node's module attachment is updated. `lem-pur-finite-section-family-constancy` is the
proved finite-ring generalization of the ordinary actual family comparison.
`lem-pur-finite-smooth-dualizing-scalar` is the intrinsic-to-ordinary coefficient/chart
bridge. `lem-pur-section-scalar-base-change` is the exceptional square and its section
pullback. `lem-pur-scalar-section-compositor` records scalar balancing with canonical
section cancellation. The original theorem node follows the actual Lean assembly.

Change record: `coord/changes/P2-dnc-coefficient-data-relocation.md`.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
