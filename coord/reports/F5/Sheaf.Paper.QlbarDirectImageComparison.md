## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicAlgCl_of_boundedBelow`
in `Sheaf.Paper.QlbarDirectImageComparison`, preserving its complete signature and all public
imports. Added private proved helpers for restriction conservativity, its passage to derived
categories, invertibility of the canonical scalar mate, existence of the small derived copowers,
and application of the scalar copower criterion. No definitions or public statements changed.

The proof uses the already proved `condensedQbar_derived_scalar_basis`,
`condensedSubfield_bounded_copower_comparison`, and
`Adjunction.isIso_iff_unitCoproductComparison`. These are mathematical tools, not replacements
for any blueprint unit. The unit's rational-coefficient step remains bounded filtered
continuity: the copower lemma expresses the copower as finite partial sums of a representative
with a common lower bound. No ambient unbounded coproduct preservation or properness is used.
The scalar-basis unit is normalized for the actual finite-subfield inclusion, so the criterion
applies to the specified `derivedPushHom`, rather than an abstract isomorphic pair of objects.

Updated only `proof`, `proof_deps`, `proof_origin` and obsolete `tool_uses` in the existing node
`lem-sfb-qlbar-direct-image-comparison`. The maintainer may mark the three newly used proved
project results as tool uses; no maintainer-owned approval was added here. All new imports are
private. Single-file remote compilation verifies the complete proof; delivery preflight also
checks the exported declaration signatures and axioms.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicAlgCl_of_boundedBelow`
(blueprint `lem-sfb-qlbar-direct-image-comparison`).

Added 0 holes; split off 0 statements; 0 holes remain in the delivered module.
All five private helpers are proved. This is a proof from existing declarations, not a
decomposition or a relocation of the original hole. Transitive dependencies remain subject
to the project's axiom accounting.

## No longer needed

Removed these private proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage`
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.Paper.QlbarTailModuleColimit`
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `Sheaf.Paper.ProjectionMateExact`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Sheaf.Paper.CartesianCoefficients`

The current proof does not need the old planned dependencies
`lem-sfb-qlbar-bounded-tensor-colimit` (`Sheaf.Paper.QlbarBoundedTensorColimit`),
`lem-sfb-filtered-finite-free-projection`
(`Sheaf.AlgebraicGeometry.FilteredFiniteFreeProjection`), or
`lem-sfb-internal-scalar-projection-mate` (`Sheaf.Paper.InternalScalarProjectionMate`).
Their interfaces were read and trial imports compiled before the shorter route was found.
They were not imports in the original module and are not added in this delivery. Their
claims, declarations and other consumers are untouched; this report makes no claim that they
are globally unreachable.

Removed obsolete top-level tool approvals from this node:

- `lem-pe-internal-section-tensor-comparison`
- `lem-sfb-internal-module-operations-transport`
- `lem-sfb-qlbar-tail-module-colimit`
- `lem-sfb-subfield-flat`
- `lem-weil-pbc-equivalence-injective-resolutions`
- `lem-weil-pbc-exact-functor-complex-cohomology`
- `lem-weil-pbc-independent-sheaf-tensor-colimits`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-ring-sheaf-change-adjunction`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`
- `sk-prop-sfb-cartesian-coefficients`

Retained the exact-scalar-extension and cohomological-detection tool entries. All original
public imports are retained verbatim, so consumers see the same interface. No module is
withdrawn, and no source-library declaration is deleted.

## Where the brief, the DAG or earlier work was wrong

The old six-step docstring and the later three-step DAG assembly describe a valid longer
route, but are unnecessary for this item. A complete scalar-basis assembly already exists
for proper maps in `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.
Inspection of that proof shows that properness is used only through
`condensedSubfield_bounded_copower_comparison`, whose signature requires just qcqs. This
packet uses that shorter argument directly at the item's unchanged qcqs hypotheses.
The historical docstring is retained; the node and proof-body comment record the actual route.

The rework table lists a historical quarantine caused by an imported dependency, but the
assigned source is currently present. The current source was copied and proved; no archive
was deleted or replaced. There is no current F5 return for this item.

Edge cases: the lower bound can be any integer; no upper bound, constructibility, or Tor
amplitude is assumed. Restriction conservativity is proved on arbitrary derived maps. The
copower continuity theorem includes the empty family and the zero complex; its basis
specialization uses only copies of this one bounded-below object. All comparison maps come
from the existing scalar adjunctions and retain their actual units and central scalar actions.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
