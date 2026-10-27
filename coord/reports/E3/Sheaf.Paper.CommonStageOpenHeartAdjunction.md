## What changed

Prove `WeilConjectures.commonStageOpenHeartAdjunction` with its original signature.
Construct extension by zero at the integral stage using the actual compact-support
functor for `(j,id)`, restrict the quotient-system adjunction, and rationalize its
linear maps and unit/counit. Use invertible mates of the coherent pullback comparisons
to construct a coherent left stage family, and descend its adjunction. Restrict it to
the heart; the distinguished-triangle characterization of short exact sequences
proves preservation of finite limits, and the adjunction supplies finite colimits.
All auxiliary declarations in the item are private and proved. The complete item
compiled through lcompile.py with the default limits in 51.6 seconds, with no
compiler errors or warnings.

The proof uses only `ordinaryOpen`, `openIdentity`, and `systemDirectId` from
IntegralSupportFunctorNormalization, not its theorem requiring a separated base.
The schemes in the item are not assumed separated. No target or existing theorem
signature changes. The node proof and dependencies follow the implemented route.

Two unused downstream imports caused cycles into WeilIndSheafCategory: remove the
private import of SfCommonStageWeilCohomology from FieldStageOrdinaryRealization,
and replace SfRationalDirectImageCoefficientCompatibility's public import of
WeilIndSheafCategory by DerivedPullbackTensorHom. These unclaimed modules retain
every declaration and proof. The change record is
`coord/changes/E3-common-open-adjunction-proof-imports.md`.

## Proved and sorry left

Close the one original hole, `WeilConjectures.commonStageOpenHeartAdjunction`
(node `lem-zl-common-stage-open-heart-adjunction`). Add zero holes and split off
zero statements. No `sorry` remains in the item. The two import-only adapted
modules retain their pre-existing holes unchanged: in namespace
`WeilConjectures.OrdinaryFieldRealization`, `integralRestriction_exact`,
`constantLinear_existsUnique`, `coefficientMap_comp`, `extendComp_existsUnique`,
`extendUnit_existsUnique`, `closureInclusion_comp`, `pairLinear_existsUnique`,
and `exists_ordinaryFieldRealization`; and
SfRationalDirectImageCoefficientCompatibility's
`sfRationalDirectImageCoefficientCompatibility`.

## No longer needed

The original plan's separate OpenFiniteConstructibilityInterval and
OpenRoosExtensionComparison imports and nodes are not used directly. The published
qcqs compact-support realization already supplies the complete constructible
integral object and its normalized finite reductions. The separate
`lem-weil-scalar-extension-composition` dependency is not used directly: coherence
of the left family is forced by adjunction mates and the existing coherent
pullback family. Their declarations remain available to other consumers.

The proof uses the individual normalized scalar comparison theorem, not
CompactSupportFiniteFieldIndependence or its coherent compact-support action.
Only the existence of each comparison is needed to establish invertibility of the
actual mate; the mate equations provide the coherence used in the proof.

Removed from the adapted modules: FieldStageOrdinaryRealization's private import
of SfCommonStageWeilCohomology, and the unrelated public import of
WeilIndSheafCategory in SfRationalDirectImageCoefficientCompatibility.
No Lean modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The planned finite-coefficient argument works, but its
constructibility and completion steps already have a published normalized
compact-support realization and need not be reconstructed here. The two unrelated
imports described above put later Weil-category consumers before the coefficient
construction and had to be removed to avoid an import cycle.

The ordinary-open helper declarations are elementary, already proved constructions
from the normalization module: `ordinaryOpen`, `openIdentity`, and `systemDirectId`.
Their use is stated explicitly in the node proof; the separated-scheme support
normalization theorem is not a proof dependency. No support comparison theorem
is used to prove itself through the later Weil category.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
