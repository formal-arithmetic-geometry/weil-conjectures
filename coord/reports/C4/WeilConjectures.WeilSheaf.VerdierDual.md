## What changed

Prove AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso
by the native scalar-valued Hom chain and explicit representing-object inverses.
The private exists_dualizing_hom_equiv helper proves tensor--Hom transposition
and its naturality from the actual native closed structure and the chosen
structural adjunction. No theorem is added with sorry.

Extract the existing tensor block of Sheaf.Paper.DerivedWeilOperations verbatim
to Sheaf.Paper.DerivedWeilTensorOperations. The old module publicly re-exports
it and retains its unchanged Verdier declarations. Four unclaimed tensor
modules use the lower import. WeilCompactStructureTensorComparison now names
its public tensor dependency directly, so the complete comparison dependency
chain is compiled before the item in the delivery packet. This removes the circular proof dependency that
otherwise prevents importing the existing compact structure tensor comparison.
NativeOpenDerivedTensor is also split for the per-file compile limit:
NativeOpenTensorPresentation holds its unchanged generic normalization records,
and NativeOpenTensorOperations holds its unchanged concrete operations and
representative/forget maps. The original module re-exports both and keeps its
data records and theorem unchanged. These are relocations, not new statements.
The change record is coord/changes/C4-native-derived-tensor-layer.md.

Validation: lcompile.py accepts the item, the extracted modules, all adapted existing modules, and the unchanged direct consumer
NativeWeilDualizingHomTransposition. The unchanged consumer copy was removed
after its check. The structure comparison's declarations and proofs are unchanged;
its tensor layer import is now explicit. No profiling
options or heartbeat-limit increases are present.

## Proved and sorry left

Closed 1 of the item's original 4 holes:
AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso
(lem-sf-weil-verdier-exchange). This proof uses the existing projection-formula
and closed-structure dependencies; it adds no holes and no decomposition.

The 3 original holes left in the item are:

- AlgebraicGeometry.WeilComplex.nonempty_iso_verdierDual_rightOp_comp_verdierDual
  (lem-sf-weil-verdier-biduality).
- AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_iso
  (lem-sf-weil-upper-shriek-verdier-conjugate).
- AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso
  (lem-pur-weil-smooth-dualizing-complex).

The adapted existing modules retain these existing holes unchanged:

- AlgebraicGeometry.WeilComplex.native_compact_projection_formula
  (lem-sf-derived-weil-compact-projection-formula).
- AlgebraicGeometry.ProEtaleWeilSheaf.nativeGeometricForget_tensorComparison
  (lem-sf-native-geometric-tensor-comparison).
- AlgebraicGeometry.ProEtaleWeilSheaf.native_open_derived_tensor
  (lem-sf-native-open-derived-tensor).

The three extracted modules and other adapted modules have zero holes.
No holes are added anywhere in this delivery.

## No longer needed

The exchange proof does not import Sheaf.Paper.NativeWeilDualizingHomTransposition:
that module imports the item itself. Its tensor--Hom argument is implemented as
a proved private helper, directly from the existing native closed comparison.
No new obligation replaces it. This is a dependency pruned from this proof only;
the existing declaration and module remain intact.

The standalone preservation dependencies
lem-sf-native-weil-pullback-star-preservation and
lem-sf-native-weil-shriek-triangulated need no separate applications here: the
operations already take values in the actual WeilComplex full subcategories.
Their existing upstream declarations and imports are preserved.

Four lower tensor modules replace the import Sheaf.Paper.DerivedWeilOperations
with Sheaf.Paper.DerivedWeilTensorOperations; every tensor declaration used there
is unchanged. The structure comparison explicitly imports the lower tensor
module used in its public statements. No source-library public import is removed, no existing declaration
is removed, and no module is withdrawn. The original unit route is retained.

NativeOpenDerivedTensor removes these unused private proof imports:

- Sheaf.CategoryTheory.LocalizedModuleExactForSystems
- Sheaf.CategoryTheory.FixedPairCreatedAbelianStructure
- Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat
- Sheaf.CategoryTheory.RingedSliceTensorGenerators
- Sheaf.CategoryTheory.TwistedActionRingedSite
- Sheaf.Paper.WeilFrobeniusActionResolutions
- Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

Its unused public import of OpenTensorNormalization is removed; the file uses
its own normalization records. ExactDerivedAdjunction is imported publicly
because its derived adjunction occurs in public structure fields. The native
closed comparison is locally
irreducible during elaboration, avoiding expansion of its large constructed
model when checking normalization types. This local attribute changes no
exported reducibility setting. The existing unproved
native_open_derived_tensor and its planned mathematical dependencies are retained;
these proof imports can be restored when its proof actually uses them. No proved
body is replaced, and no dependency node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The declared exchange dependencies cannot originally be imported by the item:
NativeWeilDualizingHomTransposition imports VerdierDual directly, and
WeilCompactStructureTensorComparison reaches it through DerivedWeilOperations.
The latter file bundled lower tensor operations with later duality definitions.
The local delivery compile also needed the structure comparison rebuilt: the old
compiled consumer still carried the previous transitive Verdier import. Its
explicit lower tensor import records its actual public dependency and makes the
whole repaired chain part of this delivery.
Extracting the unchanged tensor layer resolves the latter cycle; the private
transposition proof resolves the former without changing the existing lemma.
The mathematical Hom-chain plan is valid, including the empty-scheme and zero
object cases: it only uses equivalences and identities and needs no nonzero or
connectedness hypotheses. No statement or target meaning changes.

## New nodes

- def-sf-native-derived-tensor-layer records the tensor-only construction component
  of the existing derived operations node, attached to DerivedWeilTensorOperations.
- def-sf-generic-open-tensor-presentation records the generic normalization records
  and presentation types, a component of the existing native presentation-data node.
- def-sf-native-open-tensor-operations records its concrete native operation and
  representative-map component, attached to NativeOpenTensorOperations.

All three are definition records for existing declarations relocated unchanged;
none adds a mathematical object or a sorry. The original broad nodes remain valid,
and the exchange proof cites these component constructions. The change record is
coord/changes/C4-native-derived-tensor-layer.md.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
