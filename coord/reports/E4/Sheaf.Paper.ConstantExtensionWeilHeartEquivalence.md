## What changed

Filled the two Frobenius return identities in
`Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` without changing any public
signature or definition. A private projection lemma iterates the two defining
Galois-map projection equations. A private field lemma identifies geometric
Frobenius over the extension field with the mth power over the original field,
using the cardinality formula and Mathlib's arithmetic Frobenius iterate theorem.
Pullback uniqueness proves the sheet return. Naturality of geometric Frobenius
then proves the fibre return by induction on positive powers.

Validation: the final single-module lcompile run passed without warnings or errors
in 20.9 seconds, with the reduced imports and exactly two named theorem holes.

The shared source changed during the initial reads: an initial snapshot had
four holes and included five elementary proofs recorded in the B2 proof review;
the subsequent source had nine holes again. This packet preserves those five
proofs as well: field properties, model properties, sheet compatibility, the
fibre-map isomorphism and closedness of the image. Those five are retained work,
not claimed as original discoveries of this session.

## Proved and sorry left

Holes closed relative to the nine-hole shared source:

- `WeilConjectures.constantExtensionField_properties` (retained earlier proof).
- `WeilConjectures.constantExtensionModel_properties` (retained earlier proof).
- `WeilConjectures.constantExtensionSheet_compatible` (retained earlier proof).
- `WeilConjectures.constantExtensionFiberMap_isIso` (retained earlier proof).
- `WeilConjectures.constantExtensionClosedImage_mem` (retained earlier proof).
- `WeilConjectures.constantExtensionSheet_return` (new proof).
- `WeilConjectures.constantExtensionFiber_return` (new proof).

The two holes left, both attached to
`lem-zl-constant-extension-weil-heart-equivalence`, are:

- `WeilConjectures.constantExtensionCyclicSheets`.
- `WeilConjectures.constantExtensionWeilHeartEquivalence`.

Holes added: none. No statement was split off. The new return proofs cover m=1
and empty schemes without case restrictions; the only arithmetic step is
m-1+1=m, justified by the original hypothesis 1 ≤ m.

## No longer needed

Removed these private imports, which neither the retained statements nor the
completed proofs use directly (the two existing public imports expose the
canonical definitions):

- `Sheaf.AlgebraicGeometry.ClosedPointField`.
- `WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorCoproduct`.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`.
- `Sheaf.CategoryTheory.SemilinearScalarLocalization`.
- `Sheaf.CategoryTheory.Triangulated.TStructure.HeartAbelianKernelSplitting`.
- `Sheaf.Paper.FiniteClopenDerivedDecomposition`.
- `Sheaf.Paper.FiniteFieldFiber`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
- `Sheaf.Paper.IntegralPointTransportTowerPowers`.
- `Sheaf.Paper.IntegralPullbackComposition`.
- `Sheaf.Paper.IsomorphismDerivedPullback`.
- `Sheaf.Paper.LocalFrobeniusTrace`.
- `Sheaf.Paper.SfConstructibleHeart`.
- `Sheaf.Paper.SfWeilSheafComplex`.
- `Sheaf.Paper.WeilPullbackLocalFrobenius`.
- `Sheaf.SixFunctors.FrobeniusPointTransportNatural`.
- `Sheaf.TraceFormula.PointTransportComposition`.

Kept the two public imports and added the private Mathlib finite-morphism import
needed for the retained finite-projection proofs. No DAG dependency, module or
declaration is withdrawn: the main equivalence and clopen-cover arguments remain
unfinished and retain their existing proof plan. Removing their unused private
imports here does not assert they are unnecessary for those future arguments.

## Where the brief, the DAG or earlier work was wrong

The main theorem's planned sheet-coordinate, local-return and pullback-return
modules use the definitions owned by this item and import this module. They
cannot be imported here without an import cycle. In the shared snapshot,
`ConstantExtensionSheetHeartCoordinates` also imports
`ConstantExtensionSheetHeartData`, which is absent from the current Lean tree.
This delivery does not alter their statements, dependencies or ownership.
The return identities proved here avoid these cycles by using only field
Frobenius and the pullback universal property.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
