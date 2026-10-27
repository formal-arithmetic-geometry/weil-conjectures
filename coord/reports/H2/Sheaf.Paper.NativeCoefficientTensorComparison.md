## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeCoefficient_tensorComparison`, keeping its
statement and all binders verbatim. The proof first identifies the supplied tensor
with the standard native derived tensor, equips coefficient transport with a strong
monoidal structure, and applies the existing generic derived monoidal comparison.

Added `Sheaf.Paper.NativeOrdinaryTensorIdentification`. Its proved theorem
`nativeOrdinary_tensorRight_iso` compares the two ordinary module tensors, conjugates
their adjunctions to identify internal Homs, identifies the product-total Hom complexes,
and extends the representative isomorphism from K-injectives by localization. Uniqueness
of left adjoints then identifies the supplied closed tensor with the canonical tensor.
The previously proved generic private tensor and Hom-complex comparison helpers in
`Sheaf.WeilSheaf.NativeHomPrecompositionQuasiIso` are reused with `import all`.

Added `Sheaf.Paper.NativeScalarForgettingMonoidal`. Its proved theorem
`nativeScalarForgetting_monoidal` constructs a strong monoidal left adjoint to forgetting:
free ambient modules followed by extension along the counit on the coefficient algebra.
The right triangle identity identifies its right adjoint with the literal existing
forgetful functor. Since forgetting is an equivalence, uniqueness of right adjoints
transfers the inverse monoidal structure back to it. The existing strong monoidality of
extension of scalars is used, rather than introducing a new balanced-tensor obligation.

The ordinary comparison is written over abstract module and derived categories, so
Lean does not repeatedly unfold the native sheaf instances. Limit and colimit instances
are cached locally for its generic comparison constructions.

All proof imports are private imports. No existing definition or statement was changed,
and no source-library module was edited. The only direct user of the main theorem is
`Sheaf.Paper.NativeGeometricHomComparison`; its application has exactly the same type.
The existing unit route is preserved; this item's unit record has no realized step
that this proof bypasses.

Validation: the three modules compile together in import order. The unchanged direct
consumer `Sheaf.Paper.NativeGeometricHomComparison` also compiles; its temporary
copy was removed from this packet. `#print axioms` for
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeCoefficient_tensorComparison` reports
exactly `propext`, `Classical.choice`, and `Quot.sound`. Temporary profiler options
were removed before delivery.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeCoefficient_tensorComparison`
(`lem-sf-native-coefficient-tensor-comparison`).

Both new public helper theorems have complete proofs:
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeOrdinary_tensorRight_iso` and
`AlgebraicGeometry.ProEtale.nativeScalarForgetting_monoidal`.

Holes closed: 1. Holes added: 0. There is no `sorry` in any delivered Lean file.
This is a proof from existing declarations, not a decomposition into new holes.

## No longer needed

No original public import is removed. `PadicIntModuleComparison` supplies the
exactness and additivity instances for sheaf composition with scalar forgetting;
`DerivedExtendScalars` supplies exactness of restriction of scalars. These instances
are needed to elaborate the existing statement. No module is withdrawn.

The parent proof no longer uses
`lem-pc-sites-sheaf-tensor-bilinear-universal`: the ordinary monoidal structure is
obtained from the monoidal left adjoint and inverse equivalence. It also does not need
a separate native coefficient totalization, differential-sign, K-flatness, or localization
comparison lemma: the existing `Functor.mapDerivedCategoryTensorComparison` supplies that
argument for the standard derived tensors. No such new obligations were created.

The `NativeOrdinaryTensorModels` hypothesis is retained verbatim but is not needed by
this proof. Naturality of `NativeHomRepresentatives` and the supplied closed adjunction
already determine the source tensor up to the natural isomorphism needed here. This does
not withdraw the model definition or its other users. The other original material
proof dependencies remain in use, directly or in the proved helpers.

## Where the brief, the DAG or earlier work was wrong

The original plan needlessly repeated the generic derived monoidal-functor argument.
The library already has this result, including invertibility for an exact monoidal
flat-preserving functor. The missing ordinary monoidality can also be obtained from
already stated and proved free-module, scalar-extension and inverse-equivalence APIs.
Thus neither a third restatement of the coefficient-derived comparison nor a new
underived tensor hole is necessary.

The arbitrary supplied closed structure requires a genuine identification with the
canonical derived tensor before using that generic comparison. This delivery supplies
that identification from the natural Hom representatives, rather than silently treating
the two monoidal instances as definitionally equal. The braiding in the final composition
corrects the fixed-right/fixed-left convention explicitly.

## New nodes

`lem-sf-native-ordinary-tensor-identification` records the proved native-only tensor
identification, with no coefficient change or scalar forgetting. Its public statement
is strictly separate from the main coefficient-transport assertion.

`lem-sf-native-scalar-forgetting-monoidal` records the proved underived strong monoidality
of the literal scalar-forgetting functor, via its monoidal inverse. It contains no
complexes, derived categories, or arbitrary supplied closed structures.

Both nodes have complete source proofs, actual search records, Lean signatures and
blueprint provenance. The parent node's proof and proof dependencies were updated to
match the implemented route. No change record is needed: no existing signature or
definition changed.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
