## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_closed_tensor_models`
with an explicit construction from a proved tensor statement and one smaller
remaining currying statement. The private
`closed_of_natural_currying` helper builds each tensor-right adjunction with
`Adjunction.mkOfHomEquiv`, derives its two naturality laws from a single
three-variable inverse-currying law, and proves evaluation naturality by applying
that law twice to identities. It also proves that the resulting transpose is the
supplied bijection. The item then combines the representative uncurrying equation
with the tensor models, signed swap and derived braiding square. The canonical
monoidal structure equality is reflexive. The public theorem signature and both
public imports are unchanged.

Added `NativeOrdinaryTensorRepresentatives` and
`NativeOrdinaryRepresentativeCurrying`, each with one public theorem and its DAG
node. The tensor theorem is proved directly: construct the balanced bicomplex
comparison, apply the signed total flip, transfer acyclic-test K-flatness, and
use the canonical localization tensorator. Conjugating the complex braiding
produces the signed swap; the localization's lax braided equation proves the
derived braiding square. The construction is proved over an abstract module
category and then specialized to native sheaves. Local instances cache the
recurring totalization and graded tensor instances, avoiding the repeated native
instance inference that caused the first concrete version to exceed 60 seconds.
These separate the tensor/symmetry localization from the Hom-set calculation;
neither asserts the original closed-structure existence statement. The latter
accepts any natural one-K-flat tensor model and constructs only bijections and
their representative equations. No definition chooses an undetermined witness from an unproved
existence statement. No existing shared definition, source-library declaration, consumer or
unit route is changed.

Validation: the main adjunction assembly compiled against the two signatures;
the direct tensor construction then compiled in 47.5 seconds. The delivery tool
checks the final packet, including the removal of unused section assumptions.

## Proved and sorry left

Original holes: one, in
`AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_closed_tensor_models`.
Its proof is now complete relative to the remaining currying statement.
`AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_tensor_representatives`
and every private tensor helper are proved without a hole. The generic
`closed_of_natural_currying` helper is also proved without a hole.

One hole is added, exactly the whole proof of a named public theorem:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_representative_currying`
  (`lem-sf-native-ordinary-representative-currying`).

This is a decomposition: one upper hole closed and one lower hole added, net
zero. The remaining native Hom normalization is not proved. Both new
statements retain arbitrary schemes and unbounded complexes; zero complexes and
the empty scheme impose no additional assumption. The tensor lemma has no Hom
parameter, and the currying lemma has no closed or symmetric structure in its
conclusion. Each is strictly a part of the original argument.

## No longer needed

Removed the following direct proof imports from the item:
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`,
`Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction`,
`Sheaf.Paper.NativeScalarForgetting`, and
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`.
Their corresponding nodes remain proof dependencies of the currying lemma;
they are not claimed as pruned from the transitive closure. The proved tensor
lemma uses none of these transport statements: its dependencies are
`lem-sf-ringed-derived-native-tensor` and the balanced tensor helpers in
`lem-sf-native-hom-precomposition-quasi-iso` and
`lem-sf-native-ordinary-tensor-identification`. The item now directly
imports only the two new proof modules. No existing module or DAG node is
withdrawn, and no unit-level step is bypassed. Modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The old node's prose combined
two analytic transport arguments with the formal packaging of an adjunction.
The ringed-site theorem does not directly state that native transport, and the
existing `nativeOrdinary_tensorRight_iso` only identifies a tensor after a closed
structure is already supplied. Therefore neither is a direct proof of this item.
The delivery proves the tensor calculation and the formal packaging, and makes
the remaining normalized currying calculation precise rather than renaming the
entire obligation again. The existing
unit record has no realized step that this refinement bypasses.

The chain-level calculations in `KFlatBifunctorTensorHom` confirm the native
row-sign and unsigned degree-zero currying convention, but that module imports
this item through `NativeWeilClosedForgetful` and `NativeWeilTensorTransport`.
`import_direction.py may` reports that importing it here would close a cycle.
It is therefore a reference for the remaining calculation, not an import of
this delivery.

## New nodes

`lem-sf-native-ordinary-tensor-representatives` in
`NativeOrdinaryTensorRepresentatives` states the natural one-K-flat total model,
signed complex swap and its braiding square for the canonical native monoidal
structure, without an internal Hom. Its source is Stacks 06YS/06YT/0FPT and the
native tensor portion of the original proof. It is proved using generic native
localization, without the original scalar-forgetting route.

`lem-sf-native-ordinary-representative-currying` in
`NativeOrdinaryRepresentativeCurrying` states natural Hom-set bijections and the
unsigned homogeneous uncurrying formula relative to a supplied natural tensor
model and the supplied Hom representatives. Its source is Stacks
08J9/0A90/0A8Z/0A97 and the Hom portion of the original proof. The parent DAG now
records these two steps and the proved adjunction assembly. Both new nodes carry
LeanSearch, LeanFinder, Loogle and source-grep searches. No change record is
needed because no existing interface or definition is changed.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
