## What changed

The statement and the two existing comparison definitions of
`Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging` are unchanged. The main proof
first identifies projections by definitional equality of the retained compactification.
It then compares the inverse-projection/counit words by naturality, and compares their
actual adjoint transposes using the full realization and the counit-preserving
`Adjunction.rightAdjointUniq` isomorphism. All categorical helpers are private and proved.
The new proof import is `Sheaf.Paper.TowerTensorAdjointDomains`. Both delivery
modules compile without errors or warnings through `lcompile.py --all`.

The domain-only part of gamma clause (2) is isolated as a named theorem in that new
module. It supplies normalized tensor models, coefficient-unit membership, tensor-source
membership and invertibility of the specified projection. It asserts no retagging or
comparison equation. The item node records the implemented route and the new node.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.SpTowerTensorRetagging.tensor_transpose_ground_field_retagging`
(node `lem-pur-tower-tensor-transpose-ground-field-retagging`).

Added one hole:
`AlgebraicGeometry.ProEtale.SpTowerTensorRetagging.tensor_adjoint_domains`
(node `lem-sp-tower-tensor-adjoint-domains`), in its own module. Its body is exactly
`by sorry`; its docstring and node give its source and complete argument. This is a
one-for-one decomposition, not a net proof closure. The item module has zero holes;
the delivery has one. No definition contains a hole.

## No longer needed

No existing public imports were removed. The proof does not use the theorem
`sp_tower_operations_ground_field_retagging`: the compactification-retagging definition
already retains exactly the same record. The operation module remains needed for those
public definitions and the theorem signature. The generic exchange-projection theorem
is not used separately: the concrete `SpTowerShriek.projection` definition and
`Operations.openTensor_mate` give the full naturality calculation directly.

Thus `def-exchange-projection` is removed from the item's proof dependencies, while its
statement dependency and public import stay. No module is withdrawn and no unit route
is bypassed. The other original dependencies remain needed for the actual definitions,
full subcategories, or the new domain lemma.

## Where the brief, the DAG or earlier work was wrong

The old argument describes gamma clause (2)'s domain witnesses without exposing a
standalone theorem giving them for the arbitrary adjunction and compactification in
this statement. The existing `tower_gamma` theorem requires finite-level and twist data;
`twisted_pullback_tower_domain` additionally requires a diagonal orientation and its
finite normalization equations. Neither can simply be applied with the present inputs.
The new node extracts precisely the missing domain conclusion. The actual comparison
argument needs no orientation and no faithfulness of finite evaluation.

## New nodes

`lem-sp-tower-tensor-adjoint-domains`, in
`dag/nodes/sec-six-functors/lem-sp-tower-tensor-adjoint-domains.json`, is attached to
`AlgebraicGeometry.ProEtale.SpTowerTensorRetagging.tensor_adjoint_domains` in
`Sheaf.Paper.TowerTensorAdjointDomains`. It is strictly the domain and
projection-invertibility part of gamma clause (2). The retagging statement's projection
equality and its two comparison equations are all omitted. No existing definition body,
signature or public import changed. Local proof attributes keep derived functor
constructions irreducible while checking the comparison; these attributes do not
change the public interface.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
