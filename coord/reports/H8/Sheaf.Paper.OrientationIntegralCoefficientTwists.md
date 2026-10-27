## What changed

Replaced the proof hole in `WeilConjectures.sfOrientationIntegralPullUnit_isIso` by the
ambient completion argument. The ordinary pullback is identified with the shifted
root line on the source. Intrinsic constructibility makes that line complete; the
legacy comparison and the normalized Roos criterion make its specified completion
unit invertible. The representative comparison then gives invertibility of the
ordinary-to-completed augmentation.

Added `Sheaf.Paper.IntegralPullbackAugmentationAmbient` for the identity between the
two existing ordinary pullback presentations and their actual augmentations. This
identity applies to arbitrary complexes and schemes and retains both Roos components.
The existing item signatures, definitions, public imports and instance attributes
are unchanged. The new module is imported only for the proof. The item node records
the new argument. No adopted source-library file is changed.

## Proved and sorry left

The original item had three holes. The delivery closes
`WeilConjectures.sfOrientationIntegralPullUnit_isIso`.

Two original holes remain unchanged, both attached to
`def-sf-orientation-integral-line-comparisons`:

- `WeilConjectures.sfOrientationIntegralLineMaps_existsUnique`.
- `WeilConjectures.sfOrientationIntegralComplexProduct_existsUnique`.

`WeilConjectures.integralPullbackAugmentation_ambient` is proved with no proof holes.
Its private generic mapping-cocone extensionality helper is also proved. No holes
are added: one original hole is closed and two original holes remain. The new
proof uses the existing stated line comparison, ambient tower comparison and
completion criteria; those downstream proof obligations remain with their nodes.

Validation: `lcompile.py --all` accepted both modules without warnings. The new
module contains zero `sorry`; the item contains exactly the two named original
holes above. No axiom declaration, target change or definition change is added.

## No longer needed

No existing imports, declarations, modules or nodes are withdrawn. The original
flatness and tensor-unit proofs still use all the original proof dependencies.
For the pull-unit proof no separate surjective-tower/vanishing-higher-limit lemma
is needed: completeness of the source line and the existing normalized Roos
criterion supply the result. No such additional module was imported or created.

## Where the brief, the DAG or earlier work was wrong

The last previous proof step explicitly left all three holes open. The pull-unit
hole can instead use the existing completion infrastructure, once the two ordinary
pullback presentations are compared. The existing Frobenius augmentation theorem
requires an isomorphism of schemes, so it cannot be applied to the arbitrary map in
this item. No statement is disputed or weakened.

## New nodes

`lem-sf-integral-pullback-augmentation-ambient` compares the actual chain-level
augmentations for every input complex. It identifies the completed structural
maps by their projections, compares the left adjoints through their shared right
adjoint, and compares the two Roos coordinates. This is a normalization identity,
not the invertibility assertion under another name. It requires no completeness
hypothesis and does not introduce a choice of a line trivialization. Zero
complexes, empty schemes, the identity map and degree zero all obey the same
adjunction and coordinate calculation. No change record is needed because all
existing public signatures and definitions are retained.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
