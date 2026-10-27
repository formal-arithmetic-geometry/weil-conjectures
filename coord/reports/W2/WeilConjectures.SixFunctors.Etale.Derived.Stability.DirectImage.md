## What changed

Proved `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_isNoetherianRing`
in `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage`, with its complete
original signature and all existing public imports unchanged. Added six private proof
imports and two proved private helpers:
`torsion_forget_of_nsmul_id_eq_zero` and `torsion_heart_direct_image_bound`.

The proof follows the node's constant-module projection and geometric-stalk route.
It explicitly transfers the torsion abelian higher-direct-image bound to module sheaves,
uses the existing bounded-heart amplitude theorem on the tensors of K with arbitrary
constant modules, applies the stated torsion-object projection formula, and invokes the
geometric-stalk Tor test. The empty interval a > b is handled by proving K is zero.
No torsion assumption on the coefficient ring and no finite-generation assumption on
the tested module has been inserted. The finite-ring residue test is not used.

The dimension input is shortened to the already proved source declaration
`AlgebraicGeometry.topologicalKrullDim_pullback_le_of_field`. A new attachment node records
that existing theorem; no new Lean declaration or module is introduced for it.
The Noetherian theorem's node proof, proof dependencies and proof origin are updated.

Validation: the final item compiled through `lcompile.py` without errors or warnings
(42.9 seconds). All added Lean lines have at most 100 characters. The proof was compiled
repeatedly while resolving the exact forgetful, total/plus, over-base, and tensor interfaces.

## Proved and sorry left

Closed 1 of the item's 1 original holes:
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_isNoetherianRing`
(node `lem-sf-direct-image-tor-amplitude-noetherian`).

The item now has zero `sorry`. Added zero holes and split off zero statements.
Both new private helpers are completely proved. The new dimension node attaches a
completely written existing source proof; it adds no hole.

This is a proof from the existing stated dependencies, rather than a claim that all
transitive dependencies are closed. In particular, the already existing theorem
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_constant_of_torsion_object`
(node `lem-sf-projection-torsion-object-constant`, module
`Sheaf.AlgebraicGeometry.TorsionObjectConstantProjection`) still has its pre-existing
`sorry`, which this packet does not modify or add.

## No longer needed

Removed no existing public imports and withdrew no modules or declarations.
Every added private proof import is used:
`Sheaf.AlgebraicGeometry.TorsionObjectConstantProjection`,
`Sheaf.AlgebraicGeometry.Sites.TorsionAbelianDirectImageVanishing`,
`WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison`,
`Sheaf.CategoryTheory.BoundedHeartAmplitude`,
`Sheaf.AlgebraicGeometry.EtaleStalkTorTest`, and
`Sheaf.SixFunctors.GeometricStalkTensorConstantSingle`.

Removed these direct proof dependencies and their obsolete top-level tool approvals
from `lem-sf-direct-image-tor-amplitude-noetherian`:

- `lem-sc-fibre-dimension-after-base-change`
  (`Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`): the existing global
  field-extension dimension theorem supplies exactly the required numerical bound.
- `lem-weil-pbc-dimension-supremum-local-dimensions`
  (`WeilConjectures.Topology.DimensionSupremumLocalDimensions`): the main proof no
  longer calculates local dimensions or takes their supremum.
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
  (`WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`): the
  structural instances already available through the original public imports suffice.
- `lem-weil-pbc-module-sheaves-enough-injectives`
  (`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`): no separate application
  of this bundled existence theorem is needed by the existing derived-functor APIs.
- `prop-weil-pbc-kinjective-resolutions-exist`
  (`Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`): the proof uses the existing
  total-derived functor and its single-object comparison, without constructing a resolution.

These are removals from this item's direct proof route, not claims that their modules
are globally unused. In particular, the explanatory affine proof of the new dimension
attachment can still reach local dimension results indirectly. No unit statement or
realized unit step is removed or bypassed. The finite-coefficient theorem in the same
module and its separate node are unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original six mathematical steps work with the stated
interfaces. Explicit conversion between integer cohomology degrees and natural-number
higher-derived-functor degrees is necessary. The arbitrary-module projection theorem
requires bundled scheme-over-base instances; the proof constructs those from aX, aY and hf.
The separate local-dimension calculation and explicit existence packages are unnecessary.

No statement, definition, target signature, public import, or consumer was changed.
There are no forced adaptations or change records. The first delivery preflight
classified extra `omit` commands around the private helpers as scope changes; moving
the helpers before the finite-coefficient section eliminated those added commands.
The resulting file compiled cleanly again with the existing scope commands unchanged.

## New nodes

`lem-sf-field-extension-dimension-upper-bound`, in
`dag/nodes/sec-six-functors-basics/lem-sf-field-extension-dimension-upper-bound.json`,
attaches the existing
`AlgebraicGeometry.topologicalKrullDim_pullback_le_of_field` from
`WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension` (lines 61-79).
It states exactly the dimension inequality for a locally finite type scheme over a field
after any extension of the ground field, including empty schemes and without an extra
quasi-compactness hypothesis. Its affine-open proof is recorded from the existing source;
Stacks Tag 00P3 supplies the affine field-extension calculation. Mathlib searches by
LeanSearch, LeanFinder and grep were actually run and logged; none states the scheme
inequality. Searches of the DAG and blueprint found no existing node of this statement.
It is a proved-source attachment, not a split-off theorem or a moved hole.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
