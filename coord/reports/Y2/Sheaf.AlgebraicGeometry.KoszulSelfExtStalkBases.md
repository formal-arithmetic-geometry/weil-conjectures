## What changed

`Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases` now combines a local self Ext
pullback frame with an explicit, fully proved finite-coordinate stalk calculation.
Its exterior-stalk conclusion is proved from the existing Koszul conormal basis,
affine conormal frame, finite-free internal duality, and exterior local-free comparison.
The existing public theorem has exactly its original signature and visibility.
Added proof imports of `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`, and the new chart-frame module.
All original public imports remain unchanged. Helper parameters are explicit: no new
module-scoped variable or open commands alter the importing modules' interface.

The private coordinate-germ helpers follow the already proved helpers in
`Sheaf.AlgebraicGeometry.AffineConormalFrame`. Those helpers are private and therefore
cannot be imported. Their cocone, scalar-linearity, delta-coordinate and reconstruction
proofs are retained here, without any holes. The additional restriction helper uses
`restrictFunctorComp`, `restrictCompIso`, `overIsoFreeEquiv` and `restrictFreeIso`.
No object is defined by an arbitrary witness from an unproved existence theorem.
All free frames obtained from propositions are used only inside theorem proofs.

Added `Sheaf.AlgebraicGeometry.KoszulSelfExtPullbackLocalFrame`, which isolates the
remaining affine derived calculation as a chart-level free sheaf statement. It has
no point, no auxiliary open V, and no conormal-dual or exterior-stalk assertion.
Its proof in words follows the zero-differential Hom calculation in Stacks Tag 0BQY,
read online. The original node copy now records the actual two branches of the Lean proof.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.koszulRegularImmersion_self_ext_stalk_bases`
(node `lem-sc-koszul-self-ext-stalk-bases`). No sorry remains in the item's module,
including any private helper.

Added one hole:
`AlgebraicGeometry.koszulRegularImmersion_self_ext_pullback_local_frame`
(node `lem-sc-koszul-self-ext-pullback-local-frame`), in its own new module.
It supplies only the affine sheaf frame used in the first branch. The independent
exterior branch and both transports from frames to stalk bases are complete Lean proofs.
This is a decomposition: one upper hole closed, one lower hole added, net zero holes;
it is not claimed as a fully axiom-free proof of the target closure.

The coordinate proofs use arbitrary finite index types and cover the empty type.
At n=0 the subset index is a singleton; at n>m it is empty. At m=0 the conormal
and its positive exterior powers are zero. Empty inverse-image charts are allowed
by the new frame statement, while a stalk in such a chart cannot occur. No
regularity outside U, nonzero quotient hypothesis, or derived-universe restriction
has been added.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.RingTheory.KoszulProjectiveResolution`
- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`

They are retained as the proof dependencies and proof imports of the new local-frame
module, so they are not pruned from the target closure. The conormal basis, conormal
frame and exterior local-free comparison remain directly used. No node or module
is claimed as globally pruned. The unit's realized routes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG's second step supplies usable declarations, but the generic frame-to-stalk
linear equivalence is private in the existing proved modules. Its proof had to be
reused locally. The first step's declarations do not by themselves expose the final
zero-differential cohomology and quotient-pullback frame; that missing combination
is isolated in the new statement rather than hidden by a sorry in the main proof.
No statement was found false and no existing interface was changed.

LeanFinder returned cotangent and formally unramified base-change results, Loogle
returned free-sheaf and basis APIs, and source grep found no independent self Ext
local-frame statement. LeanSearch returned Internal Server Error; this is recorded
as unavailable, with no inference of absence. Whole-blueprint searches for self Ext
and 0BQY found no match.

## New nodes

`lem-sc-koszul-self-ext-pullback-local-frame` states the affine derived self Ext
calculation after ordinary tensor pullback, before any stalk or conormal-exterior
comparison. Its four existing dependencies are the actual Koszul resolution,
affine quotient resolution sheafification, restriction of derived internal Hom,
and the bounded-above finite-free Hom model. Its docstring and node give the
zero-differential calculation, localization compatibility, quotient tensor
multiplication, universe comparison and edge cases. It inherits the parent's
chapter and unit and follows the same blueprint ancestor. No change record is needed.

## Second reading by Y2

1. Compared the delivered stalk-bases module with the repository version. The public theorem
   signature is byte-for-byte unchanged; only proof imports, private helpers, and proof bodies
   changed. The added local-frame module and node are explicitly listed.
2. Compiled both delivered modules with `lcompile.py`; there are no errors, forbidden commands,
   or hidden `sorry`s. The sole remaining `sorry` is the named split theorem and its node.
3. Checked the split statement against the affine zero-differential Koszul calculation and its
   edge cases (degree zero, degree above m, m=0, and empty inverse-image charts). It is strictly
   below the stalk-bases target and has a source, docstring, and matching DAG node.
4. Reviewed the proof route and imports. The stalk theorem uses the new frame, conormal frame,
   and exterior comparison; removed direct imports are retained only where the split proof uses
   them. The unit's realized route is preserved and no unnecessary node is claimed pruned.
5. Checked the DAG proof steps, dependencies, origins, and Lean records against the actual
   declarations. They agree; no existing declaration is duplicated or weakened.

Changed during second reading: no Lean statements or definitions; added this review record only.
