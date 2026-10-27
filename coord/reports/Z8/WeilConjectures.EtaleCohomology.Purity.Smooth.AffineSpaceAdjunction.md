## What changed

The adopted source module `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceAdjunction`
now proves its original theorem
`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace` by
induction on the dimension. Its signature, visibility and public imports are unchanged.
The geometric input is the projective-line adjunction for the same normalized Tate
parameter. From it the private `affineLineAdjunction` composes the standard open-chart
adjunction with the proper projective-line direct image and transports along the explicit
compactification. The zero-dimensional case uses the isomorphism of affine zero-space
with the base. A private dependent congruence transports compactification-dependent
functors along equality of scheme maps without unfolding their constructions.
The successor case uses reindexing, the affine-space sum isomorphism,
composition of compactly supported direct images, and explicit pullback/twist isomorphisms.
All functor isomorphisms, including zero twist, pullback of a twist, addition of twists,
and the coordinate-tower comparison, are constructed by proved private helpers.
The completed private isomorphism definitions are irreducible to avoid repeated
unfolding of the large derived-functor constructions during type checking.

Private proof imports are `Sheaf.SmoothPurity.NormalizedProjectiveLineAdjunction`,
`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek`,
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`,
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso`, and
`WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor`.
There is one new public theorem, in its own new Sheaf module, and two new node records.
There are no changed definitions or statements, no forced consumer adaptations and no
change record is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace`.
The item module has zero remaining holes. Its induction and the affine-line reduction
are complete Lean proofs.

Added one hole:
`AlgebraicGeometry.Etale.nonempty_normalizedProjectiveLineAdjunction`, in
`Sheaf.SmoothPurity.NormalizedProjectiveLineAdjunction`, attached to
`lem-normalized-projective-line-adjunction`. This is the projective-line input of the
blueprint argument, with arbitrary base and the adopted normalized Tate parameter.
It contains neither the affine open-chart argument nor any coordinate-tower induction.
Consequently this delivery is a decomposition, with one upper hole closed and one lower
hole added, not a net elimination of the geometric duality hole.

Edge checks for the new statement: the empty base and the zero coefficient ring give
zero categories and admit the asserted adjunction. Over a geometric point, the statement
is the usual projective-line trace adjunction with shift two. No positivity assumption on
the coefficient characteristic or nonzero-ring assumption was added. The two homogeneous
coordinates are exactly `Option (ULift (Fin 1))`; the formula agrees with the existing
relative-projective-space chart used for affine one-space. The arbitrary-base and
normalized-datum scope is retained explicitly, rather than silently applying a
Noetherian/concrete-coefficient theorem to it.

## No longer needed

No original public import was removed, and no module is withdrawn or claimed globally
pruned. The broad private `Derived.Composition` import considered while developing the
proof was narrowed to `Derived.LowerShriekComposition`.

The assigned source theorem does not need to import the distinct explicit finite-Tate
route through `Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction` or
`Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunctionCore`. Nor does it need their
Noetherian projective-line wrapper `Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction`
or the explicit finite-coefficient affine-base wrapper
`Sheaf.AlgebraicGeometry.SfAffineBaseP1TraceAdjunction`. These are not removed: they have
independent public statements and their existing nodes and consumers stay intact.
The new geometric input still needs the projective-line trace/diagonal argument, so its
underlying geometric dependencies are not claimed pruned. No sheaf-Ext recognition,
abstract affine-local purity theorem or higher-dimensional geometric input is imported:
the dimension step is ordinary composition, proved here. No unit statement or realized
unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The source module's docstring names `cor-amb-affine-space-adjunction`, but that node's
current Lean attachment is the different declaration
`AlgebraicGeometry.nonempty_affineSpaceAmbientAdjunction` in
`Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction`. That declaration uses an explicit
finite roots-of-unity Tate sheaf and a Noetherian base; the assigned theorem uses an
arbitrary normalized `HasTateTwist` datum over an arbitrary base. The source theorem has
no current DAG attachment. Repointing the old attachment would lose that distinct
statement. The delivery therefore preserves it and records the exact source theorem in
`cor-normalized-affine-space-adjunction`.

Likewise the available concrete projective-line adjunctions do not accept the parameter
of the assigned theorem. The new projective-line statement records that missing
interface without assuming a definitional equality of the two twist models. Its
source is the current blueprint's diagonal-kernel construction and two triangle
identities, the geometric input explicitly invoked by the affine-space proof.

Searches were run with the launcher search tool (LeanSearch, Loogle/LeanFinder and grep),
and with repository `rg`. Their queries and actual results are recorded in the new
nodes. The Mathlib results concerned ordinary sheaf/module pullback adjunctions and
preservation of projective objects; none supplied the twisted projective-line or
affine-space statement. Blueprint searches found the concrete adjunction nodes, whose
coefficient/base interfaces were checked before writing the new statement.

## New nodes

`lem-normalized-projective-line-adjunction` attaches the sole new holed theorem in
`Sheaf.SmoothPurity.NormalizedProjectiveLineAdjunction`. It is the first geometric
input in the blueprint affine-space proof, and states exactly the projective-line
adjunction needed before restriction to the affine chart. Its docstring and node give
the diagonal-kernel unit, trace counit and both triangle computations.

`cor-normalized-affine-space-adjunction` attaches the already existing adopted-source
theorem. Its proof record follows the actual Lean proof: the open-chart composition,
the explicit twist calculus, the zero-dimensional isomorphism, and coordinate induction.
The node statements spell out the source Tate and Kummer parameters in full: the
concrete coefficient-twists node is not treated as their definition.
It records the relationship to the existing concrete affine-space blueprint node while
preserving that node's current attachment. No new public source declaration is added.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
