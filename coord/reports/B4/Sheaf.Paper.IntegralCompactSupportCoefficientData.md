## What changed

Proved the two remaining theorems of
`Sheaf.Paper.IntegralCompactSupportCoefficientData` without changing their statements,
any definition, or the public imports. Added private proof imports, two private proved helpers for derived slice presentation
and tensor support, and the fully proved reusable ordinary slice-presentation theorem
`AlgebraicGeometry.Scheme.proEtaleOpen_slicePresentation`.

The actual open extension is an equivalence followed by slice extension. Its unit is
invertible because the open object is subterminal. Scalar restriction and tensoring
preserve the image of slice extension, so the relevant counits are invertible. The
specified mate and projection transpose are consequently composites of invertible
maps. The tensor argument uses an arbitrary first complex and a flat K-flat resolution
only of the second factor, without finiteness or quasi-compactness assumptions.

Updated the coefficient-data and intrinsic-projection DAG proof records to match
these arguments and added the slice-presentation node. No source-library module or
other consumer was edited. Instance selection is adjusted only within the affected
proof declarations to avoid unrelated max-universe site instances.

## Proved and sorry left

Closed the two original holes:

- `WeilConjectures.PurCompactSupport.openRestrictionMap_isIso`
  (`def-pur-integral-compact-support-coefficient-data`).
- `WeilConjectures.PurCompactSupport.openProjectionInverse_isIso`
  (`lem-sp-intrinsic-open-projection-invertible`).

There are zero `sorry` declarations left in the item and zero holes added or split off.
The five theorems already proved by Y9 are retained.

## No longer needed

No existing import was removed: the existing public imports belong to the unchanged
coefficient-data interface and the retained proofs still use their previous private
imports. The new proof imports are used for the slice presentation, the slice unit
and tensor-support helpers, mixed K-flat tensor representatives, and scalar/slice
extension comparison.

The intrinsic projection proof no longer uses its old direct proof dependencies
`lem-cbc-extension-zero-projection-formula` (`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`),
`lem-cbc-proetale-extension-zero` (`Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`), or
`lem-sf-open-tensor-support` (`Sheaf.SixFunctors.OpenTensorSupport`). Those nodes are
replaced in its proof record by the actual arbitrary-ring slice argument. This does
not withdraw their modules or assert that other consumers no longer need them.

## Where the brief, the DAG or earlier work was wrong

The current restored item already contained Y9's proofs of five of its former seven
holes. This delivery starts from that restored source, preserves those proofs, and
closes the two remaining holes. The old quarantine row and pre-sync return do not
require removal of the current module or of its Lean attachment.

The old projection proof plan cited interfaces for fixed or finite coefficient
presentations. The current statement permits arbitrary coefficient ring sheaves,
arbitrary derived tensor factors and any open immersion. The slice essential-image
argument proves exactly that statement without restricting it. The scalar mate proof
does not require choosing mutually compatible slice equivalences: preservation of
the essential image suffices.

## New nodes

`lem-sp-proetale-open-slice-presentation` records the fully proved theorem in
`Sheaf.AlgebraicGeometry.ProEtaleOpenSlicePresentation`. It refines the existing
ringed-open comparison and left-adjoint construction by retaining the equivalence
and the open-extension natural isomorphism. It is a genuine geometric component
shared by the two proofs, and introduces zero holes. Its separate module avoids a
public/private scalar-adjunction name collision in the large coefficient interface.
No change record is required: no existing statement, definition or public import changed.

The combined sandbox compile checked both modules. The final item compiles cleanly
in 38.0 seconds after marking chosen-adjoint/derived-functor and canonical comparison
definitions locally irreducible, preventing expensive speculative unfolding. These
are proof-local transparency settings; no definition body changed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
