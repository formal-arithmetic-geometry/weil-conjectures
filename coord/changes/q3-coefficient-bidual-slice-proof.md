# Coefficient bidual slice proof: private proof context and new source interfaces

## Reason

Complete `CategoryTheory.CoefficientBidual.slice_compatibility` using the fixed,
normalized restriction comparison. The proof requires private closed-adjunction
and shift helpers, and two new source modules. Preflight reports an interface
change because its textual command index includes the added section variables,
scoped options, local instance registration, and an `open ... in` prefix.
This record makes those commands and the new interfaces explicit for review.

## Old

The item has one unfinished theorem, `slice_compatibility`. Its public statement,
definitions, existing instances, and public imports are those of the shared source.
There are no declarations in either new module.

## New

The existing theorem's signature is preserved verbatim; the textual signature
comparison is identical. Only its proof changes. New private helpers use extra
section variables and scoped elaboration options. `dualRightOpCommShift` is a
proved private definition registered as a **local** instance for this module's
proofs; it does not add a global instance for importing modules. Existing public
instances are untouched. The preflight command index associates an added local
`open Pretriangulated.Opposite in` prefix with the theorem; this is not a change
to its binders or conclusion.

`Sheaf.CategoryTheory.RingedSiteSignedDualRestriction` introduces the constructed
`CategoryTheory.closedDualRestrictionIso` and the proved theorem
`CategoryTheory.ringedSiteSignedDual_restriction`.
`Sheaf.Algebra.Homology.RingedSliceHomSourceShift` introduces the narrower source
theorem `CategoryTheory.ringedSlice_hom_sourceShift`, whose whole body remains
`sorry`. Both new modules and declarations have new DAG attachments. No existing
definition, target, public import or adopted-source declaration changes.

## Users

The item `Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility` is held by
Q3 and uses the two new modules. The new
`Sheaf.CategoryTheory.RingedSiteSignedDualRestriction` uses
`Sheaf.Algebra.Homology.RingedSliceHomSourceShift`.
A search of the current Lean source finds no importing module or other textual
consumer of `slice_compatibility`. Its DAG parents keep the same declaration
attachment and statement; their mathematics is unchanged. No consumer fails to
compile, and no consumer adaptation is made or required. Review should verify
that the local instance registration has no exported instance effect and that
all original public signatures and non-theorem bodies remain identical.

## Status

landed 20261021T024155-L-3041028 2026-10-21 (merge of deliver/Q3/Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility)
