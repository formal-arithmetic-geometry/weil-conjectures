## What changed

Restored the quarantined module
`Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
to its original Lean path. Removed four dangling `omit ... in` commands left by the
upstream-verbatim extraction. These had been attached to declarations now supplied by
the public upstream import; in the extracted file they incorrectly scope a `variable`
command and `end CoefficientMap`. Wrapped the extraction comment to 100 columns.

Preserved every import and the four concrete definitions verbatim:
`AlgebraicGeometry.ProEtale.CondensedRing.derivedPushSource`,
`AlgebraicGeometry.ProEtale.CondensedRing.derivedPushTarget`,
`AlgebraicGeometry.ProEtale.CondensedRing.derivedLowerShriekSource`, and
`AlgebraicGeometry.ProEtale.CondensedRing.derivedLowerShriekTarget`.
The source library is untouched. The restored file compiled through lcompile.py in
22 seconds, without errors or warnings. Change record:
`coord/changes/F1-coefficient-comparison-scope-restoration.md`.

## Proved and sorry left

This is the assigned zero-hole rework repair, not a proof decomposition.
Original holes: 0. Holes closed: 0. Holes added: 0. Holes remaining: 0.
All four definitions above construct the same composites as in the archive; no data
or proofs were replaced. There are no new theorems or assumptions.

## No longer needed

None. All six public imports, all four definitions, and all dependencies are retained.
The quarantined consumer `Sheaf.Paper.ProperBaseChangeRational` imports this module
and mentions `derivedPushSource` and `derivedPushTarget` in a local attribute command.
It requires no adaptation because their names, visibility, signatures and bodies are
unchanged. No module is withdrawn; the quarantine archive is left intact.

## Where the brief, the DAG or earlier work was wrong

The rework row accurately identifies the parser failure at `end CoefficientMap`.
The extraction retained four scoped `omit ... in` commands after moving their associated
lemmas back to the upstream import. Removing those orphan commands repairs the actual
failure. The item has no attached DAG node (searched the module name and all four names
through dag/nodes); there is no proof route, dependency, or Lean attachment to change.
No current return entry for this item is present in coord/returns/F1.md.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
