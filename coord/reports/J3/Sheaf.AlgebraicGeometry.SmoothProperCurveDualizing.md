## What changed

Restored `Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing` from the rework archive.
Replaced the proof import of the withdrawn Sheaf exterior-one module with the proved
`WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafOneIso`, and added the private
proof import `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafComparison`.

The proof first specializes `smoothProper_dualizing` to `Spec k` and degree one.
It composes `eqToIso (exteriorSheaf_eq_exteriorPower ...)` with the upstream degree-one
isomorphism, maps this through the degree-zero single functor and shift by one, and
composes with general duality. The theorem signature, universes, docstrings, visibility
and public imports are byte-for-byte preserved from quarantine.

The restored module compiled through `lcompile.py` in 3.6 seconds with no warnings.
The sole quarantined direct importer, `SmoothCurveUpperShriekDifferentials`, also
compiled unchanged against the repair in 32.8 seconds (the item took 15.8 seconds in
that two-file check). Its temporary source copy was removed before delivery.
Both added imports pass `import_direction.py may`. The current node already describes
this exact proof and names all three dependencies; no node update is needed. The unit
route is preserved, and no adopted source-library file is changed.

Change record: `coord/changes/J3-smooth-proper-curve-dualizing-restoration.md`.

## Proved and sorry left

`AlgebraicGeometry.smoothProperCurve_dualizing` has a complete repaired proof from the
existing named declarations. This is a zero-hole rework assignment: zero direct holes
before, zero direct holes after, zero holes closed and zero holes added. No statements
were split off. There are no remaining `sorry` declarations in this delivery. Imported
general-duality dependencies retain their existing proof status.

## No longer needed

Removed the obsolete private import
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafOneIso`, an already withdrawn empty module,
in favor of its adopted source-library theorem. No mathematical node or declared proof
dependency is pruned. The general-duality node, degree-one exterior node, and upstream
comparison node all remain used. No declaration is withdrawn by this delivery.

## Where the brief, the DAG or earlier work was wrong

The quarantined proof still imported the retired Sheaf twin, so its theorem name was
unknown. Importing the adopted theorem alone would not fix the proof: its conclusion
uses `exteriorPower`, requiring the explicit comparison with `exteriorSheaf`.
The 2026-10-20 retirement change record and current curve node already describe this
repair; the archived source had not yet incorporated it. The quarantine archive and
its Lean attachment are preserved.

Checked the current rework row, current build errors, J3 returns, the three dependency
signatures, and the unit record. No J3 return entry is specific to this module.
Lean Finder returned differential constructions rather than a shorter duality result;
the local search found the exact existing general-duality theorem and proved exterior
comparison. No new mathematical statements or edge-case hypotheses are introduced.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
