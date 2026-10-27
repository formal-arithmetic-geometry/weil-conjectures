## What changed

Proved `AlgebraicGeometry.exists_smooth_geometricallyConnected_fibre_neighbourhood`
in `Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedOpenSpreading` by the declared
four-step route. Mathlib supplies flatness of a smooth morphism, the existing
`Smooth.geometricallyReduced` instance supplies geometric reducedness, and
`exists_geometricallyConnected_fibre_neighbourhood` supplies all the witnesses.
Smoothness of the open family follows from smooth base change, smoothness of an
open immersion, and smooth composition. The proof preserves the embedded fibre
equality verbatim. The repair also removes the unused `warn.sorry` setting that
triggered the returned hole-attribution failure. No signature, definition, public
import, or other module changed.

Validation: the repaired file compiled remotely with exit code 0 in 2.1 seconds.
The source ledger reports zero hole markers, no warnings, and no gate failures.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.exists_smooth_geometricallyConnected_fibre_neighbourhood`
(node `lem-trf-smooth-connected-open-spreading`). Proved 1 of 1 original sorries;
0 sorries remain in the item, and 0 are added or split off.
The proof uses the existing, separately assigned theorem
`AlgebraicGeometry.exists_geometricallyConnected_fibre_neighbourhood`, whose
existing sorry is unchanged.

## No longer needed

Removed private proof imports:

- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`: Mathlib's
  smooth-implies-flat instance already supplies the forward flatness clause of
  `sbc-lem-smooth-criterion`; the full fibrewise iff is unnecessary here.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: the only relevant clause of
  `lem-pc-proper-base-change` is smooth base change, already supplied by the
  public `Mathlib.AlgebraicGeometry.Morphisms.Smooth` import.

No mathematical dependency node is withdrawn: the four proof steps are unchanged,
with their generic smoothness clauses realized directly by Mathlib instances.
No module is deleted. The geometrically reduced and general spreading imports
remain necessary.

## Where the brief, the DAG or earlier work was wrong

Returned delivery `9b9b9ae2c14` failed the landing ledger: its hole-token scanner
matched the `sorry` component of the unused `set_option warn.sorry false` setting
at line 26, reporting an unattributed hole. Removed that setting from the item.
The proof is unchanged and has no hole; the repaired source has zero ledger
markers or warnings and passes `sorry_ledger.missing_gate` against current main.
No tools were changed. The current main source still has the original theorem
hole; the restored sandbox retains the returned proof and the same two private
import removals, with this additional removal repairing the reported failure.

No mathematical error found. The existing imports included two unnecessary proof
modules, as explained above. LeanFinder returned smooth-chart and etale-locus
lemmas, while Loogle and Mathlib grep found no combined smooth connected-spreading
theorem. Local searches found only this theorem and the declared general
spreading theorem. The existing declared reduction is sufficient without new nodes.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
