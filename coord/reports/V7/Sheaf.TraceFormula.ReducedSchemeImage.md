## What changed

Repaired the return of delivery `b172034b59c`: removed the unnecessary
`set_option warn.sorry false` command at the reported line 34. The landing
ledger's token scanner counted the option-name component as an unattributed
hole. The command is unnecessary for this fully proved module, so the file now
uses the project's warning settings. The mathematical proof from the returned
packet is retained.

Proved `AlgebraicGeometry.schemeTheoreticImage_reduced` in
`Sheaf.TraceFormula.ReducedSchemeImage`, with its signature unchanged.
The proved source-library `Scheme.Hom.ker_eq_vanishingIdeal` identifies the
canonical image with the vanishing-ideal subscheme. The existing reduced
induced closed subscheme theorem supplies reducedness and the underlying range.
Closedness of any other factor's range then gives the range inclusion needed
by the recorded reduced-source factorization theorem, including uniqueness.
Updated the item's proof steps and proof origin to match this argument.

Replaced the proof import `Sheaf.Paper.ReducedSourceFactors` by the direct
proof import `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic`.
The existing reduced induced subscheme and source closed-immersion imports
are both used. Public imports, definitions and declaration signatures are unchanged.
The repaired file passed the single-file remote compile in 3.5 seconds with
exit code 0 and no Lean diagnostics. It contains zero `sorry` tokens; delivery
preflight also checks declaration axioms. Comparison with the current shared
source confirms that only the node's `proof` and `proof_origin` fields change.
Added `coord/changes/reduced-scheme-image-warning-option.md`, as requested by
preflight for removal of the file-level warning option. Its consumer table
lists all 45 downstream modules; none uses the declaration textually and none
needs adaptation. The only declaration-use hit is the item itself.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.schemeTheoreticImage_reduced`
(node `lem-trf-reduced-scheme-image`).
No holes remain in the item; no holes were added, and no statements were split off.

## No longer needed

Removed the proof import `Sheaf.Paper.ReducedSourceFactors`: its wrapper is
unnecessary because the DAG's current Lean attachment for
`lem-weil-pbc-reduced-source-factors-through-closed-subscheme` is the proved
source-library `IsClosedImmersion.existsUnique_fac_of_range_subset_range`,
which is used directly. No DAG proof dependencies or unit steps are pruned:
the reduced induced subscheme theorem, reduced-source factorization theorem,
and closed immersion definition all remain used. No library declaration is
removed and no claim is made that the removed wrapper has no other consumers.

## Where the brief, the DAG or earlier work was wrong

The returned packet retained an unused warning-suppression option from the
original statement module. Its `sorry` token caused the landing failure even
though the theorem's proof had no holes. Removing the option repairs that
specific failure without altering any declaration or the proof route.

The old import pointed to the reduced-source wrapper although the dependency
node now records the source theorem. The existing source kernel/vanishing-ideal
identity also makes the planned separate construction and minimality-based
identification unnecessary. The node statement and mathematical route are
unchanged. The empty-source case is covered by the same kernel identity;
no quasi-compactness, nonemptiness or reducedness of the ambient scheme is added.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
