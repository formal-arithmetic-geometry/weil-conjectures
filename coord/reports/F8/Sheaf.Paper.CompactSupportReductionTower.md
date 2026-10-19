## What changed

Proved `WeilConjectures.compactSupportProjection_comp` in
`Sheaf.Paper.CompactSupportReductionTower`, with its statement unchanged.
The retained proof establishes the identity quotient and composition of an
adjacent quotient with an arbitrary quotient using `Ideal.Quotient.factor_eq`
and `Ideal.Quotient.factor_comp_apply`. Induction on `n ≤ m` then uses
naturality of the completed coefficient limit cone after forgetting
commutativity. Its two helper lemmas are private and fully proved.

Checked the retained sandbox against the current source and removed an empty
line inside the proof and two unnecessary local transparency options. The
module compiles without warnings through `lcompile.py`; the resumed attempt
rechecked it against the current build in 6.3 seconds.
No definitions, public signatures or imports were changed.

## Proved and sorry left

Closed 1 of the original 2 holes:
`WeilConjectures.compactSupportProjection_comp`.

The existing hole `WeilConjectures.exists_compactSupportReductionTower` remains
unchanged (node `lem-weil-compact-support-reduction-tower-functor`).
There are no other direct holes in the delivered module. No holes were added
and no theorems were split off. A separate `#print axioms` check reports
`propext`, `Classical.choice`, `Quot.sound` and inherited `sorryAx`; the
existing imported theory is not yet free of holes. This is a partial proof
delivery, not a proof of the coherent tower-existence theorem.

## No longer needed

None. The proof closes the projection-compatibility part of the existing
route and retains the unresolved tower construction. Its planned dependency
imports are retained; no node or module is claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

The retained report said `Sheaf.Paper.SemilinearDerivedSections` and
`Sheaf.Paper.CoefficientSystemDerivedComparison` were absent. Both modules
are now present in the current shared sources. Their declarations and the
semilinear system, scalar-extension and geometric-operation interfaces were
read in this attempt. The previous absence claim no longer applies and is
not an obstacle to using their statements, even though they contain `sorry`.

The remaining theorem needs the actual composite through the ringed sequence
site, identification of its evaluations and all quotient transitions with the
specified finite-level functors, and normalized scalar structures and
linearity of that composite. Those constructions are not supplied by the
projection calculation and remain in the original named theorem.

The earlier searches recorded quotient identity/composition and sequence
functor lemmas. A fresh LeanFinder search for the coherent compact-support
lift returned condensed module constructions, with no matching theorem.
Local searches in both library roots found consumers of the tower theorem,
not an independently proved replacement. The proof includes the equal-level
and adjacent cases and proves arbitrary gaps by induction. Index zero means
the positive exponent one throughout, including in the base case.

The previous attempt stopped before preflight because worktree creation
failed (first exit 137, then the 600-second checkout timeout). This resumed
attempt retained the proof and began with the required dry run. The launcher
scripts have not been changed or bypassed.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
