## What changed

Replaced the whole proof hole in `Sheaf.Paper.DiagonalOrdinaryOrientationGluing`
by ordinary-site degree-zero gluing. The cover is indexed by all finite-type
affine target opens, so the result prescribes every requested restriction.
A private generic helper glues both homs and inverses and proves the inverse
identities using the existing equality test. The proof then cancels the shift
and uses naturality of the comparison isomorphism to recover the exact equation.
An abstract private natural-isomorphism lemma keeps the large coefficient-unit
definitions folded during kernel checking. Profiling identified repeated unit
unfolding as the cause of the initial over-limit compile.

Added `Sheaf.Paper.DiagonalOrdinaryChartLift`: real exact-restriction, coefficient-unit,
comparison and realization maps; a finite-Tate concentration proof by flat tensor
induction; and a proved local ordinary lift using the existing bounded-below
comparison Hom bijection. The induction follows the existing private
`base_normal_form` proof in `BundleSectionOrientationMapExt`, using its public
ingredients, without importing its unrelated bundle-section orientation theorem.

Added `Sheaf.Paper.DiagonalOrdinaryOverlap` for the exact shift and overlap
comparisons and the one remaining coherence/equality step. Updated the item DAG
proof and dependencies to follow this argument. No existing public signature,
definition, attribute or public import changes. No source-library changes.

Validation: the two new modules and the original item compile through lcompile.
The final item compile is clean, takes 16 seconds, and has no development options.
The theorem signature and public imports match the original byte for byte.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.diagonalOrdinaryOrientationGluing` (1 of 1).
Added one hole:
`WeilConjectures.PurityFiniteSetting.OrdinaryDiagonal.overlap`, node
`lem-pur-diagonal-ordinary-overlap`. This is a decomposition (one hole closed,
one strictly smaller local compatibility obligation added), not a net hole proof.
The item module and the new local-lift module contain zero holes.

Proved the new public `OrdinaryDiagonal.chart_lift` and
`OrdinaryDiagonal.twist_concentrated`, the general `OrdinaryDiagonal.concentrated_iso`,
and all private helpers. The overlap theorem
asserts only equality of two already given local maps on their overlap: no global
orientation, global existence, or global inverse equations. Its docstring and node
provide the affine-refinement, comparison coherence and degree-zero equality-test
argument. Existing imported theorem holes remain with their existing owners.

Edge cases: the finite cover may be empty and the gluing theorem includes empty
covers. All affine opens are indexed, so empty opens are also allowed. The Tate
induction has an explicit zero case and allows d=0. Neither the local lift nor
gluing uses absolute separatedness of X or Y, or ramification-index divisibility.

## No longer needed

Removed the direct proof import `Sheaf.Paper.DegreeZeroDerivedMapGluing`; it is
now publicly exposed by the new overlap interface because its canonical
open-composition map occurs in that interface. Its theorem is still used explicitly
in the main proof; this is not pruning of its module or node.

No module or node is withdrawn. The old direct proof dependencies
`thm-pur-dnc-invariance`, `def-weil-pbc-proetale-modules`,
`def-coefficient-twists-detailed`, and
`lem-pur-diagonal-orientation-refinement` are now accounted for below the local
lift and overlap nodes (or in the unchanged statement dependencies), rather than
as applications in the parent proof. In particular no direct analysis of each DNC
factor is needed to lift a local isomorphism: faithful exact comparison reflects
its Tate concentration, and the proved bounded-below Hom bijection lifts it.
All those underlying mathematical nodes remain needed; no closure pruning claimed.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The original gluing plan mixes pro-etale gluing followed
by a global ordinary lift with ordinary-site gluing. The latter makes the inverse
identities formal and avoids needing a separate global bounded-below comparison.
The remaining difficult glue is the equality of canonical comparison compositors
and Tate pullbacks on nonaffine overlaps; Agrees is only stated for nested affine
opens, so it does not directly supply this equality in ordinary exact coordinates.

Search: LeanFinder returned topological sheaf section gluing, not derived diagonal
orientations. LeanSearch returned sheaf-map extensionality, not this comparison
calculation. Loogle supplied the shift preimage API and general commuting-shift
structures. Local searches found the existing degree-zero gluing interface,
comparison Hom bijection and finite-Tate induction; these were reused. The new
nodes record the searches and exact declarations. The unit's diagonal/DNC/vector
route is preserved; no route is replaced by an unrelated smooth-purity assertion.

## New nodes

`lem-pur-diagonal-ordinary-chart-lift` records the proved ordinary lift of one
specified affine-target orientation. The extra wrappers express canonical maps,
not new mathematical data, and the concentration statement is proved in this module.

`lem-pur-diagonal-ordinary-overlap` records only compatibility of existing local
ordinary lifts after the common even shift. It is the sole new sorry and is
strictly local. The item uses it to perform actual gluing and inverse checks.

No change record is required: existing interfaces are unchanged.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
