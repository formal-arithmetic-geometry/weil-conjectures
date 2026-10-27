## What changed

Replaced both proofs in `Sheaf.Paper.FiniteWindowBounded`, keeping every existing
statement and public import unchanged. The new private helpers transport Hom
subsingletonness across an isomorphism, convert finite cohomology support to
boundedness, apply the already proved source-library degreewise devissage, and
identify positive Ext with maps into a sheaf placed in its cohomological degree.
The extension argument uses `Triangle.coyoneda_exact₂` explicitly.

Added the proof import `Sheaf.Paper.ConstructibleIndExtBound`. Its one theorem is
the sheaf-only vanishing input shared by the two coefficient choices, not a
renaming of the bounded-complex conclusion. Its coefficient condition is equality
of bundled monoid objects, including the specified multiplication; arbitrary
multiplications on the same underlying abelian sheaf are not admitted.

The source-library theorem
`DerivedCategory.prop_of_bounded_of_degreewise` supplies the complete truncation
induction. No module in `WeilConjectures` was edited. The existing node's proof,
proof dependencies and proof origin now follow this implementation.

Validation: `lcompile.py --all` compiled both modules, with the new sheaf input at
31.7 seconds and the bounded-complex module at 52.2 seconds, both below 60 seconds.
The final delivery also performs the required compile and axiom probes. Edge
cases were checked in the argument: empty cohomology support, zero sheaves,
d_C=0, q=-d_C-1, and q above that cutoff. At the boundary the Ext degree is
exactly d_C+1, so the strict inequality has the correct sign. For algebraic
closure coefficients the otherwise unused finite intermediate field is the
explicit bottom field, with its actual finite-dimensional instance.

## Proved and sorry left

Closed the two original holes, by complete Lean proofs from the named sheaf input:

- `AlgebraicGeometry.ProEtale.finiteWindow_bounded`
- `AlgebraicGeometry.ProEtale.finiteWindow_bounded_padicAlgCl`

There are zero `sorry`s left in the item module. Added exactly one hole:

- `AlgebraicGeometry.ProEtale.constructibleInd_extBound`, node
  `lem-finite-window-ind-ext-bound`, in
  `Sheaf.Paper.ConstructibleIndExtBound`.

This is a reduction of two bounded-complex obligations to one shared sheaf Ext
obligation, not an unconditional proof of the geometric sheaf input. The new
statement has no derived complex, finite-support hypothesis, cohomological
cutoff hypothesis, or truncation induction. It only extends the supplied bound
from constructible sheaves to one ind-constructible sheaf. All three private
helpers are fully proved. Holes closed: 2; holes added: 1.

## No longer needed

Removed these private proof imports:

- `WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Mathlib.CategoryTheory.Triangulated.Triangulated`
- `Sheaf.Paper.AmbientIndDerivedSums`
- `Sheaf.Paper.IndHeartIIVanishing`

The first four are replaced by the proved source-library degreewise devissage
and its existing imports. `det-ambient-ind-derived-sums` is unnecessary here:
the degreewise Hom property avoids constructing an auxiliary ind-constructible
complex or invoking closure under sums/truncations. The original lower-truncation
step node `lem-pc-derived-lower-truncation-step-triangle` and the composite
homotopy-colimit definition node `def-kun-truncations` are no longer direct
proof dependencies of this item; ordinary standard-t-structure truncation is
used inside the proved source-library devissage instead.

`det-ind-heart-ii-vanishing` is not applied because it has unavailable Noetherian
hypotheses. Its general-scheme, sheaf-only source input is isolated in the new
node. This does not retire that existing theorem or claim its theory is globally
unused. Concentration in one degree, standard truncation and triangle exactness
remain parts of the same bounded devissage argument. All public imports were
retained to preserve the existing consumer interface. No files were withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original node applies `indHeartII_vanishing` on an arbitrary scheme, while
that declaration requires `[IsLocallyNoetherian X] [CompactSpace X]`. Its source
Ext-continuity declaration has the same extra hypotheses. The stage-2 review
already recorded this applicability gap. Neither the original statements nor
the unit's current blueprint statement supply them. I did not silently add
these hypotheses or apply the Noetherian theorem as if it were unrestricted.

The blueprint's `sk-cor-ind-heart-ii` and its proof assert the sheaf input for
general X. That exact vanishing input is the remaining named obligation. The
new docstring and node explicitly record that the current Noetherian continuity
result does not close it; a proof in the required generality (or a separate
mathematical correction by the maintainers) remains necessary. No counterexample
to the vanishing statement is asserted by this delivery.

The initial proof plan also overlooked the already proved degreewise devissage
in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`. Using
it avoids reproving the bounded truncation induction without bypassing any
unit-level statement or step. The unit's `realized` record is unchanged.

The current rework row and source were checked before copying. Although the
row records an earlier quarantine caused by a primitive-quotient dependency,
the item source is present in `lean/` and was used intact as the starting point.
No quarantine path was removed or placed in `deleted.txt`.

## New nodes

`lem-finite-window-ind-ext-bound` states the uniform Ext bound against a single
ind-constructible sheaf, for the two rational condensed coefficient rings. It
comes from the vanishing clause of `sk-cor-ind-heart-ii` and the one-cohomology
case of `det-finite-window-bounded`. The known related DAG node
`det-ind-heart-ii-vanishing` also includes full continuity and requires a
Noetherian scheme, so its current statement cannot replace this input.
Blueprint and DAG searches were made for ind-heart/Ext results. LeanFinder,
Loogle and Mathlib grep found no exact theorem; LeanSearch was unavailable and
is recorded as unavailable. No change record is needed: only the item's proofs,
private imports, own node, and this new module/node were changed.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
