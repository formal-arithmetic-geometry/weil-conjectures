## What changed

Replaced the `sorry` in
`AlgebraicGeometry.Monoscheme.finite_chart_components_algebra` by a complete Lean proof.
All four existing public theorem signatures and their public imports are unchanged.
The previously proved `finite_chart_components` is preserved verbatim.

The proof isolates only the intrinsic affine-section/generic-stalk comparison in the new
module `Sheaf.AlgebraicGeometry.MonoschemeGenericChartCompletion`, theorem
`AlgebraicGeometry.Monoscheme.generic_chart_completion`. This statement does not assume
global torsion-freeness or a coefficient field and does not assert a lattice basis, an
algebra domain, or algebra generation. Its docstring explains the smallest-neighbourhood,
sheafification, stalk and canonical completion calculations in full.

From that geometric bridge, the parent proof derives positive-power injectivity of the
component lattice directly from `hM`, transfers finite generation through one chart
completion, and uses `Module.basisOfFiniteTypeTorsionFree'` and the basis coordinate
isomorphism to obtain the finite free lattice. For every chart it derives cancellation
and torsion-freeness, invokes Mathlib's affine-monoid unique-products and monoid-algebra
domain instances, and proves monomial generation by explicit submonoid-closure and
monoid-algebra inductions. Thus the new lemma is a strictly smaller geometric step;
the algebra consequences are genuinely proved here.

Added only private proof imports for the new bridge,
`Mathlib.Algebra.AffineMonoid.UniqueSums`,
`Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors`,
`Mathlib.GroupTheory.MonoidLocalization.Finite`, and
`Mathlib.LinearAlgebra.FreeModule.PID`. Updated Steps 3--4, proof dependencies and proof
origin of the existing DAG node; added the new bridge node. No shared definition,
instance, attribute or existing public interface changes.

Validation: `lcompile.py --all` compiled the new bridge and the parent module, with no
errors or warnings (1.9 s and 7.9 s respectively in the successful proof iteration).
The delivery tool checks the final packet again. Source read: ILO VIII 3.1.2--3.1.4,
3.1.9--3.1.10 and 3.2.4, printed pp.98--103. Checked the bridge on the empty monoscheme
(vacuous), the trivial monoid, a group chart, the chart of natural numbers, and charts
with nontrivial units. No sharp quotient is used, so the generic stalk retains units.

## Proved and sorry left

Starting item: three textual holes. Closed:

- `AlgebraicGeometry.Monoscheme.finite_chart_components_algebra`, by the complete proof
  described above, conditional on the new geometric bridge.

Added one hole:

- `AlgebraicGeometry.Monoscheme.generic_chart_completion`
  (`lem-trf-monoscheme-generic-chart-completion`), in its own new module.

The two existing holes remain unchanged:

- `AlgebraicGeometry.Monoscheme.finite_chart_components_localization`
  (`lem-trf-monoscheme-finite-chart-components`).
- `AlgebraicGeometry.Monoscheme.finite_chart_components_realization`
  (`lem-trf-monoscheme-finite-chart-components`).

This is a decomposition: one upper hole closed and one strictly smaller hole added,
net zero holes, with actual finite-free, domain and generator arguments now formalized.
The already proved topology theorem is not counted as a newly closed hole.
There are three textual holes across the final two-module packet, two in the item itself.

## No longer needed

No imports removed and no modules withdrawn. No existing planned dependency can be
pruned globally from this partial delivery: the original localization and realization
proofs remain open. The new bridge absorbs the generic-chart comparison formerly hidden
inside the algebra proof; the original prime-neighbourhood dependency remains needed
there and in the proved topology argument. No normalization theorem or additional toric
realization parent is imported for the domain argument: Mathlib's existing unique-product
instances suffice.

## Where the brief, the DAG or earlier work was wrong

The initial topology theorem is already proved in the current source, leaving three
holes rather than four. Its proof and statement were preserved. The mathematical plan
is retained. The existing dependencies did not expose the unsharpened intrinsic
section/generic-stalk comparison with its canonical germ formula. The fan localization
statement uses `Associates` and cannot substitute for the unsharpened monoid stalk;
the spectrum universal property states morphism and fraction formulas rather than the
needed completion isomorphism. The new bridge records exactly this missing geometric
step. Current unit and chapter routes are unchanged; the historical toric support branch
is retained as assigned.

## New nodes

`lem-trf-monoscheme-generic-chart-completion`, in
`dag/nodes/sec-trace-formula/lem-trf-monoscheme-generic-chart-completion.json`, records
`AlgebraicGeometry.Monoscheme.generic_chart_completion` in
`lean/Sheaf/AlgebraicGeometry/MonoschemeGenericChartCompletion.lean`. It states fineness of
intrinsic affine sections, the canonical chart-completion comparison and that the generic
stalk is already a group. It is strictly smaller than the parent algebra theorem, and
has no domain, free-basis or algebra-generation assertion. Its proof steps and docstring
retain the source argument and its canonical maps. LeanSearch, LeanFinder and Mathlib
source grep found only ring-scheme stalk comparisons, not this unsharpened monoid
comparison; the complete blueprint search for monoscheme returned no duplicate.
No change record is needed: all existing public signatures, definitions and imports
are unchanged, and no other existing module is modified.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
