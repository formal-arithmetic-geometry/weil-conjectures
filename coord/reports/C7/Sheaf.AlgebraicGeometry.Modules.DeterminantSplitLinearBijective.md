## What changed

Repaired the returned retirement against C8 landing 4453be244d6. Retire
Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective as assigned by
coord/retire-items.tsv:529, preserving its mathematical node with the proved
upstream realization. No source-library file changes.

The consumer DeterminantSplitComparison starts from its current repository source.
It retains C8's canonical linear-family construction and all of its transport,
wedge and naturality proofs. Replace the private bijectivity import by the
upstream module. Apply canonical bijectivity to d', then compose with the evaluated
comparison isomorphisms to obtain bijectivity of the transported family d0.
All public signatures, public imports, attributes and docstrings stay unchanged.
Updated the two nodes without overwriting C8's reviewed metadata.

Change record: coord/changes/retire-determinant-split-linear-bijective.md.

## Proved and sorry left

Initial item holes: zero. Holes closed: zero. Holes added: zero. Sorries left: none.
No split-off theorem. The upstream realization of
AlgebraicGeometry.Scheme.Modules.determinant_split_linear_maps_locally_bijective
is already proved. The adapted
AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_exists is complete.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective.
Its private import in DeterminantSplitComparison is replaced by the upstream one.
Its private topIndexEquiv, topBasis, topBasis_apply and split_wedge_bijective are
redundant with the adopted source proof. No upstream declaration is removed.

The retired file's imports disappear with it:
Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf;
WeilConjectures.AlgebraicGeometry.Modules.TensorSection;
WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree;
Mathlib.Algebra.Homology.ShortComplex.ShortExact;
Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts;
WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitChartComparison;
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPresheafComparison;
Mathlib.LinearAlgebra.ExteriorPower.Basis; Mathlib.LinearAlgebra.Prod;
Mathlib.LinearAlgebra.TensorProduct.Basis;
WeilConjectures.LinearAlgebra.ExteriorTopDirectSum;
WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison;
WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero.
These are not asserted globally unused.

Removed lem-sc-exterior-sheaf-presheaf-upstream-comparison from the item's proof
route: upstream uses canonical exterior powers directly. The consumer retains
lem-sc-exterior-sheaf-power-comparison. The common-chart argument, triangular
basis argument, parent dependency and unit route remain.

## Where the brief, the DAG or earlier work was wrong

The current assignment is a zero-hole retirement. The returned packet was based
on the earlier legacy linear-family construction, which C8 has since replaced.
The repaired packet preserves that landing and avoids transporting the legacy
family back to canonical powers: canonical bijectivity is applied before transport.
No statement was disputed or weakened.

## Forced adaptations

DeterminantSplitComparison is unclaimed. Merely replacing its private import
makes the call with d0 fail: upstream expects exteriorPower while d0 uses
exteriorSheaf. The repaired call instead uses d' and hd', followed by composition
with comparison linear equivalences. The proof-local transparency option handles
the definitional comparison between that composition and d0. Only these forced
lines are changed relative to the current repository source.

Validation: consumer compiles cleanly; its direct importer
DeterminantWedgeMorphismSplit compiles against the adapted consumer. The delivery
preflight checks declaration axioms. Import-direction check permits the upstream
import. The retained search log records LeanFinder, Loogle and Mathlib grep.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
