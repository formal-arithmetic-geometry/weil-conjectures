## What changed

Proved `AlgebraicGeometry.Scheme.Hom.exists_etale_to_affineSpace_of_exists_smooth_appLE`
in `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`, with its existing signature unchanged.
The given smooth affine chart is made into a smooth restricted scheme morphism via
`arrowResLEAppIso`; Mathlib selects a standard smooth subchart, and the proved source theorem
`Scheme.Hom.exists_etale_to_affineSpace_of_isStandardSmoothOfRelativeDimension` supplies its
étale factorization. The image-open and membership calculations return a chart of the original
morphism. This uses no global finite-presentation assumption on that morphism.

Added only the proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
Updated the item's node proof, proof dependencies, proof origin, and removed two obsolete tool
uses. No definitions, existing signatures, public imports, or consumer modules were changed.
The proof retains the unit's Jacobian normal-form route through the source theorem's
`RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` construction.

Validation: server `lcompile.py` compiled the module with no errors or warnings.
An additional compile with `#print axioms` reports exactly `propext`, `Classical.choice`,
and `Quot.sound` for the proved declaration. The diagnostic command was then removed.
Edge cases: the proof never assumes d is positive, never assumes X or Y globally affine, and
uses only the given point to select a nonempty source chart; no nontriviality or field
hypothesis is introduced.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Hom.exists_etale_to_affineSpace_of_exists_smooth_appLE`
(node `sbc-thm-etale-local-normal-form`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module, and the proved
declaration has no transitive sorry axiom.

## No longer needed

Removed proof imports:
- `Mathlib.AlgebraicGeometry.ResidueField`;
- `Mathlib.RingTheory.Smooth.StandardSmoothOfFree`;
- `WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive`;
- `WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree`.

Removed direct proof dependencies:
- `lem-weil-pbc-affine-open-spec-points`;
- `lem-weil-pbc-affine-open-section-vanishing-prime`;
- `def-exc-jacobian-presentation`;
- `lem-exc-etale-jacobian-presentation`.

The first two are subsumed by Mathlib's scheme-level standard-smooth chart selection.
The last two, and their source modules listed above, are replaced by Mathlib's already proved
standard-smooth polynomial étale factorization. The proof does not use the separate square
Jacobian presentation type or its étaleness equivalence. The local standard-smooth ring node
is retained as the algebraic input implemented inside Mathlib's chart selection, and the
ring/scheme comparison nodes remain the inputs of the reused affine-chart theorem.
These removals concern this proof; no claim is made that the modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The earlier search correctly found no exact theorem with the pointwise hypothesis, but missed
that the source library already proves the needed standard-smooth affine-chart factorization.
Its smooth-locus theorem cannot be applied directly to the original g, since that theorem
assumes global local finite presentation. Applying only the affine-chart theorem after
restricting to the supplied smooth chart avoids that extra assumption. No statement repair
was needed, and no new node or change record was created.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
