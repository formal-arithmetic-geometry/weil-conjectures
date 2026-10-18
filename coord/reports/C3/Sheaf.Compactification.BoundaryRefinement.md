## What changed

Proved `AlgebraicGeometry.Compactification.boundaryRefinementProperty_isMultiplicative`
in `Sheaf.Compactification.BoundaryRefinement`. The identity case uses
`Scheme.Hom.id_preimage`. For composition, the full-subcategory and refinement
projections reduce to the composite of the ambient scheme morphisms;
`Scheme.Hom.comp_preimage` then lets the two boundary equalities rewrite the goal.
This follows Steps 2 and 3 of `det-nagata-definition-refinement`; the existing
wide-subcategory and full-subcategory constructions supply Step 4.

All existing signatures, definitions, visibility, docstrings and imports are unchanged.
The DAG's existing proof plan remains accurate, so no node changes are needed.
LeanFinder, Loogle and Mathlib/source-library searches identified the elementary
inverse-image API; no additional theory is required.

Validation: the complete module compiled through `lcompile.py` in 2.6 seconds,
with no errors or warnings. The proof works for empty and full distinguished
opens as well, using the same unconditional inverse-image identities.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Compactification.boundaryRefinementProperty_isMultiplicative`
(node `det-nagata-definition-refinement`).

Zero holes remain in the item module. Zero holes added; zero split off.

## No longer needed

None. No imports were added or removed. Each existing public import supports
the file's statements or definitions: quasi-compact objects and the dense full
subcategory, the wide subcategory, scheme-theoretic dominance, and upstream
compactifications/refinements. No dependency node or module is bypassed or pruned;
the proof implements the existing elementary identity/composition plan.

## Where the brief, the DAG or earlier work was wrong

None. The assigned hole is an elementary instance construction; the existing
refinement projections and Mathlib inverse-image identities suffice directly.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
