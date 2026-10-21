## What changed

Restored `lean/Sheaf/Paper/SitePerfectComplex.lean` from the quarantine archive
identified in `coord/rework.tsv`. Preserved all ten declarations, their universes,
public imports, docstrings, and the node attachment `def-weil-site-perfect-complex`.
Repaired `WeilConjectures.IsRationalFiniteProjectiveTerm` by explicitly specifying
`integralTowerModules l E Y` in its four `DerivedCategory.singleFunctor` applications.
This keeps the recorded category visible to scalar-localization instance synthesis.
The finite, integral, legacy rational, intrinsic rational, and common-stage
site-perfectness definitions retain their meanings and source routes.

Change record: `coord/changes/E3-site-perfect-category-inference.md`.
The archived original was compiled to reproduce its line-122 Quiver instance failure.
The repaired module compiles; no consumer adaptation is needed for a definitional
category annotation. The change record lists all twelve archived direct consumers.

## Proved and sorry left

This assigned repair has zero holes originally and zero holes after repair.
Holes closed: none (0). Holes added: none (0). Sorries remaining: none (0).
No theorem proof or source-library declaration is changed. This is a definition
elaboration repair, not a decomposition or a claim to have proved a new theorem.

## No longer needed

None. No import, node, declaration, dependency, or module is pruned or withdrawn.
All six original public imports and the complete archived module are retained.
The node has no proof steps or proof dependencies to change; its Lean attachment
already records the restored module and all ten declarations. The unit route stays
unchanged. Quarantined consumers remain required and are not deleted.

## Where the brief, the DAG or earlier work was wrong

The assigned rework is an elaboration failure in a definition with zero `sorry`s.
The upstream sync exposed that inferring the degree-zero functor's category from
the coefficient unit did not find the scalar-localization Quiver instance. Naming
the recorded module category fixes the failure without changing the mathematics.
No incorrect DAG statement or blueprint route was found.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
