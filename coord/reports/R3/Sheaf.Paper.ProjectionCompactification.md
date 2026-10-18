## What changed

Proved both holes of `Sheaf.Paper.ProjectionCompactification`. A proved private helper
transports the existing exact slice-extension adjunction through the open localization
and coefficient equivalences. Uniqueness of left adjoints transfers finite-limit
preservation to the specified extension functor; its adjunction supplies additivity
and finite-colimit preservation. All existing signatures, definitions, public imports,
and docstrings are unchanged. Three proof-only imports provide the existing results.
The item node now records this proof and its actual dependencies.

## Proved and sorry left

Closed 2 of 2 original holes:
- `AlgebraicGeometry.Scheme.proEtaleOpenRestriction_isRightAdjoint`.
- `AlgebraicGeometry.Scheme.proEtaleRingOpenExtension_exact`.

Both belong to `def-weil-pbc-projection-compactification`. Added zero holes; no sorry
remains in the item or any delivered module. The private helper
`openRestriction_exactLeftAdjoint` is fully proved. No split-offs or new nodes.

## No longer needed

No original imports were removed and no original proof dependency was discarded
(the node previously had no proof steps or proof dependencies).
The trial proof-only import `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` was removed:
the general `CategoryTheory.localized_restriction_extension_exists` supplies its exact
slice adjunction without importing closed-complement localization, immersion limit
preservation, closed counits, localization sequences, or filtered-colimit arguments.
Thus `lem-weil-pbc-proetale-ringed-open-closed` is not needed by this proof. This is an
avoided dependency, not a claim that the module is globally unreachable.
All final proof-only imports are used: `import all ...ProEtaleOperations` exposes its
proved private scalar-equivalence and tensor adjunction helpers; the other two imports
supply open localization and exact slice extension respectively.

## Where the brief, the DAG or earlier work was wrong

The definition node originally had no proof plan or proof dependencies despite the
two supporting theorem holes. Existing fully proved localization and exact slice
adjunction results suffice; no new intermediate theory is needed. The current
blueprint's exact termwise extension route and the unit route are preserved.
The proof requires no quasi-compactness, nonempty open, nonzero ring, or coefficient
finiteness assumptions. Empty opens and zero coefficients are covered by the general
slice-extension theorem. The existing compactification definition is untouched.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
