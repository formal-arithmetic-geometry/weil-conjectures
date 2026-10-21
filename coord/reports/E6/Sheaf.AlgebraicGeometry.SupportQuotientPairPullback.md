## What changed

Proved `AlgebraicGeometry.Scheme.supportQuotient_pair_pullback` from the actual cokernel
presentations and the existing normalized support-quotient comparisons. The etale relation
vanishes on every geometric stalk, hence vanishes as an ordinary sheaf morphism. Cokernel
descent constructs the etale map; its normalized stalks give Cartesian invertibility.
The proetale map is the explicit transport through the normalized quotient comparisons.
Constant-section adjunction calculations prove coefficient identity, composition and
comparison equations. Cancelling pulled-back quotient epimorphisms proves uniqueness,
identity and composition. Uniqueness of the normalized quotient comparison gives the
comparison clause for every comparison admitted by the statement.

All existing public declarations and public imports are unchanged. New helper definitions
and lemmas are private and proved. No changes to definitions or statements in other modules,
no forced adaptations, and no new modules or nodes. The proof elaboration context is
recorded in `coord/changes/E6-support-pair-pullback-proof-context.md`.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.supportQuotient_pair_pullback`
(node `lem-pur-support-quotient-pair-pullback`). Zero holes added or split off; zero holes
remain in the delivered module. Every private helper has a complete proof. The full module compiles cleanly through
`lcompile.py` in 34.3 seconds, with no errors or warnings.

## No longer needed

The following planned dependencies are not used by this proof:

- `prop-weil-pbc-inverse-image-modules-exact` and
  `lem-weil-pbc-etale-inverse-image-algebraic-structures`: the fixed-coefficient pullback
  already is a left adjoint, preserving the cokernel and quotient epimorphism. The
  published module-valued inverse-image stalk isomorphism applies directly.
- `prop-weil-pbc-geometric-stalks-exact`: the existing joint faithfulness of geometric
  stalks proves the relation zero directly, without introducing its image object.
- `lem-sf-comparison-pullback-exact`: the proetale inverse image is itself a left adjoint,
  so preserves the quotient epimorphism directly.
- `lem-pur-proetale-constant-ring-composition`: the proof derives the constant-section
  composition equation for arbitrary coefficient categories and specializes to modules,
  avoiding an extra ring-to-module transport.

Removed proof-only imports: `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`,
`Sheaf.Paper.ComparisonPullbackExact`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`, and
`Mathlib.Algebra.Homology.ShortComplex.ShortExact`. The redundant direct import
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint` is also removed: it is
already publicly provided by the inverse-image stalk and extension-by-zero imports.
The same imports provide `Mathlib.CategoryTheory.Sites.Point.Skyscraper`, whose
redundant direct import is removed too. Obsolete top-level `tool_uses`
approvals for the omitted nodes are removed; remaining approvals retain their order. No module is withdrawn; these nodes can remain
needed by other consumers. The DAG proof and proof-dependency list record this route.

## Where the brief, the DAG or earlier work was wrong

The original route is mathematically sound, but overstates the machinery needed for
quotient epimorphisms and equality of sheaf morphisms: adjunctions and joint faithfulness
suffice. Normalizing the specified adjunction mates on constant sections works directly
for the module coefficient category. The source factorization, Cartesian hypothesis,
quasi-compact complements, and every normalization in the original theorem are retained.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
