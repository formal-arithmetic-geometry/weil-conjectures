## What changed

Proved `SheafOfModules.PrincipalReduction.Setup.exactSectionsReductionUnit` in
`Sheaf.Paper.ExactSectionsReductionUnit`, preserving its statement and all existing
constructions. Added proved private helpers for normalized derived adjunctions,
the ordinary sections comparison, regularity on flat terms, and the representative
formulas. No other Lean module is changed.

Preflight requires an interface change record for module-local elaboration options
and scoped `omit` commands: `coord/changes/exact-sections-reduction-unit-elaboration.md`.
These commands leave all existing declaration signatures and constructions unchanged;
no consumer adaptations are needed. The downstream-use check lists no importing modules.

The comparison is the adjoint mate of the canonical restriction square. The existing
normalized derived-mate theorem identifies it with `Setup.alpha` on flat-term K-flat
models. Principal-quotient quasi-isomorphisms then prove that it is invertible. This
works over a general commutative ring with regular t and does not assume that sections
of a K-flat sheaf complex are K-flat. The dependency node records this route.

Proof imports add the resolving adjunction and derived-mate comparison, localization
factorization lemmas, ordinary K-flat resolutions, preservation under scalar extension,
the principal-quotient lemma, and Mathlib flat-module regularity. An `import all` of the
existing resolution-independence module permits reuse of its proved internal comparison
and counit lemmas without changing its public interface.

## Proved and sorry left

Closed the original one hole:
`SheafOfModules.PrincipalReduction.Setup.exactSectionsReductionUnit`
(node `lem-coef-exact-sections-reduction-unit`).

Item module: 1 original sorry, 1 closed, 0 remaining. Added holes: 0. Split-off statements: 0.
Validation: the complete module compiles successfully through `lcompile.py` in 18.3 s,
with no diagnostics. The main theorem signature is byte-identical to the original,
and all lines satisfy the 100-character limit. Both new generic proof imports pass
the import-direction cycle check. Every new private helper is proved. Existing imported declarations retain their own proofs
and dependency status.

## No longer needed

The proof uses the universe-independent resolving-adjunction theorem directly instead
of specializing the sheaf adjunction to a point site and comparing two separately
constructed ordinary derived extensions. Consequently the principal statements of
`lem-pur-sheaf-ring-derived-coefficient-adjunction` and
`lem-pur-derived-change-of-rings` are unnecessary as direct proof dependencies.
Their public imports are retained: they supply the cochain adjunction declaration,
additivity, and Grothendieck module-category instances needed by the existing interface.
The former node also remains in the unchanged statement dependency record.

`lem-weil-pbc-flat-tensor-exact` is replaced by Mathlib's
`Module.Flat.isSMulRegular_of_isRegular`, which handles regular elements over arbitrary
commutative rings. No source-library declaration is removed.

The ordinary derived tensor functor's definition is already supplied by
`DerivedReductionResolutionIndependence`; this proof needs no separate application of
`lem-pc-derived-tensor-second-factor-functor`. The source dependency itself remains
needed transitively by the existing definitions. Redundant imports of
`MixedTensorPointwiseLeftDerived`, `DerivedTensorSecondFactorFunctor`,
`DerivedChangeOfRingsCochainModel`, and `Mathlib.RingTheory.Flat.Basic` were removed;
the required declarations are available through retained imports.

The common-refinement resolution-independence theorem is not needed to establish
naturality: the mate is a natural transformation from the outset. Its module remains
necessary for `Setup`, `theta`, `alpha`, the canonical counit, and `resolvedComparison`.
No modules or declarations are withdrawn, and no global pruning is claimed for these
retained transitive dependencies. Removed only the obsolete `tool_uses` entries
`lem-weil-pbc-flat-tensor-exact`, `lem-pc-derived-tensor-second-factor-functor`, and
`lem-pur-sheaf-ring-derived-coefficient-adjunction`; remaining approvals retain their
original order. No approvals were added or replaced.

## Where the brief, the DAG or earlier work was wrong

The planned point-site specialization is unnecessary. The generic resolving-adjunction
theorem supplies the same normalization directly for ordinary modules and for sheaves,
while allowing the derived-category universes to stay independent. The existing sheaf
adjunction interface uses one derived-category universe, so applying it directly would
unnecessarily identify universes in this item's unchanged statement.

Existing flat-comparison helpers assume that the coefficient ring is a domain. That
hypothesis is unnecessary here: Mathlib regularity on flat modules supplies exactly
the required replacement. This delivery changes no existing statement or definition.
The unit record has no realized proof steps to bypass; the comparison, principal-quotient
argument, normalized units, and both resolution formulas are all retained.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
