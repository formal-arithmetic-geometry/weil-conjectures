## What changed

Proved `DerivedCategory.exists_derivedCanonicalFiltration` in
`Sheaf.Algebra.Homology.DerivedCanonicalFiltration`, preserving its full statement.
The proof constructs the canonical filtration functor on bounded complexes, passes
through their homotopy quotient, and uses bounded roofs/common refinements to prove
that this quotient localizes to the bounded derived category. Localization then
supplies the functor and natural isomorphisms. The proof checks the specified
representative, chain-map, roof, forgetful, and graded normalization equations.

All new helpers are private and fully proved. The bounded-complex category,
quotient functors, and filtration on maps are actual constructions; the lift of a
chain map is unique because its underlying map is prescribed. No arbitrary bounded
representative is chosen. The localization comparisons come from the existing
filtered tensor localization theorem, using its specified lifting isomorphisms.
Updated the existing node's proof, dependencies, and proof origin to record this
route. Eliminated existential witnesses from the large filtered tensor statement
step by step and factored its forgetful/graded data into the fully proved private
`localization_comparison_data` theorem. This keeps the comparison construction
independent of the large unused tensor data. The refactored complete module
compiled cleanly in 46.2 seconds with kernel checking and linting. A subsequent
profiled compile with the full maintainer axiom probe passed in 19.7 seconds,
reporting no unexpected axioms or holes.
No other module or existing signature is changed. The preflight-requested scope
record is `coord/changes/DerivedCanonicalFiltration-proof-scope.md`; it lists
all import consumers and explains why no adaptation is necessary.

Validation: the complete proof compiled through `lcompile.py`; the final packet
is also checked by the delivery dry run. The statement was compared verbatim with
the repository statement. There are no lines over 100 characters and no added
public declarations. The theorem-local unused-variable linter setting preserves
the existing statement's named binders, including names used only implicitly.

## Proved and sorry left

Closed 1 of 1 original holes:
`DerivedCategory.exists_derivedCanonicalFiltration`
(node `lem-kun-derived-canonical-filtration`).

Actual holes remaining in the item: 0. Holes added: 0. Split-off statements: 0.
There are no holes in any definition or private helper. This proof uses the
already declared `CochainComplex.exists_canonicalTruncationFiltration`,
`DerivedCategory.boundedDerivedRoofs`, and
`CochainComplex.filteredTensor_localization`; their upstream proof obligations
are unchanged.

## No longer needed

Removed the proof import `Sheaf.Algebra.Homology.FilteredQuasiIsoFractions` and
the dependency `lem-kun-filtered-quasi-isomorphism-fractions` from this node's
proof steps and proof dependencies. A calculus of fractions in the filtered target
is unnecessary: the functor is descended using localization of the bounded
homotopy source, proved directly from the bounded-roof and common-refinement
clauses. This prunes that dependency from this item's proof; other consumers may
still need it.

Removed redundant direct imports
`Sheaf.Algebra.Homology.FilteredComplexSubquotients` and
`WeilConjectures.CategoryTheory.Abelian.Filtration`; their definitions remain
available through the retained statement imports and their nodes remain used.
Added the proof-only Mathlib import
`Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions` for the
source localization criterion. All other declared dependencies remain used.
No unit statement or realized unit step is bypassed (the unit's realized lists
are empty). No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan required filtered quasi-isomorphism fractions to establish
independence of roofs. This is stronger than needed. Bounded ordinary roofs and
common refinements already establish the source localization universal property,
and any functor inverting its denominators descends to it. The remaining original
steps are retained, with full normalization and naturality proofs. No statement
or definition repair was required.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
