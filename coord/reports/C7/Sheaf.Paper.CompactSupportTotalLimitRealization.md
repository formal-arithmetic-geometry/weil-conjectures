## What changed

Proved `WeilConjectures.sfCompactSupportTotalLimitRealization` in
`Sheaf.Paper.CompactSupportTotalLimitRealization`. The public theorem signature
and the definition of `sfCompactSupportTotalLimitFunctor` are unchanged.

The proof reuses the proved complex-level Roos construction from
`RingedStrictTowerHomotopyLimitIndependentCoefficients` through a proof-only
`import all`. Private proved helpers over an abstract abelian category identify
its evaluations and first arrow with the canonical coefficient-tower evaluations
and resolution-normalized
projections. The connecting arrow is natural. Product evaluation isomorphisms
then transport that triangle to the stated compact-support system. Linearity
uses the proved source-library `linear_rightDerivedFunctor` instance, together
with equality of the normalized scalar actions. The shift and distinguished
triangle formulas use the literal composite functor.

The final assembly uses a private proposition alias, proves it for the canonical
chosen tower, and transports the result along the stipulated tower equality.
Explicit existential and conjunction introductions retain the specified scalar,
shift and evaluation choices without expensive nested constructor inference.
The normalized scalar comparison reuses the proved private helper from
`CompactSupportRepresentativeIndependence` through a proof-only `import all`.
Local irreducibility prevents completed-sheaf implementations and the
constructible predicate from unfolding during elaboration. The private proposition alias is marked
`no_expose`, avoiding expensive abstraction of its nested proof terms.
The shift identity uses the proved generic composition lemma. A private
compatibility theorem takes the tower and its evaluation maps as parameters,
and packages its composite shift together with the compatible maps; the final
assembly instantiates it at the specified chosen tower. This keeps the compatibility proof independent of repeated dependent choice projections.
The canonical assembly takes the limit shift as data, with its
triangulatedness proof, so it checks the clauses without repeatedly expanding
the derived shift construction. Scalar-normalization calls name their underlying
linear structures explicitly.

Updated the existing DAG node's proof, proof dependencies and proof origin to
record this route. No public statement, definition, target, or adopted source
module was changed. The original public declaration docstrings are preserved.
No existing instance attributes are changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.sfCompactSupportTotalLimitRealization`
(node `lem-sf-compact-support-total-limit-realization`).

One of one holes closed; zero holes added; zero holes remain in the item.
No result was split off. Every private helper is proved.

## No longer needed

Removed the original proof import
`Sheaf.CategoryTheory.KInjectiveTotalDerivedLinear` and the proof dependency
`lem-weil-kinjective-total-derived-linear`, including its obsolete top-level
`tool_uses` entry. The proved source-library
`CategoryTheory.Functor.linear_rightDerivedFunctor` supplies this argument.
This removes this item's dependency; it does not withdraw that module or its
other consumers.

Removed the redundant direct import of
`Mathlib.Algebra.Homology.DerivedCategory.Linear`; the proved source-library
linearity module publicly imports it. Removed the unused draft import
`Mathlib.Algebra.Homology.DerivedCategory.ShortExact`. The source-library
`RightDerivedFunctor.ShortExactPullback` import is needed for normalization of
the derived unit on K-injective complexes.

The proof retains `Sheaf.Paper.CoefficientConstantTowerRoos` through a proof-only
`import all`: its private derived evaluation and transition helpers are used by
the generic normalization argument. Its objectwise triangle theorem alone does
not provide the natural connecting arrow required here.

The other original dependencies remain needed. In particular, the ringed
strict-tower module remains imported and its proved construction is used.
No Lean modules or declarations are withdrawn, and the blueprint unit route
is preserved.

## Where the brief, the DAG or earlier work was wrong

The abstract existential Roos-triangle interface alone does not identify its
first arrow with the fixed canonical coefficient-tower projection in this
item's statement. The proof therefore uses its existing proved construction
and proves the projection normalization by the canonical projection's
uniqueness property. The normalized scalar structures also require an explicit
comparison with the standard derived scalar structures before composition.
Neither issue requires changing the statement. No statement is disputed.

Inspection of the elaborated private copy also shows that the equality
`sL = (inferInstance : (coefficientConstantTowerLimit ...).CommShift ℤ)` uses the
explicitly bound `sL` as that instance. Thus this equality is reflexive rather
than an independent canonicality condition, contrary to the earlier statement
review's description. This delivery preserves the statement verbatim and
explicitly chooses the canonical right-derived shift, so its realization still
has the intended canonical shift.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
