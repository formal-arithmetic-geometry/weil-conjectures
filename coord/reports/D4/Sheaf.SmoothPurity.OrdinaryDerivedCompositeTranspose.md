## What changed

Proved `WeilConjectures.PurityFiniteSetting.ordinaryDerivedCompositeTranspose` in
`Sheaf.SmoothPurity.OrdinaryDerivedCompositeTranspose`, with its existing signature unchanged.
Three proved private helpers establish successive transposition, transposition through
conjugation, and the normalization of the actual finite direct-image compositor.
The latter uses the proved source theorem
`Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv`, then compares the exact-map
derived adjunctions with the published K-flat derived adjunctions using
`Adjunction.derived_eq_ofNatIsoLeft` and the left-derived counit factorization.

The proof imports `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate`
and `WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction` privately.
Updated the item's DAG proof, proof dependencies and proof origin to match this route.
The declaration docstring now describes the implemented proof. No definitions or statements
changed, no new public declarations, no new nodes, and no source-library modifications.

Validation: the server compiled the module cleanly. A temporary `#print axioms` check of
`ordinaryDerivedCompositeTranspose` reported exactly `propext`, `Classical.choice`, `Quot.sound`.
The temporary command is absent from the delivery. Import-direction checks allow both
new proof imports. The sole downstream module is
`Sheaf.SmoothPurity.OrdinaryTripleProductTranspose`; its imports already supply each removed
public dependency, and the server compiled it unchanged against the sandbox version. Its validation copy
was then removed from the packet, so this delivery changes only the assigned module.

## Proved and sorry left

Closed 1 original hole:
`WeilConjectures.PurityFiniteSetting.ordinaryDerivedCompositeTranspose`
(node `lem-pur-ordinary-derived-composite-transpose`).

Added 0 holes; split off 0 statements. No `sorry` remains in the item or is added elsewhere.
All three private helpers are fully proved. The item has no dependency on `sorryAx`, as
confirmed by the axiom check, so this is a proof rather than a decomposition.

## No longer needed

Removed the private import `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` and the
public imports `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`, and
`Sheaf.Paper.IntegralFinitePullbackComposition`. The theorem's statement uses the existing
fixed-scalar operations already provided by `Sheaf.Paper.FiniteDirectImageComposition`.

The proof no longer uses `lem-sfb-ringed-derived-monoidal-comparisons` or
`lem-pur-proetale-constant-ring-composition`; both are removed from the proof dependencies
and the obsolete `tool_uses` entries. Their Lean modules are unnecessary for this proof.
The general ring-sheaf and integral tower constructions of
`Sheaf.Paper.IntegralFinitePullbackComposition` are also unnecessary for the fixed-scalar
compositor normalization. The existing fixed-scalar pullback composition declaration
attached to `lem-weil-pbc-proetale-derived-pullback-composition` is still used.

These removals concern this proof's dependencies; none of these modules is withdrawn,
and their other consumers and declarations are preserved. The unit `sk-prop-an` has empty
`realized` statement and step attachments, and no unit statement or prescribed step is
bypassed or modified.

## Where the brief, the DAG or earlier work was wrong

The old plan routes normalization through a complete ringed-topos monoidal comparison
system. That is unnecessary here: the inverse image with fixed module coefficients is
exact, and the proved generic source composition-conjugacy theorem gives the required
K-injective normalization directly. The small adjunction-transport calculation supplies
the precise K-flat left comparison; no identification of arbitrary chosen systems is used.

The revised proof cites `lem-sfb-derived-composition-adjunction-normalization` for its
already proved source specialization recorded among that node's Lean candidates,
`Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv`. This source theorem is
imported directly; the larger Sheaf normalization theorem and simultaneous monoidal system
are not needed. The new proof dependency is a tool from another unit; its source theorem
is proved, and this packet does not add maintainer approval entries.

No false statement or missing hypothesis was found. The two generic categorical helpers
are uniform in arbitrary objects and morphisms, including zero morphisms and identity
adjunctions. The compositor helper needs only a commutative coefficient ring and arbitrary
scheme maps, so all original finite-type hypotheses are preserved without being used to
justify an invalid restriction.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
