## What changed

Replaced the hole in `WeilConjectures.PurStrictScalar.systemProper_existsUnique`
by a construction using `ExactDerivedSquare.square_exists`, the canonical
whole-cochain unit normalization, and `ExactDerivedSquare.square_unique`.
Proved private helpers perform resolution-unit cancellation and unit normalization
over abstract functors before specialization, keeping concrete sheaf-functor
definitions unexpanded. The same resolution-unit helper replaces the duplicate
argument in the existing derived-limit comparison. Its categorical comparison
argument is likewise proved over abstract functors and then specialized, avoiding
expansion of concrete coefficient definitions during normalization.
The existing identity-on-sections ordinary comparison is retained verbatim.
The already-proved `towerConstantRestriction_exact` keeps its forgetful-sheaf
argument and uses the local exact restriction functor explicitly during
pointwise instance search.

The remaining geometric step is isolated in the new module
`Sheaf.Paper.NativeConstantRestrictionAcyclicity`: ordinary direct image sends
a K-injective resolution map of a restricted
native K-injective system to a quasi-isomorphism. The item proves invertibility
of the canonical derived unit from this chain-map assertion by naturality and
cancellation. The lower statement has no derived comparison isomorphism,
normalization, or uniqueness conclusion. The item's proof assembles
those conclusions using the existing proved categorical API.

Added proof-only imports of that module and
`Sheaf.CategoryTheory.DerivedExactSquareCoherence` (with `all` for its proved
private generic helpers). Updated the item's node
to record this reduction. No existing signature, definition body, public import,
or source-library module is changed.

Validation: the new lower module compiled in 37.3 seconds, and the item compiled
in 42.2 seconds after the abstract-functor refactoring. Development profiling
options have been removed. Import-direction checks found no cycles; node
proof-dependency unions and the new node's verbatim Lean statement were checked.

## Proved and sorry left

One of the four original holes is closed in Lean:
`WeilConjectures.PurStrictScalar.systemProper_existsUnique`.
One hole is added:
`WeilConjectures.nativeConstantRestriction_push_quasiIso`
(node `lem-pur-native-constant-restriction-acyclicity`).
This is a decomposition, with net zero holes closed, not a completed proof of
the geometric acyclicity step.

Three original holes remain unchanged, all attached to
`def-pur-native-constant-support-model`:
`WeilConjectures.PurStrictScalar.systemProperOrdinary_existsUnique`,
`WeilConjectures.PurStrictScalar.systemPullMap_isIso`, and
`WeilConjectures.PurStrictScalar.systemOpenMap_isIso`.
The delivered files therefore contain four holes in total (three old, one new).

## No longer needed

No existing imports, nodes, or modules are removed. The existing limit proof and
all its dependencies are retained. The new proper-comparison argument needs
acyclicity for direct image, rather than preservation of K-injective complexes
by the nonflat coefficient restriction. No preservation-of-K-injectives lemma
is added or imported for that restriction.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped without producing a compiling reduction. Its
observation about mates is correct: an invertible square does not in general
have an invertible mate. The present reduction addresses the derived proper
comparison, independently of the inverse/open mate holes.

`ConstantScalarTowerMates.unitCompatible_existsUnique` assumes preservation of
K-injectives and therefore cannot simply be applied to quotient coefficient
restriction. The more general existing `ExactDerivedSquare.square_exists`
requires only direct-image acyclicity and supplies the appropriate interface.
The new lemma's natural-language proof uses normalized composition of ringed
topos direct images, not the false stronger preservation assertion. Its edge
cases include zero complexes, empty schemes, identity morphisms, and nonflat
coefficient quotients. The unit's route is preserved.

## New nodes

`lem-pur-native-constant-restriction-acyclicity`, in
`dag/nodes/sec-smooth-purity/`, states only the acyclicity input for the derived
proper square, expressed entirely as preservation of a specified resolution
quasi-isomorphism by ordinary direct image. Its module has one named public
theorem with `:= by sorry`, a
source citation, and the full sequence-site realization, derived-composition,
and unit-transport argument in its docstring. Existing generic ringed-topos
composition covers the abstract acyclicity argument; identifying the concrete
native restriction and the constant strict-tower presentation is the remaining
formalization work. No change record is needed: existing statements and
definitions are unchanged.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
