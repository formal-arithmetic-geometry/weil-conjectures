## What changed

Proved `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.encoding_compactification`
in `Sheaf.Paper.FiniteDiscreteEncodingCompactification`, with its signature and existing
public imports unchanged. Added private proof imports of
`Sheaf.Paper.FiniteDiscreteEncodingPullbackFixed` (using `import all` to reuse its proved
private `encodingPushforwardNatIso`) and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp`.
No dependency module is changed.

Four proved private constructions supply the natural pullback, open extension-by-zero,
derived pushforward and derived open extension-by-zero comparisons. The first two use
uniqueness of left adjoints; the last two use the existing exact and right-derived
composition isomorphisms. The final proof composes them with functor associators for the
specified compactification, using the supplied encoding at its intermediate scheme.
Updated the item's DAG proof to this implementation.

Searches: LeanFinder for exact-equivalence compatibility with right derivation and
extension by zero found generic derived-factorization APIs, but no complete comparison.
Loogle found `mapDerivedCategoryCompIso`. The msearch grep for the source-library
composition names found no Mathlib match; local rg found the exact right-derived
composition APIs and the already-proved private normalized pushforward comparison.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.encoding_compactification`
(node `lem-sf-finite-discrete-encoding-compactification`). Zero holes added, zero split off,
and zero textual `sorry` remain in the delivered Lean file. All four new private
constructions have complete proofs.

The server single-file compile succeeds. The theorem's axiom audit still includes
`sorryAx` through existing imported library obligations; this delivery closes the item's
own proof and does not claim to close the transitive library. No axiom is introduced.
The construction is functorial on all objects, so it imposes no nonempty-scheme,
nonzero-ring, boundedness, properness beyond c, or quasi-compact-open hypothesis.

## No longer needed

No existing imports were removed. No modules are withdrawn or declared globally unused.
The separate ringed-module operation interface
`def-weil-pbc-proetale-operations` / `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
is not needed for this proof: the target is about fixed ModuleCat-valued sheaves, whose
actual direct image is the source-library `lowerStar` used by the reused comparison.
The wrapper `sk-def-sfb-module-derived-pushpull` /
`Sheaf.Paper.CondensedModuleDerivedPushpull` and the separate arbitrary-resolution
interface `sk-def-sfb-derived-categories` /
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` are not imported or used:
the target's derived functors are already the source-library total right-derived
constructions and exact termwise functors. These three direct proof dependencies are
removed from the node. Their underlying mathematical operations and conventions are
retained via the actual target definitions and the generic source-library APIs.
All other original dependencies remain, and the node of the reused normalized
pushforward/pullback comparison is added. This does not bypass a unit statement or step.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original plan's scalar-action
calculation had already been implemented as `encodingPushforwardNatIso` in the pullback
comparison module. Reusing that proved private result avoids duplicating that argument.
The existing pointwise public pullback theorem alone would not supply the natural
isomorphism needed for adjoint uniqueness, so the proof obtains the natural comparison
from the existing natural pushforward comparison.

The latest blueprint unit proof no longer contains the historical coefficient-identification
steps 11--12 cited by this node. The node statement remains unchanged; the implemented
argument follows its recorded adjunction and K-injective plan and the cited Stacks sources.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
