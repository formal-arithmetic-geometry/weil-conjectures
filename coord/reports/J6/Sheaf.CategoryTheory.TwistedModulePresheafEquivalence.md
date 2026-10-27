## What changed

Proved `CategoryTheory.InternalActionSite.module_presheaf_equivalence` in
`Sheaf.CategoryTheory.TwistedModulePresheafEquivalence`, with its statement unchanged.
Private constructions give extension by action after restriction, recovery from label-one
and vertical arrows, strict object and morphism round trips, and identity section components
for the unit and counit. Both functors preserve addition. Matching families on corresponding
sieves have the same unique amalgamations, giving preservation and reflection of sheaves
and the restricted additive equivalence. The coefficient sheaf follows by applying that
comparison to the rank-one module with trivial action; the proof does not invoke the
parent presentation theorem or its coefficient-sheaf hole.

Updated the existing node's proof to follow these constructions directly at the
Grothendieck-topology level. No existing public statement, definition or instance was changed.

## Proved and sorry left

Closed 1 hole: `CategoryTheory.InternalActionSite.module_presheaf_equivalence`
(node `lem-sfb-twisted-module-presheaf-equivalence`). Added 0 holes; split off 0.
No `sorry` remains in the delivered module. All private helpers are proved.
The proof uses the existing stated sieve-geometry theorem and existing category/action
interfaces; their separate unfinished proofs are not part of this delivery.

## No longer needed

`lem-weil-pbc-pretopology-sheaf-condition` is not needed by this proof: both sides of
the statement already use generated Grothendieck topologies, so the covering-sieve
comparison applies directly. Its other library users remain unaffected.

Removed the redundant private imports `Sheaf.CategoryTheory.Sites.GrothendieckTopos`,
`Mathlib.CategoryTheory.Sites.SheafOfTypes`, and
`Mathlib.CategoryTheory.Sites.EqualizerSheafCondition`. The sieve and sheaf APIs used
are already available from the public dependencies; no equalizer argument is used.
All existing public imports are preserved.

No modules are withdrawn. No new nodes are introduced.

## Where the brief, the DAG or earlier work was wrong

The DAG's conversion from a base pretopology sheaf condition is unnecessary for the
existing Lean signature. The rest of its explicit construction and matching-family
argument is retained, with no change to the unit route. Edge cases require no additional
hypotheses: the matching-family proof includes empty sieves, the construction accepts
zero rings and modules, and the trivial group gives the ordinary restrictions.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
