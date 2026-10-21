## What changed

Proved `CategoryTheory.ringedTripleResolution_formulas` without changing its statement
or the definition `Functor.HasTripleResolutionFormulas`. All work is in the assigned module.
Private proved helpers compute the localized image of a homotopy class, express naturality
in arbitrary resolution coordinates, and evaluate a derived unit on K-injectives.
A generic private calculation then constructs all seven coordinates, the unique class u,
the four factor equations, their two products, and the two specified canonical transitions.
Small-site Grothendieck abelianness supplies K-injective resolutions. Added the private
source-library import `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
for its resolution instance. Server compilation of the complete proof passed in 22.8 s;
its two sequence-style warnings were then corrected before delivery verification.
The subsequent axiom-probe compile also passed without warnings. Preflight requested a change
record for added section commands; those commands were removed by spelling out private helper
binders, and the static comparison now reports no interface change.

## Proved and sorry left

Closed the one original hole, `CategoryTheory.ringedTripleResolution_formulas`
(node `lem-pur-ringed-triple-resolution-formulas`). Holes added: zero. Holes left: zero.
No decomposition or new public statements.

## No longer needed

Removed the redundant private import
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` (already public through
`KInjectiveDerivedMapComputation`). The map-computation theorem for a specifically chosen
universal derived pair is unnecessary: the proved private `resolution_naturality` and
`coordinate_map` compute directly from the supplied unit of the arbitrary derived functor.
The dependency's real definitions `kInjectiveResolutionHomTarget` and
`kInjectiveHomotopyImage` remain used, and its public import remains.
The pair-composition theorem need not be invoked existentially: the given normalized
comparison and its naturality prove the coordinate formulas directly. Its public import
remains and its K-injective derivability lemma `CategoryTheory.derives` is used.
No DAG dependency or module is withdrawn; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. The available derived-map theorem chooses
its own derived pair; direct naturality is shorter for the arbitrary six derived pairs
already supplied here. Quasi-isomorphy of g_*j follows from the normalized comparison,
not from preservation of K-injectives. Only I, J, K, T and the primed resolution targets
are assumed K-injective. Empty/zero complexes and identity resolutions require no special
case, since the argument uses only isomorphism cancellation and Hom bijectivity.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
