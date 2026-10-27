## What changed

Filled `CategoryTheory.Mod.shortExact_of_sectionwise`, preserving its signature,
all three short exactness conclusions, and their prescribed arrows. Evaluation
jointly reflects isomorphisms, so Mathlib's `shortExact_iff` detects the presheaf
short exact sequence. Exact sheafification and `sheafificationNatIso` give the
original sheaf sequence. The existing internal-module forgetful functor reflects
isomorphisms and preserves finite limits and colimits, so the singleton-family
case of the same criterion gives the internal-module sequence.

The canonical tensor and all existing instance definitions are unchanged.
Server single-file compilation passed in 4.7 seconds; applied the compiler's
local-instance syntax suggestions before final delivery validation.

## Proved and sorry left

Closed one of one holes: `CategoryTheory.Mod.shortExact_of_sectionwise`
(blueprint `lem-pe-internal-module-sectionwise-short-exact`).
Added zero holes; split off zero statements. No sorry remains in the item.

## No longer needed

Removed redundant private imports, whose interfaces remain available through
the unchanged public imports: `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`,
`Mathlib.CategoryTheory.Abelian.FunctorCategory`, `Mathlib.CategoryTheory.Sites.Abelian`,
`Mathlib.CategoryTheory.Sites.Limits`, `Mathlib.CategoryTheory.Sites.Sheafification`,
`Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`, and
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.

No mathematical dependencies or modules are pruned: the proof follows the
presheaf, exact-sheafification, and internal-module-forgetting route in the node.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The inverse-linearity argument in proof step 4 is
already implemented by the source library's `Mod.forget` reflection instance;
the proof reuses that instance.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
