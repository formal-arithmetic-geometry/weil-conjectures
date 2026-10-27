## What changed

Filled the proofs of `WeilConjectures.constantExtensionRestriction_data` and
`WeilConjectures.constantExtensionRestriction_normalization` without changing either
statement or any existing definition. The residue-compositum proofs and the final
assembly theorem remain as before.

The proof reuses `sheetReturnExactFunctor`, rather than rebuilding the cyclic
fixed-pair equivalence. It proves the carrier comparison, uniqueness of functors
satisfying the restriction specification, exactness of actual Weil inverse image,
and the natural coordinate recursion with its successor equations. The return
equation is transported through an actual Weil isomorphism. The functor comparison
returns `Nonempty` and is unpacked inside the proof, so no data definition chooses
a witness from a mere-existence theorem. Small proved equations for the forgetful
functor and explicit functor associators avoid unfolding the entire pullback
construction when checking coordinate isomorphisms. All associator components
are identities. A proved generic comparison helper keeps its categorical composition
abstract during kernel checking. The finite-field record is locally
`implicit_reducible` so its base-field projections are available to implicit
type comparison; this does not change an exported attribute or definition.
Private generic lemmas construct the finite chain and compose the return squares;
the sheaf proof specializes their laws with the concrete pullback functors folded.

Added `Sheaf.Paper.ConstantExtensionPullbackSheetComparison` for the one remaining
ordered-iterate/compositor equality. This compares already constructed morphisms
on an actual pullback carrier; it neither asserts a restriction equivalence nor
repackages either original existence/normalization statement. Its proof in words
is the induction on ordered iterates using normalized pullback composition.

New proof imports are `ZlWeilHeartLocalizationExact`,
`ConstantExtensionReturnExactFunctor`, `ConstantExtensionPullbackSheetComparison`,
the proved source `WeilConjectures.Mathlib.NumberTheory.Padics.Complex`, and
`Mathlib.AlgebraicGeometry.Morphisms.Separated`, and
`Mathlib.CategoryTheory.Preadditive.LeftExact`.
The p-adic source supplies an abstract coefficient-field isomorphism needed only to
instantiate the existing localization exactness theorem. No source-library
signatures, definitions, or attributes were changed. The returned version had an
unnecessary public import of `ConstantExtensionWeilHeartEquivalence` in the assigned
module; removing it and importing `ConstantExtensionWeilHeartData` directly keeps the
data declarations available while breaking the reported cycle through the equivalence
module.

Updated the two original proof nodes and their assembly node, and added the comparison node. The unit's
finite constant-extension route is retained.

Validation: `lcompile.py` accepted both sandbox modules. The assigned module compiled
in 25.7 seconds. Profiling and checkpoint commands were removed for delivery.

## Proved and sorry left

Closed the two original holes, by reduction from existing declared dependencies
and the new comparison equation:

- `WeilConjectures.constantExtensionRestriction_data`.
- `WeilConjectures.constantExtensionRestriction_normalization`.

The assigned module has zero remaining `sorry`. Added one hole:

- `WeilConjectures.pullbackSheetReturnComparison`, in
  `Sheaf.Paper.ConstantExtensionPullbackSheetComparison`, node
  `lem-zl-pullback-sheet-return-comparison`.

This is a decomposition of the two upper statements into one strictly smaller
coherence equation, with the categorical and exactness glue proved. It is not a
claim that the entire constant-extension argument is independent of `sorry`:
`sheetReturnExactFunctor`, `zlWeilHeartLocalizationExact`, and
`constructible_pullback_t_exact` are existing stated dependencies. The new hole
is a named public theorem with source, complete proof in words, and a matching
node; no data definition contains a hole.

## No longer needed

No whole module is withdrawn or claimed globally pruned. In particular the source
library remains intact. The equivalence import removed from the assigned module was
only a redundant public re-export: the assigned declarations use the lower data module,
and the equivalence module remains available to its own consumers.

The two assigned proofs no longer directly construct or invoke
`constantExtensionSheetHeartCoordinates` or `cyclicReturnExactEquivalence`; they
reuse the already stated `sheetReturnExactFunctor` which encapsulates those
steps. Their nodes therefore replace the direct coordinate-equivalence proof
route with that existing theorem and the concrete pullback comparison. These
coordinate/cyclic dependencies remain needed by that theorem and must not be
removed from its own route.

The assembly node also drops its now-transitive direct references to
`def-dl-a1-constant-extension-data`, `def-weil-constructible-heart`,
`def-weil-weil-sheaf-complex`, `def-zl-weil-ind-sheaf-category`,
`lem-pod-integral-pullback-composition`,
`lem-zl-constant-extension-sheet-heart-coordinates`, and
`lem-zl-cyclic-return-exact-equivalence`. Their mathematics remains used below
the two assembly lemmas or the existing sheet-return theorem; these are edge
simplifications, not withdrawn modules.

No new local-operator or weight theorem is needed. The argument uses none of the
local-operator or weight clauses of the parent
`constantExtensionWeilHeartEquivalence` theorem.

## Where the brief, the DAG or earlier work was wrong

The former proof plan suppressed the equality between the normalized ordered
return of actual inverse image and the restriction compositor. The new node
states this equality with the actual existing maps, rather than assuming an
unspecified comparison of functors.

The normalization theorem accepts an arbitrary equivalence satisfying
`ConstantExtensionRestrictionSpec`; its proof cannot silently assume that this
equivalence satisfies the stronger sheet specification. The proof uses a
separate sheet-return functor, compares the two restriction functors through
their carrier specifications, and transports the return equation along that
Weil isomorphism.

The exactness proof uses the already proved source theorem
`PadicAlgCl.nonempty_ringEquiv_complex`, then `IsAlgClosure.equiv`, only to supply
the unused coefficient-realization parameter of the localization theorem. Its
source proof is the direct application of Mathlib's classification of
uncountable algebraically closed fields to the closed p-adic algebraic-closure
and complex-cardinality facts. No weight theorem or unproved
extension-of-embeddings theorem is imported or needed.

Edge cases checked in the statements and construction: `m = 1` has no successor
equations and uses only the base return square; zero carriers and empty or
disconnected schemes require no additional hypotheses. No lissity is assumed.

## New nodes

`lem-zl-pullback-sheet-return-comparison`:
`dag/nodes/sec-deligne-laumon-general/lem-zl-pullback-sheet-return-comparison.json`,
realized by `Sheaf.Paper.ConstantExtensionPullbackSheetComparison` and
`WeilConjectures.pullbackSheetReturnComparison`. It is the normalized compositor
calculation for the ordered Weil iterate of actual inverse image, extracted
from Deligne, Weil II, (1.1.10) and the following change-of-finite-base paragraph,
pp.151--152. Both assigned proofs need it via the restriction-specification
comparison. No change record is needed because existing statements and data
are unchanged.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
