## What changed

Proved `finiteProperLocalizing`, the proper pushforward clause on the localizing categories.
The retained base-change clause is still being repaired. The proof uses
normalized finite discrete coefficient encodings, the existing finite proper theorem on
Dctf generators, and the adopted source coproduct theorem for etale-origin cohomology.
The tested base-change draft extends through the localizing isomorphism locus.
The public statements and
coefficient constructions are unchanged. All new helpers are proved and private.

The open-immersion and compactification proofs already present in the current source
are retained. Continuity of maps between discrete coefficient rings is now proved
explicitly instead of through `fun_prop`. Private proof imports and the node proof route
are updated to match the implementation.

The proper-pushforward clause compiles in the full module at the delivery path (45.2 s).
Its cached instances and opacity settings are scoped away from the original coefficient
definitions and admissibility proof. The pullback proof keeps the canonical `unboundedLocalizingPullbackCommShift`.
A private `import all Sheaf.Paper.FiniteProperExchange` exposes the exchange body for
identifying the two specified mates. The packet reuses the landed finite proper
generator helpers and their local instance caches.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.finiteProperLocalizing` (one of the two original holes).
Remaining: `AlgebraicGeometry.ProEtale.finiteProperLocalizing_baseChange`.
Added: zero holes and zero split statements. The delivery module currently has one `sorry`.
The prior proved `finiteOpenLocalizing` and `finiteCompactificationLocalizing` remain proved.

## No longer needed

No original import is removed and no module is withdrawn. The added direct import of
`Mathlib.CategoryTheory.Shift.Adjunction` was removed because
`Mathlib.CategoryTheory.Triangulated.Adjunction` publicly supplies it. The proof uses the small
`Sheaf.CategoryTheory.Triangulated.LocalizingSubcategoryUniverse` API rather than importing
`Sheaf.SixFunctors.FiniteCompactProetale` for its private universe-closure helper. The proof does not directly
need the planned `FiniteClassicalLocalizing`, `FiniteProperClassicalCoproducts`,
`FiniteProperClassicalTruncation`, or `ProperGeometricFibreCohomologicalBound` modules.
The source `LowerStarCoproducts` theorem already proves the requisite classical coproduct
comparison; localizing minimality and the isomorphism locus replace a second truncation
argument in this module. Those four nodes are removed from this node's direct proof
edges. This is a local dependency reduction, not a claim that their other consumers can
be deleted.

The remaining former direct edges now supplied through the existing finite proper
proof and coefficient encoding are `det-ctf-finite-proper-tor`,
`det-pe-finite-tor-comparison-noetherian`, `lem-pc-separated-quasi-separated`,
`lem-weil-pbc-finite-discrete-condensed-ring-constant`,
`lem-weil-pbc-finite-discrete-scheme-ring-constant`,
`lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-locally-noetherian-quasi-separated`,
`lem-weil-pbc-triangulated-functor-restriction`,
`sk-thm-pe-direct-image-comparison`, and `sk-thm-properbasechange`. They need no separate
imports or new proofs here; no upstream declaration or proof is removed.

## Where the brief, the DAG or earlier work was wrong

The rework/quarantine description is stale relative to the current readable source:
the live module has already been restored, and the recovered open proof has already
been repaired and landed. Its two remaining holes are the proper and base-change
clauses. The delivery starts from that current text and does not restore an old file
wholesale or withdraw its quarantine archive.

The older DAG plan requested a separate finite-window argument. The already proved
adopted source coproduct theorem, together with the current finite proper generator
comparison, gives the needed assembly directly. The unit's etale preservation,
coproduct, and unbounded base-change route is retained. No mathematical statement is
changed or disputed.

Proof-context record: `coord/changes/E9-finite-proper-localizing-proof-context.md`.

## New nodes

`lem-sfb-source-etale-origin-proper-coproducts` attaches the existing complete source
proof of `isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology`.
It records the ordinary coefficient interface used directly by the proof, with no
new module and no new hole. The intrinsic coefficient variant in the earlier plan
has a different presentation and an extra supplied fibre bound. The source declaration
is preserved verbatim.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
