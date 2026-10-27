## What changed

Partial proof delivery of WeilConjectures.SmoothPurity.Defs, starting from the
current source including the E1 and A2 partial proofs. The archived source is
preserved; no quarantine file is deleted or treated as withdrawn.

Added three fully proved private helpers. smoothTrace_finiteQuotientSquare proves
the native finite gamma quotient square, including the coefficient-unit map:
compose ReductionData.pro_purity with that map, use pro_natural, and identify the
remaining source map by finitePuritySourceUnitReduction. Equal-level quotients
are included. Its only new import is private.

smoothTrace_normalizedFiniteSystem extracts the finite levels and their reduction
data from the native reconstruction result, reindexes at n+1, proves all the
quotient squares, and retains ReconstructionResult for the same compactification
and witnesses. It extracts data only inside a proof; no definition chooses them.

smoothTrace_normalizedComparison_unique constructs the comparison from the
supplied representing pairing and source/target isomorphisms, and proves that its
exact counit formula determines it uniquely. The existing private
smoothTrace_from_representing_pairing now consumes this theorem, with its
signature and docstring unchanged. This proves uniqueness for explicit inputs;
it does not select an arbitrary purity isomorphism or construct a geometric trace.

Updated the existing isIso route node to record these partial steps and the
additional finite root-balancing dependency. Its statement and unit route stay
unchanged. No new node or public declaration is introduced.

The compile repair keeps the actual chosen lower/upper shriek functors, their
adjunction and ReconstructionResult locally irreducible inside Purity. The latter
is explicitly unfolded for its finite-system projection. HasDerivedCategory.standard
and Functor.leftAdjoint are locally irreducible only in FiniteNative. Spec stays
locally irreducible inside PointObstruction, and Over.mk is folded only during the
original instance registrations, then restored to semireducible. Every original
registration and declaration is retained. Elaboration is synchronous in this file.
The existing private smoothPurityMap_of_reconstructed_trace proof now names its
lifted Tate comparison, composite and two equations separately, avoiding expensive
elaboration of one nested constructor. Its signature and statement are unchanged.
None of these controls changes an exported definition or reducibility attribute.
Edge cases: every finite level is n+1, so no zero-level quotient is used. The
quotient proof includes b=a and d=0; it needs no nonempty-scheme, odd-prime or
nonzero-coefficient premise. The uniqueness argument is purely categorical and
uses exactly the supplied pairing, including when its source is a zero object.

All source public signatures, attributes, public imports and non-theorem bodies
remain unchanged. No other existing Lean module is edited.

Validation: the final module compiled cleanly through lcompile.py in 45.0 seconds,
with exit code zero and no warnings. All profiler and trace settings are removed.
The original source compiled in 59.2 seconds. The first delivery probe exceeded
60 seconds and did not push; the additional local unfolding controls reduced the
final clean file compile to 45.0 seconds. No limit was increased. No direct importer
needs adaptation because public signatures and definition bodies are identical.

Change record: coord/changes/C3-smooth-purity-normalized-comparison.md.

## Proved and sorry left

0 of 4 original holes closed; 0 holes added; 0 split off. This is partial proof
work and local compile repair, not a completed trace-definition repair or a
proof of the disputed unconditional purity statement.

New fully proved private declarations:

- AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace_finiteQuotientSquare
  (finite coefficient compatibility step of lem-route-is-iso-smooth-purity-map).
- AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace_normalizedFiniteSystem
  (native finite-system and reconstruction inputs, Step 1 of the same node).
- AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace_normalizedComparison_unique
  (normalized comparison assembly in lem-route-is-iso-smooth-purity-map).

Retained original holes:

- AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace
  (def-route-smooth-trace).
- AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap
  (lem-route-is-iso-smooth-purity-map).
- AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_zero_of_isOpenImmersion
  (lem-route-smooth-purity-iso-zero-of-is-open-immersion).
- AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_comp_openImmersion
  (lem-route-smooth-purity-iso-comp-open-immersion).

The finite square uses the existing named finitePuritySourceUnitReduction theorem,
which itself still has sorry. No new sorry is introduced, inside a definition or
elsewhere. The existing hollow smoothTrace remains an explicitly reported legacy
hole; the delivery does not disguise its mathematical construction as a proof.

## No longer needed

None. No existing import, node, module or declaration is removed or withdrawn.
The finite, integral, realization and normalized trace dependencies remain needed.
Mathlib searches via Loogle, LeanFinder and grep found generic adjunction uniqueness
and Hom-bijection lemmas, used in the new uniqueness argument. They do not supply
the geometric normalized trace or its realization comparisons.

## Where the brief, the DAG or earlier work was wrong

The rework row refers to SfP1ProjectionTraceFalseTail, but both the current source
and the preserved archive already omit that import. Removing it is therefore not
claimed as work by this packet. The current source includes the E1 partial proof
delivery; it is the base used here.

The existing STATEMENT-DISPUTED warning remains valid. The elaborated purity
instance lacks SmoothOfRelativeDimension d f.left, although the node requires it.
The existing private point counterexample is proved before that instance. No
listed upstream statement exception allows correcting this signature. The new
proofs occur before the instance and do not use the contradiction it would yield.

The geometric reconstruction pairing, identification with the prescribed Tate
realization, and actual definition of smoothTrace are still missing. The new
uniqueness theorem does not assert their existence or normalize an arbitrary
trace. The finite quotient proof is only the precise finite-level compatibility
needed by that construction, not its integral or condensed realization.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
