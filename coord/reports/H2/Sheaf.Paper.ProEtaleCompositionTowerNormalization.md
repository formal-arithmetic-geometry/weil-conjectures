## What changed

The original theorem `AlgebraicGeometry.ProEtale.proEtaleCompositionTowerNormalization`
now has a complete Lean proof from an equality-only split and the existing library.
Private helpers prove transport of the bounded-below exchange and open unit into the
unbounded category, identify lambda with the canonical site restriction, identify its
open adjunct with the proper/open site mate, and prove lambda and gamma invertible.
Naturality transports these results along any supplied etale-origin witness. For the
specified input `J_j nu^*L`, the proof constructs the explicit etale witness `j_!L`.
No arbitrary data is chosen from an existence theorem.

The remaining canonical compositor equality is stated separately as
`AlgebraicGeometry.ProEtale.proEtaleCompositionTowerFormula`, for finite rings and
Noetherian schemes, assuming the already-proved invertibility of lambda. It says only
the equality clause, not invertibility on all witnessed inputs. Its source and complete
natural-language proof are in its docstring and new node. The original theorem combines
this equality with its independently proved invertibility clauses.

To avoid an import cycle, move the thirteen original tower constructions byte for byte
into `Sheaf.Paper.ProEtaleCompositionTowerDefinitions`, publicly imported by the original
module. This is a dependency separation for a genuine logical decomposition, not a way
to evade a compile limit. Original public imports, names, visibility, universes,
signatures, and construction bodies are preserved. In particular the origin compositor
is still independently specified by `originCompositionAmbient`; it is not defined as
the desired formula. The existing candidate-comparison node follows its definition.
No source-library file or target statement is edited.

Validation: the three-module packet compiles through `lcompile.py`; the main proof has
no sorry. Mechanical comparison confirms all thirteen construction blocks are byte
identical to the current source. The theorem signature is byte-identical to current source. All five direct consumers compile unchanged against the delivered modules:
ProperCompositionSiteTransport, ClosedSectionCompactOrigin, FiniteTripleProductNormalForms,
ProductExchangeCounitCoordinates and ProjectionCompatibleTriangleAssembly. No consumer
source is included or adapted. The delivery compile passes. The first preflight rejected only the new construction
node signature record (it included the abbreviation body); the record now uses the
checker-extracted signature. Its search-category advisory is fixed by recording an
actual additional LeanSearch query. The delivery tool reruns final preflight.

## Proved and sorry left

Closed one original hole syntactically:
`AlgebraicGeometry.ProEtale.proEtaleCompositionTowerNormalization`.
Its witness and isomorphism clauses, including invertibility for arbitrary supplied
bounded-below etale-origin witnesses, have complete proofs. The combination of those
clauses with the equality split is complete.

Added one hole:
`AlgebraicGeometry.ProEtale.proEtaleCompositionTowerFormula`
(node `lem-trf-proetale-composition-tower-formula`), proof exactly `:= by sorry`.
It is strictly the remaining canonical-composition equality under an `IsIso lambda`
hypothesis, and asserts none of the independently proved invertibility clauses.
Thus this delivery is a decomposition, not one net sorry eliminated: one closed,
one added, net zero. There are zero holes in the original item module, zero in the
construction module and one in the equality module. No private helper or definition
contains sorry. Existing imported sorry statements are used as the stage-3 brief allows.

## No longer needed

No whole module is withdrawn or claimed globally pruned. The equality clause still
needs the finite-site pasting and canonical origin/candidate coherence theory; those
are assigned to the split node rather than discarded. The unit route is retained.

Removed from the main proof's imports:

- `Sheaf.Paper.FiniteSiteTowerPaste`
- `Sheaf.Paper.CompactSupportSiteCoherence`
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`
- `Sheaf.Paper.CompactSupportExchangeTransport`
- `Sheaf.Paper.RefinementComparisonComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`

The main proof writes the explicit etale `j_!` functor instead of importing the
FiniteSiteTower alias. The canonical-origin module remains an original public import;
only its extra `import all` access is removed. The construction module also drops the
following proof-only imports inherited from the original file, since it has no theorem
proofs needing them:

- `Sheaf.Paper.UnboundedProperOpenInterchange`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`
- `Sheaf.Paper.FiniteLevelProEtaleBaseChange`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.Paper.CondensedAmbientExchange`
- `Sheaf.Paper.EtaleOriginDerivedCategory`
- `Sheaf.Paper.ProperOpenCoefficientMate`

The duplicate private `LowerShriek.Open.Defs` import is removed from the construction
module. The main node no longer directly lists these old proof dependencies:

- `def-compact-support-direct-image-detailed`
- `def-weil-pbc-ambient-ringed-exchange`
- `lem-trf-open-square-exchange`
- `lem-weil-derived-direct-image-composition`
- `lem-weil-pbc-conjugate-iso-unit-equation`
- `thm-sf-comp-composition`

Dependencies still needed for the equality are retained in the new formula node or
its cited definitions. `lem-trf-open-square-exchange` is not needed by this proof:
ordinary constant-ring exchange is treated directly via its adjunctions and the
bounded-below inclusion, without the intrinsic-open-square theorem.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was interrupted by a genuine compile-server disk failure; it had
not delivered. The resumed server accepts compiles. Its unfinished private proof drafts
have been checked and corrected. The module's only original sorry combined two distinct
obligations: arbitrary-witness invertibility and identification of the specified canonical
composition. The first is now proved, the second explicitly split off. No false statement
or target-signature defect was found. The new proof uses `lem-amb-open-site-evaluation-counit`,
`lem-amb-compact-support-proper-factor`, and `lem-kun-unbounded-exchange-agrees`
as tools: their generic unit and bounded-below exchange compatibility is needed
to connect the actual tower definitions with the already-specified site mate; the
Weil-push unit has no such compatibility statements. The equality split uses
`lem-sp-finite-site-tower-paste` and `lem-pur-compact-support-site-coherence` as
construction-coherence tools, retaining the original composition route.
Mathlib searches for the complete formula returned
no exact match; its generic mate and adjunction APIs are used in the proof.

Edge cases checked before stating the split: for identity opens the open-adjunction
compositor and units specialize to the corresponding triangle identities; for identity
proper maps the direct-image compositor is the canonical identity normalization. The
empty source gives maps on the zero extension. Zero coefficients also yield the zero
module category. No finite-field hypothesis or properness of h or f is introduced. The
hypotheses of the split are supplied explicitly from finite type over the arbitrary
field and properness of the compactification arrows. Adjunction is used to identify
maps, never to infer that an adjunct of an isomorphism is invertible.

## New nodes

`lem-trf-proetale-composition-tower-formula`: the equality-only remainder, from the
Construction paragraph of the current blueprint composition proof (Stacks 0F7J).
It is one strictly simpler step, not the original theorem under a new name. Its proof
plan evaluates the canonical origin map in etale coordinates, applies finite-site
pasting, and identifies the proper/open factor by its transpose.

`def-trf-proetale-composition-tower-data`: records the twelve unchanged concrete
constructions moved into the common definitions module. The thirteenth,
`towerCandidateComparison`, keeps its existing owning node
`def-sf-origin-candidate-comparison`, whose Lean attachment is updated.

Change record: `coord/changes/H2-proetale-tower-definitions.md`.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
