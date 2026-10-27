## What changed

Proved `ResolutionConjugation.section_resolution_conjugation_identities`, retaining its
original signature verbatim. The proof uses the existing push/pull normalization,
all-complex tensor representative condition, ordinary oplax total comparison, and
K-flat equivalence. It proves the conjugation equations and their naturality for all
internal complexes, then uses resolving membership for inverse-equivalence representatives.

`SectionCochainTensorComparison` exposes the canonical cochain comparison and proves
its naturality by the signed-total summand formula. Fifteen existing tensor caches move
here from `SectionTotalOplaxComparisonData`, which publicly imports them. Their names,
signatures, bodies and attributes are retained; their blueprint links identify the new node.
The new `retainedCochainFunctor` stores the original termwise object and map functions
separately, with their original functor laws. Reflexivity proves its equality with the
original `mapHomologicalComplex`. The cochain section equivalence and the two termwise
pullbacks use this identical representation. The section pullback retains its original
monoidal structure through an explicit instance. This removes repeated expansion of
large cochain constructions in the concrete diagram calculations.

`SectionRepresentativeTensorArrow` exposes the original localization, tensor and unit
components with fixed canonical endpoints. It proves their naturality, representative
normalization and ordinary unit compatibility. Its four internal derived-instance
aliases and typed Q/G/L/comparison aliases return precisely the existing data. No new
localization, resolution, tensor, unit, comparison map or coherence law is chosen.

`SectionDerivedTensorData` imports the cochain interface and explicitly retains the
original localization parameters of both `internalTotalTensor` and `totalTensor`;
their bodies and all current data
bodies and attributes are unchanged. The delivery preserves the D7 component APIs,
regular single unit and direct-object total-functor representation that landed during
this session. `SectionModuleOperationsData.equivalence` keeps its body,
type and reducible status, with a regular definition kernel hint. The assigned module’s
component definitions use these same data, including the original regular units.
All current shared conjugation constructors and inverse laws are preserved.
No target signature or adopted source-library declaration changes.

All seven delivery modules compile without warnings within the file limit; the
conjugation module compiles in about 44 seconds. The latest unchanged realization
consumer also compiles against the delivery. Definition and consumer changes are detailed in
`coord/changes/G6-section-cochain-tensor-interface.md`, including archived consumers.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolutionConjugation.section_resolution_conjugation_identities`
(node `lem-pd-section-resolution-conjugation-identities`).

Holes closed: 1. Holes added: 0. Split off: 0. No sorry remains in any delivered Lean
module. Imported unfinished declarations remain proof dependencies, as required by stage 3.
The two new nodes describe constructed data and proved APIs, not new proof obligations.

## No longer needed

Removed the original direct proof import
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
The output calculation uses the all-complex representative condition, so the assigned
proof steps no longer use `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` or
`lem-weil-pbc-site-derived-tensor-descent` for a separate resolving-preservation argument.
Their obsolete direct proof-step and `tool_uses` entries are removed; statement-level
and transitive dependencies needed for the resolving data are retained.
Ordinary and total comparison naturality are exposed by the cochain component interface.

These dependencies remain needed transitively by existing declarations. No entire
module or declaration is withdrawn, no archived source or attachment is removed, and
no global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The old output-equation plan checked resolving preservation unnecessarily: the first
clause of the existing `TensorRepresentativeCondition` applies to every pair of complexes.
The old plan also left naturality implicit. The proof establishes ordinary naturality
by the unique pure-tensor normalization, total naturality by summand extensionality,
and the requested four squares by composition of natural squares. It reads the stored
forward total conjugation map directly and cancels its two inverse transports.
No mathematical statement is disputed or weakened. The unit route is retained.

## New nodes

`def-pd-section-cochain-tensor-comparison` records the canonical cochain comparison,
shared existing instances, retained termwise functor data, and proved naturality.
Every object and map is the existing one; the retained functor equality is reflexivity.

`def-pd-section-representative-tensor-arrow` records the existing localization and tensor
components, derived-instance and functor aliases, unit components, and their proved
naturality, normalization and unit compatibility APIs. It introduces no hole.

Both nodes and the changed existing proof records follow the actual Lean argument.
The change record is `coord/changes/G6-section-cochain-tensor-interface.md`.

## Forced adaptations

`Sheaf.Paper.SectionOplaxTotalComparison` (unclaimed): the original compiler error was
at line 359 of `equivalence_total_summand`: `unfold totalComparison` failed because
unfolding `totalTensorComparison` now exposes `cochainTensorComparison`. The sole change
adds `cochainTensorComparison` to that existing unfold list. No signature, visibility,
import, statement or other proof line changes. This is the forced unfolding of the
new interface back to the same original comparison.

The unchanged realization consumer, including its latest D7 component APIs, compiles
against the rebased data. It is not adapted or included in the delivery. The unchanged K-flat,
tensor-right, representative-square, normalization, constraint-data and
constraint-diagram consumers all compile against the final rebased data. The unchanged
K-flat consumer emits one unused-section-variable warning; the delivery files have
no warnings. Archived consumers and all their Lean attachments remain
intact; their temporary absence from the library is not pruning.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
