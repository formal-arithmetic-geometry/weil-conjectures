## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.ProjectionRestriction.localBaseData_exists`
by an assembly of separately normalized ordinary and derived constructions, preserving
its statement and the whole `LocalBaseData` structure. The two restrictions are built
using `localizedSystemExact` and the native section-normalized `tensorOverIso`.
Restriction preserves resolving complexes by restriction of K-flat complexes and
restriction of the local equational flatness criterion.

Added `Sheaf.Paper.ProjectionExactTensorComparison`: a proved generic descent of an
additive exact tensor functor preserving small colimits and resolving complexes,
including the representative formula and both signed shift squares. The proved
cochain descent and the two shift verifications are in
`ProjectionExactTensorCore`, `ProjectionExactTensorFirstShift`, and
`ProjectionExactTensorSecondShift`, respectively, so each file stays within the
compile limit after caching the exact-derived factorization and reusing existing
shift helpers. This makes the
existing projection tensor argument usable for restriction functors as well as module
pullback functors. It reuses the existing tensor-model rigidity, representative descent,
and shift-diagram helpers; all shared declaration types and bodies are preserved.

Added `Sheaf.Paper.ProjectionLocalOrdinaryResolving`, isolating only the ordinary
localized exact module pullback, its pure-unit tensor comparison, and preservation
of resolving complexes. The existing generic derived-adjunction construction supplies
the adjunction after this ordinary construction; it is not part of the remaining hole.
All added imports of the item are proof imports. All six proof-packet Lean modules
compiled via the remote compiler. The full descent core, first shift, second
shift, and item compiled in approximately 47, 27, 33, and 32 seconds respectively;
subsequent checks also passed the 60-second per-file bound. The existing structure
text is preserved verbatim; the new restriction proof gives the ordinary functor
an explicit source and target to normalize the coefficient presentation.

The import repair also requires a compile-time refactor of two unclaimed consumers.
The complete normalized adic constructions and exact extension models are moved
verbatim into two lower modules. Their main theorems, signatures, definition bodies,
original imports and proof routes are preserved; the old modules re-export the
constructions. The DAG attachments are partitioned to match their new files.

## Proved and sorry left

Closed the original syntactic hole in
`AlgebraicGeometry.Scheme.ProjectionRestriction.localBaseData_exists` (1 of 1).
Its proof and the generic theorem
`AlgebraicGeometry.Scheme.ProjectionRestriction.ExactTensor.exactTensorComparison_exists`
are complete. There are no `sorry`s in the item or any of the four generic descent modules.

Added one hole:
`AlgebraicGeometry.Scheme.ProjectionRestriction.localOrdinaryResolving_exists`,
node `lem-weil-pbc-projection-local-ordinary-resolving`.
This is a decomposition, with one hole closed and one added, not a net hole reduction.
The remaining statement involves only ordinary module pullback and resolving complexes;
it contains none of the two restrictions, three derived tensor comparisons, their signed
shift structures, or the derived adjunction. The delivery proves all those additional
parts from the ordinary statement. No data-valued definition contains a hole.

The nine existing holes in the refactored consumer are unchanged (none closed or
added there), all in `AlgebraicGeometry.Scheme`:

- `sfCbcOrdinaryTensorComparison_existsUnique`
- `sfCbcTensorComparison_existsUnique`
- `sfCbcRestrictExtensionIso_existsUnique`
- `sfCbcFiniteTensorHom_isIso`
- `sfCbcCompletionModelIso_existsUnique`
- `sfCbcFiniteUnderlyingHom_transition`
- `sfCbcFiniteModelIso_existsUnique`
- `sfCbcCompletedReductionIso_evaluation`
- `sfCbcRealizationExtensionIso_existsUnique`

The two new construction modules contain no `sorry`. This delivery closes one
assigned hole and adds one strictly smaller hole; the consumer refactor changes
neither that count nor any pre-existing consumer hole.

## No longer needed

No original import of the item is removed and no module is withdrawn.
The private proof import of `AdicPullbackPresentationTransport` in
`CompletedStrictOpenExchange` is replaced by the actual required lower module
`AdicPullbackPresentationModels`; that consumer no longer needs the upper
transport node. The original upper module and all its declarations are retained,
since other DAG parents may still require its proof route.
In the unclaimed `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`, replaced
`public import Sheaf.Paper.RingedProjectionRestriction` by
`public import Sheaf.Paper.RingedProjectionRestrictionData`. The former imported the
higher theorem into its own lower exactness dependency and closed an import cycle
when the assigned proof began using that dependency. The data import provides all
names the exactness module uses. Its declarations are otherwise byte-for-byte
unchanged. The higher theorem remains in the library. Its downstream use search
found no uses through this import. Fifteen original direct importers compiled unchanged.
The other two had pre-existing file-level time-limit failures and are split as
described below, with the existing declarations, statements and proof bodies preserved.
The change record is `coord/changes/J4-localized-exactness-data-import.md`. The original planned direct
use of `lem-weil-pbc-ringed-slice-comparisons-shift` and its specialized package is
unnecessary: the proof descends the native ordinary restriction comparison through a
generic exact tensor functor instead. This does not claim that module is unused by the
rest of the library. The localized ringed-site and ringed-topos pullback results remain
sources for the ordinary lower step, rather than falsely being applied directly to the
entire `LocalBaseData` package. All blueprint unit statements and realized steps remain.

## Where the brief, the DAG or earlier work was wrong

Delivery's source-cycle check caught an existing upward public import in the generic
exactness library that single-file compilation against compiled artifacts did not
catch. This is repaired by the narrowed data import described above, without
changing any theorem statement or definition. Two direct consumers also exceeded the
file-time limit against the original sources. After profiling and local caching did
not resolve the cost, split their already-proved construction portions into
`AdicPullbackPresentationModels` and `SfCbcExtensionModel`. Their original main
theorems and mathematical proof routes remain in their original modules. The
combined sources retain exactly the old declaration sets and hole counts (0 and 9).
The change record is `coord/changes/J4-localized-exactness-consumer-split.md`. Of four
direct consumers of these modules, `CompletedStrictOpenExchange` also exceeded
the limit (66 s). Its proof import now names the lower construction module it
actually uses, and it respects its existing local irreducibility caches. It
compiled successfully in approximately 45 s. No public declaration, proof body,
definition body, public import or attribute in that consumer is changed. The
other three direct consumers compiled unchanged. The repaired extension-by-zero
module also compiled, and all 17 original consumers of the narrowed exactness
import have now passed (15 unchanged, two after the documented module split).
All unchanged validation copies were removed before delivery.

The original four proof dependencies do not directly return the records required by
`LocalBaseData`. In particular, the previously stated slice package uses a small-site
presentation and different tensor models, whereas these pro-etale sites have object
universe `u+1`, morphism universe `u`, and fixed native module tensors. Also the existing
projection tensor-shift theorem is presented for `Operation`; a restriction functor is
an exact module functor but is not directly such an operation. The generic proved
exact-functor argument handles this distinction without changing shared definitions,
universes, or the target statement.

## New nodes

`lem-weil-pbc-projection-exact-tensor-comparison` records the proved general descent
and its two-variable signed shift verification, in
`Sheaf.Paper.ProjectionExactTensorComparison`.

`lem-weil-pbc-projection-local-ordinary-resolving` records the remaining ordinary
localization step, with the coefficient section formula and pure-unit normalization,
in `Sheaf.Paper.ProjectionLocalOrdinaryResolving`. Its proof in words and sources are
in both its node and theorem docstring. The public-import change record is
`coord/changes/J4-localized-exactness-data-import.md`; existing declaration types
and bodies are preserved.

`lem-weil-pbc-projection-exact-tensor-core` records the proved cochain descent and
representative equation, in `Sheaf.Paper.ProjectionExactTensorCore`; the exact model
abbreviation lives with this theorem.

`lem-weil-pbc-projection-exact-tensor-shift-first` records the proved first-variable
shift verification in `Sheaf.Paper.ProjectionExactTensorFirstShift`.

`lem-weil-pbc-projection-exact-tensor-shift-second` records the proved second-variable
shift verification, including the total-complex sign, in
`Sheaf.Paper.ProjectionExactTensorSecondShift`. These three nodes have complete Lean
proofs; they do not add any holes.

A whole-blueprint search for tensor shifts and module localization found no blueprint
node equal to these generic normalized comparisons or the ordinary lower step.

`lem-cbc-adic-pullback-presentation-models` records the 18 existing public normalized
model declarations moved into `Sheaf.Paper.AdicPullbackPresentationModels`; the
original adic node retains its main theorem and remaining 14 declarations.

`lem-sf-cbc-extension-model` records the 43 existing public exact-extension model
declarations moved into `Sheaf.Paper.SfCbcExtensionModel`; the original completion
node retains its main theorem, all nine existing holes, and its remaining 45
declarations. These are source-file splits of complete constructions, with no
new mathematical statement or hole.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
