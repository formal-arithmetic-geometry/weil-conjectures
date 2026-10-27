## What changed

Reduced `WeilConjectures.wholeTowerIntegralPullbackComparison` to the existing
augmentation/counit, framework-family and common-stage-descent declarations,
plus three explicit fixed-component compatibility steps. The original structure,
instance and theorem signatures and all original public imports are unchanged.
No existing module besides the assigned item changes, and no definition changes.

The proof first obtains one realization system and its normalized finite data.
For each scheme isomorphism it obtains the actual framework stage family, forms
its mixed transformation and invokes `fdNormalizedPullbackDescent`.
The returned equality of finite data is used to transfer Roos matching. The unit,
composition, integral scalar and signed shift fields then use that same family.
The scalar-realization field is derived directly from
`fdScalarPullbackRealizationIdentification` after obtaining the two common
strict-tower models and unfolding the two restricted comparison definitions.
All remaining obligations are public named theorems in separate new modules.
Choices are scoped inside the proof of a proposition; no definition selects
data from an unproved existence theorem.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.wholeTowerIntegralPullbackComparison`
(node `lem-fd-whole-tower-integral-pullback-comparison`) by a compiling reduction.
This is a decomposition, not a claim of a sorry-free proof of the mathematical theorem.
The assigned item has zero remaining holes; the original hole count was one.

Added three holes, each the complete proof body `:= by sorry`:

- `WeilConjectures.fdNormalizedPullbackMixed`
  (`lem-fd-normalized-pullback-mixed`): retain the already selected normalized
  finite components in the mixed scalar transformation.
- `WeilConjectures.fdNormalizedPullbackGeometry`
  (`lem-fd-normalized-pullback-geometry`): transfer the actual unit, composition
  and signed shift formulas to the selected normalized family.
- `WeilConjectures.fdNormalizedPullbackIntegralScalar`
  (`lem-fd-normalized-pullback-integral-scalar`): transfer the integral scalar
  square to those same finite ambient components.

Thus one upper hole is closed and three lower holes are added, net minus two.
No other hole is closed, and no hole is moved into a definition or private helper.
The separate scalar-realization field and the common-stage assembly are actual
Lean proofs using the existing declared dependencies.

## No longer needed

The new statement-only modules also omit proof imports used only by their
natural-language plans: `FdCompletedCompositorNormalization`,
`FdPullbackSignedShiftWordTransport`, `FdScalarPullbackRealizationIdentification`
and `FdScalarRoosComparisonIntertwining`. Their nodes retain those proof
dependencies for the workers who prove the statements.

No mathematical module is claimed pruned. The six original proof dependencies
remain used, either directly or by the new fixed-component transfer lemmas.
The unit route is unchanged. Only obsolete direct proof imports in the assigned
item are removed; their mathematics remains under the declared dependency owners:

- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization`
- `Sheaf.TraceFormula.CounitRealizationSubstitution`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.CompletedPullbackAdjunction`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.SpecifiedPullbackComparisonAlpha`
- `Sheaf.Paper.KFlatScalarComparisonNormalization`
- `Sheaf.Paper.PbcScalarExtension`
- `Sheaf.Paper.ExactProductFunctorRoosDescent`
- `Sheaf.Paper.QuotientSystemMixedCoherence`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.CategoryTheory.Adjunction.Mates`

No source-library declaration or module is deleted. No existing target or
statement is weakened. The parent's old tool approvals are preserved; none is
silently replaced or added.

## Where the brief, the DAG or earlier work was wrong

The six-step DAG is a mathematical assembly plan, but its Lean declarations do
not yet identify all of their independently packaged comparison witnesses.
`fdPullbackAugmentationCounitMatching` supplies normalized finite data for one
realization system; `fdScalarRoosComparisonIntertwining` chooses pairwise finite
data from common strict-tower models, while the compositor and word-transport
results package further presentations. Their conclusions cannot simply be
assigned to the parent fields: one must identify them with the selected finite
components and form their compatible mixed transformation. The new lemmas make
precisely these missing transfers explicit, rather than selecting inconsistent
pairwise finite witnesses.

The newest blueprint trace definition now resides under
`sec-fourier-transform/sk-cor-plancherel/def-fd-trace-function.md` and states the
local-operator trace definition. The detailed auxiliary comparison argument is
preserved in the assigned node and its six existing dependencies. New lemma
sources explicitly refer to that auxiliary argument; no new claim is attributed
to the current blueprint text.

## New nodes

`lem-fd-normalized-pullback-mixed`, in `FdNormalizedPullbackMixed.lean`, is only
the compatible-transformation step for fixed finite comparisons and an already
given framework family. It does not construct a realization system, finite
data, pair descent or geometric coherence. It uses the common strict-tower,
augmentation and rational scalar-intertwining statements.

`lem-fd-normalized-pullback-geometry`, in `FdNormalizedPullbackGeometry.lean`,
is only unit/composition/shift compatibility for a given normalized family.
It does not construct that family or assert scalar realization or scalar squares.
It uses augmentation matching, actual compositor normalization and signed word
transport. Its proof-in-words cancels only complete-input augmentations.

`lem-fd-normalized-pullback-integral-scalar`, in
`FdNormalizedPullbackIntegralScalar.lean`, is only the integral scalar square for
a given normalized family, with the actual PBC alpha retained by HEq. It uses
common models, augmentation matching, scalar realization and scalar/Roos
intertwining. Repeated fields, identity schemes, zero objects, arbitrary signed
shifts and ramified extensions were checked in the proof descriptions; no
quotient map is inverted and no finite Tor-amplitude premise is added.

Each node carries its exact Lean statement, source, natural-language proof,
existing proof dependencies and the Mathlib/blueprint searches. No change record
is needed: no pre-existing definition, statement or public import was changed.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
