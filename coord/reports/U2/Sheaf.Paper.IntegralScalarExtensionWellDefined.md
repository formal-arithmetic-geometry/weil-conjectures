## What changed

Repaired return C-adc97682f by adding all five missing consumers to the change
record's `## Users`, with their current claim holders and the effect on each
consumer's mathematical definitions and statements. A fresh declaration-name
scan of both library roots found exactly these five missing users; every current
textual consumer is now recorded. The retained complete proof and node route
are preserved. The retained proof was rebuilt in a clean diagnostic overlay with profiling
enabled only in that scratch copy. An importing axiom probe confirmed that both
completed theorems use exactly `propext`, `Classical.choice` and `Quot.sound`.
The earlier validation request stopped at a 60-second timeout, and the first
profiling request received no server answer; the successful rebuild and probe
supersede those attempts. Consumer checks use the freshly rebuilt artifact. All five consumers named
in the return compiled unchanged: `ClopenRoosIntegralDescent` (24.3 s),
`ConstantScalarStrictUnit` (9.6 s), `ConstantScalarUnitQuasiIsomorphism` (8.9 s),
`IsomorphismScalarTensorKFlatModel` (9.5 s), and
`CompletedCoefficientFreeResolution` (6.2 s). No consumer adaptation is needed.
The retained older consumer artifacts were archived within the scratchpad, so
final delivery validation also starts with a clean overlay. The node metadata
was refreshed from current main, preserving independent maintainer approvals
and all fields outside this delivery's proof and Lean attachments.

Repaired return C-07128 by rebasing the retained packet on the current
`sheaf-dag` head. The landing failure was environmental: the independent
reader attempted to open `lean/Sheaf/AlgebraicGeometry/EllAdicLocalizingExceptionalConstructible.lean`,
which is currently recorded in `coord/rework.tsv` at its quarantine path.
The item source and proof are unchanged; this retry is compiled against the
current branch and is delivered again so the landing checker uses the current
quarantine-aware source set.

Reconciled return C-20907 (delivery head `209070cd62`) with current `sheaf-dag`.
The return reports a landing failure after independent review had passed, rather
than a proof defect. `Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators`
is absent from `lean/` because it is quarantined by `coord/rework.tsv`, with its
restoration currently assigned to B3. Its archive, node and dependencies are
preserved. The current downstream-user checker skips absent source files.
The retained Lean proof and node route require no source changes against the
current repository. A fresh server artifact build compiled the complete module
without diagnostics in 41.4 seconds. The delivery tool rebuilds this packet on
current `sheaf-dag` and runs the server preflight before pushing.

Repaired return C-05da8 (delivery head `05da881557`): added every named missing
consumer to the change record's `## Users`, with its current claim holder and
the effect on its definitions and normalization statements. A current declaration-use
scan also found `Sheaf.Paper.SfIntegralConstructibleLinear`, which is now recorded.
The retained proof and node route are preserved. The delivery tool recreates the
commit on current `sheaf-dag`; the repaired module compiled on the server in 46.5 seconds.
A fresh artifact-producing build and importing probe verified the two completed
theorems and four concrete-construction/API declarations use only `propext`,
`Classical.choice` and `Quot.sound`. Validation uses a clean overlay containing
this repaired artifact, without the retained sandbox's older consumer artifacts.

Six additional consumers compiled unchanged against that clean overlay:
`ConstantCoefficientScalarNormalization` (6.1 s),
`IntegralCompactSupportCoefficientComparison` (21.8 s),
`IntegralComparisonRealizationModels` (36.2 s), `PointCompletedEvaluation` (22.8 s),
`ScalarExtensionTowerCoherence` (47.6 s), and `SfIntegralConstructibleLinear` (3.3 s).
`FdCoefficientComparison` fails against both the published baseline and the clean
repaired overlay with identical diagnostics: missing additive/preserves-zero
instances at lines 195 and 199, followed by missing fields/constants at lines
212, 275 and 304. Its source is untouched, and no adaptation is forced by this
repair. The preliminary checks using the retained consumer artifacts are
superseded by these clean-overlay results. A source scan of all changed
declaration names finds no unlisted users. All table claim holders were refreshed.
No consumer source adaptation is delivered.

Completed `WeilConjectures.integralScalarTransition_existsUnique` and
`WeilConjectures.integralScalarExtensionWellDefined` in
`Sheaf.Paper.IntegralScalarExtensionWellDefined` without changing their statements
or the mathematical type of any existing public declaration. The tower and Roos functors
receive explicit annotations for their previously inferred source and target types.
The concrete ordinary tensor functor, its proved additive instance, its canonical
equality and comparison isomorphism expose the construction behind the ordinary
functor. The ordinary module-level functor and its additive instance name extension
followed by restriction. All remaining helper constructions and lemmas are private.
The implementation of ordinary scalar extension and its tensor sections is repaired as
described below; its additive instance is proved for this concrete implementation.

The transition is the sheafified balanced tensor map, restricted along the target
completion projection. Its generator formula determines it uniquely. Naturality
and uniqueness are checked using the tensor-section extensionality API.

For well-definedness, ordinary coefficient change preserves quasi-isomorphisms
between good complexes, and exact restriction preserves them after restriction.
Exact countable products and the distinguished mapping-cone triangle give Roos
quasi-isomorphism invariance and the derived-limit property. A comparison with a
termwise module-product functor proves additivity and coherent compatibility
with every integer shift, including the zero and addition coherence equations.
The existing proved localization lemma in `IntegralOperationsWellDefined`
presents the good-complex inclusion followed by Q as a localization. The localization lift supplies the functor, comparison,
additivity, coherent shifts and uniqueness. Tensor balancing verifies the actual
constant-section action; fully faithful precomposition then gives scalar
linearity on the derived categories. Model comparisons and their derived-limit
properties transport along the supplied isomorphism from a good model.

The proof reuses the proved localization, exact restriction, Roos invariance,
derived-limit and cone-map lemmas in `IntegralOperationsWellDefined` through a
private `import all`. It imports the tensor-colimit API and generic localization
and coherent-shift APIs for the remaining scalar-specific construction.
The node's proof and proof dependencies now describe this route.

The existing constant-section and chain-action proofs now share a generic
sectionwise limit-extensionality lemma and the private module scalar action.
Named ordinary-level and localization constructions, explicit tower and Roos types,
and an explicit equality-transport formula avoid repeated expansion of completed
coefficient limits and cone constructions. The module-product and complex-product
functors have projection and comparison lemmas. The coherent-shift and additive
instances use the existing localization definition's selected presentation.
The concrete ordinary functor retains the original commutative coefficient
presentation in its category and preadditive instances. Private scalar-action
helpers use the completed-ring view explicitly. Named functor-level equalities
identify the selected localization compositions before checking inversion and
scalar compatibility, avoiding repeated comparison at concrete Roos objects.
A private parametric linearity lemma checks the localization argument before
substituting the concrete descended functor. The derived scalar action chooses
the unique transformation equal to the canonical fully faithful preimage; its
proved equality and component API preserve exactly the original action while
preventing repeated expansion of that preimage.

The definition repair in `coord/changes/u2-integral-scalar-canonical-reduction.md`
replaces the large witness-based selection by a functor uniquely fixed by explicit
sectionwise extension followed by sheafification. Its objects and maps are exactly those prescribed by
the retained witness. Tensor sections transport the literal sheafified pure tensors through the proved
canonical comparison. The ordinary functor chooses the unique value equal to the
explicit construction; this small interface avoids expanding coefficient limits
throughout its consumers. The level functor composes extension
with restriction before prolonging to complexes; the two orders have identical
objects and maps. This avoids repeated expansion of the
derived-change-of-rings existence statement. Target definitions require the
normal independent statement review; the mathematical notion and all target
signatures remain unchanged.

The complete module compiled in an artifact-producing build (35.3 seconds), and
an importing probe verified that both completed theorems use only `propext`,
`Classical.choice` and `Quot.sound`. The four new concrete-construction and
comparison declarations have the same permitted axiom set.

In the previous delivery validation, twelve consumer modules compiled unchanged
against the repaired artifact, including all eight direct importers found then,
both shift modules, the
coefficient reduction model and the intrinsic constructible-linearity interface.
`CompletedScalarChainShift` compiled in 38.0 seconds and `CompletedScalarShift`
in 31.0 seconds. The change record identifies every checked module and records
the current claim holders. No consumer source adaptation is delivered.
The delivery command runs the required compile and preflight checks.

## Proved and sorry left

Closed two holes:

- `WeilConjectures.integralScalarTransition_existsUnique`
  (`lem-weil-integral-scalar-extension-well-defined`).
- `WeilConjectures.integralScalarExtensionWellDefined`
  (`lem-weil-integral-scalar-extension-well-defined`).

Added zero holes. No `sorry` remains in the delivered module; no new modules or
statements with postponed proofs are delivered. The proof uses existing stated
library dependencies as permitted by stage 3.

## No longer needed

Removed these private imports:

- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`: the finite coefficient-change
  general coefficient-change invariance theorem supplies the assertion in independent universes.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`: direct good-complex
  localization from functorial flat resolutions replaces this presentation.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`: the
  independent-universe tensor-descent theorem is also unnecessary. The specific
  tensor-colimit facts used are imported from their defining module instead.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: its direct
  import is redundant with the retained statement dependencies.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: its direct import is
  redundant with the retained independent-universe K-flat-resolution API.

Removed `lem-weil-pbc-site-derived-tensor-descent` from this node's proof route
and tool-use list: the functorial-resolution criterion proves the localization
presentation directly. Removed `lem-weil-derived-limit-levelwise-iso` from the
proof route and tool-use list: the explicit diagonal cone map and Mathlib's
triangle isomorphism criterion (`lem-sf-triangle-morphism-iso`) suffice.

The pro-etale site node `def-weil-pbc-proetale-site` remains a statement
dependency; it is removed only from the proof-step dependency list because the
revised argument introduces no separate proof obligation for the site.

Against the current repository DAG, the retained direct-localization and
termwise-product/cone proof also does not use the following planned dependencies:

- `def-weil-strict-roos-model` (`Sheaf.CategoryTheory.StrictRoosModel`),
  `lem-weil-strict-roos-comparison` (`Sheaf.CategoryTheory.StrictRoosComparison`),
  and `lem-weil-roos-comm-shift` (`Sheaf.Algebra.Homology.RoosCommShift`): the
  proved private product and cone comparisons provide the required structure.
- `lem-pur-compatible-coefficient-tower` (`Sheaf.Paper.CompatibleCoefficientTower`):
  the transition is constructed directly from the balanced tensor formula.
- `lem-pur-strict-roos-homotopy-functor`
  (`Sheaf.CategoryTheory.StrictRoosHomotopyFunctor`) and
  `lem-weil-pbc-ringed-strict-tower-homotopy-limit`
  (`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`):
  direct localization of good complexes avoids a separate homotopy presentation.
- `lem-pur-additive-localization-descent`
  (`Sheaf.CategoryTheory.AdditiveLocalizationDescent`): the private descent proof
  uses essential surjectivity and binary products directly.
- `lem-pur-linear-localization-lift`: the actual scalar natural transformations
  descend by fully faithful precomposition, with no separately chosen linear action.
- `lem-weil-tower-category-levelwise-abelian`: no separate tower-abelian argument
  is needed; products and cone maps are checked in the target module category.

The refreshed node keeps independently added maintainer tool approvals in their
original order. These approvals do not introduce new proof-dependency edges.

These are reductions of this item's direct dependencies, not requests to delete
source-library declarations or claims that their modules have no other users.
Removed the direct imports
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence` and
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`: their applications
are supplied by the existing proved integral-operation lemmas. Local duplicate
proofs of localization, exact restriction, Roos invariance, the derived-limit
property and the cone-map comparison were removed for the same reason.

No unit statement or realized proof step is bypassed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The consumer table in delivery adc97682f omitted five current users. This retry
repairs that record rather than repeating an unchanged delivery.

Return C-20907 was caused by the landing checker trying to read a quarantined
downstream source at its former library path. It did not identify a mathematical
or Lean error in this item; the current checker guards against absent files.

The previous change record's user list was stale: it omitted the six consumers
identified in return C-05da8. They and one additional current scalar-action user
are now included, with their semantic checks and compiler outcomes recorded.

The statements remain unchanged. The original ordinary-functor implementation
made elaboration expand a large existence witness and dependent transports; the
concrete sectionwise construction preserves the specified object and map formulas.

The DAG's intermediate homotopy-subcategory
presentation is unnecessary: the existing integral-operation localization lemma,
proved using a functorial flat resolution, already handles good complexes directly. The proof therefore does
not need the separate homotopy-descent calculation in its old step 4.

The conclusion asks for `CommShift ℤ`, so a comparison only for shift by one is
insufficient by itself. The proof constructs comparisons for all integers and
checks the zero and addition coherence equations on both cone summands.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
