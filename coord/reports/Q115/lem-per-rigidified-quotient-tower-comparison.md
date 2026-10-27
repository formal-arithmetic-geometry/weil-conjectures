## Worker report

Repair of L's return of immutable head 65adc5229759 (H1/H2/H11).
This is a stage-2 statement delivery, not a re-push of the stage-1 split.
The sandbox initially contained only dispatcher marker files. The node copies here were
read afresh from the live repository, including Q17's corrected statement and seven proof
steps. No git command or direct write was made in the read-only repository.

The module `Sheaf.AlgebraicGeometry.RigidifiedQuotientTowerComparison` states
`AlgebraicGeometry.rigidifiedQuotient_tower_comparison`, with proof `by sorry`.
Its helper structures spell out the objects and every clause of the conclusion; they
are data/predicates, not assumed conclusions of the theorem. All eight declarations
are listed in `lean.declarations`. The docstring reproduces all seven live proof steps,
including their dependency IDs and source places, from ILO VIII 5.4.2, 5.4.4--5.4.5
and 5.3.10--5.3.11. The whole source passage was read in the local ILO PDF, including
5.3.4's distinction between normal-crossings and strict rigidifications.

Only `lean` and the permitted added statement dependencies change on the item.
`statement`, `proof`, `proof_deps`, `mathlib_searches`, `split_report` and all remaining
fields are preserved as live. In particular there is no new statement correction and
no new STATEMENT-DISPUTED flag. The extra statement dependencies are the already
recorded `def-trf-strict-etale-log-blowup-procedure` and
`def-per-gabber-modification-data`, whose existing notions the signature helpers use.

The exact hypothesis/clause correspondence is as follows (names below are in
`AlgebraicGeometry.RigidifiedQuotient` unless qualified):

| Live node clause | Lean rendering |
| --- | --- |
| One fixed smooth-functorial saturated fan resolution | The theorem's `R : FineFan.SmoothFunctorialDesingularization.{u}`. This is the recorded fan-resolution structure, not an arbitrary sequence of maps. |
| Fixed monoidal resolution rule induced by that resolution | `P : StrictEtaleLogBlowupProcedure IsLogBlowupInput` and `hP : IsFanInduced R P`. `IsFanInduced` requires, on every fan chart, an actual `LogFanTower` of `R.resolution F`, the original chart at level zero, and its contraction comparison over the log identity to the assigned tower. `liftedTower` merely packages those existing levels, arrows and pulled centers with real data. The procedure already carries its descent-compatible strict-etale comparisons. |
| Schemes X and Y, Noetherian, regular and separated | Each `Pair G` has `logScheme`, `noetherian : IsNoetherian ...`, `regular : IsRegularScheme ...` and `separated : ...IsSeparated`. The FS object already includes its locally Noetherian proof. Apply the universally quantified system to two such pairs. |
| Finite groups G,H and their actions | `G : Type v` with `[Group G] [Finite G]`, and `Pair.action : FSLogGroupAction G logScheme`. Every log-map action law and every geometric stabilizer test is the recorded one. |
| Tame and generically free | `Pair.tame` and `Pair.genericallyFree` use `FSLogGroupAction.IsTame` and `.IsGenericallyFree`. Very tameness separately uses its own recorded predicate, as the node requests. |
| Admissible actions | `Pair.admissible` gives, for every x, an affine open containing x invariant under every g. Thus invariant affine opens cover, with no affine or quasi-projective restriction on the scheme itself. |
| Abelian geometric inertia | `Pair.abelianInertia : GabberModification.AbelianInertia action`. Its quantifiers are all algebraically closed fields, geometric points, and pairs of inertia elements. |
| Preserved G-strict/H-strict SNC boundaries | `Pair.boundary`, `snc : IsStrictNormalCrossingsBoundary boundary`, `groupStrict : GabberModification.GStrict action.baseAction boundary`, and `boundaryInvariant`. `GStrict` is the existing equal-or-disjoint condition on irreducible components. |
| Free outside these boundaries | `Pair.freeOutside : GabberModification.FreeOpen action boundary.support.compl`, using the recorded geometric-point freeness condition and invariance. |
| Invariant enlarged boundaries containing the old ones | `Pair.enlargedBoundary`, `contains : boundary.support ≤ enlargedBoundary.support`, and `enlargedInvariant`. Since both boundary structures are reduced, inclusion of supports expresses the stated inclusion. |
| NC means etale-locally SNC (Stacks 0BI9), not globally SNC | `Pair.normalCrossings` quantifies over every x and supplies an etale W -> X with a point w over x and `IsStrictNormalCrossingsBoundary (enlargedBoundary.comap e)`. It makes no global component-labeling assumption on the enlarged boundary. |
| The enlarged log structures are the divisorial fs structures | `logScheme` is fs and `Pair.divisorial` is an actual isomorphism of its log presheaf with the recorded `divisorialLogPresheaf` of the boundary complement, commuting with `divisorialStructuralMap` and `alpha`. Merely having the same characteristic-triviality locus is not substituted. |
| Very tame enlarged log actions | `Pair.veryTame : action.IsVeryTame`, directly using `FSLogGroupAction.IsVeryTame`, including the characteristic and strict-local-stratum tests. |
| lambda and phi equivariant and inducing inertia isomorphisms | `Hom.groupMap : H →* G`, `Hom.logMap`, and `Hom.inert : GabberModification.Inert ...`. `Inert` includes equality of the actual equivariant log composites, and surjectivity and injectivity on the actual geometric stabilizers via this group map. |
| Reduced boundary inverse images | `Hom.boundary` and `Hom.enlargedBoundary` equate the source ideals with `.radical` of the target ideals' `.comap` along `logMap.base`. Neither equality is silently replaced by scheme-theoretic inverse image. |
| Explicit strictness of (Y,enlarged B_Y) -> (X,enlarged B_X) | `Hom.strict : logMap.IsStrict`. This is the recorded canonical characteristic-map criterion with `CharacteristicRelation`, independent of the boundary equalities. This is precisely the hypothesis added by live Q17, and it is not dropped. |
| Invariant rigidified log quotients | `Construction.quotient`, `quotientMap`, `invariantQuotient : X.action.IsQuotient quotientMap`. The last field is the recorded orbit/categorical/affine-invariant/log-invariant quotient predicate, not an arbitrary quotient-like map. The theorem supplies these constructions for every input pair. |
| Resolve these quotients by the same rule | `Construction.input` and the actual tower `P.tower quotient input` in `Construction.pullback`. P is chosen once, before either pair or quotient. |
| Pull the quotient tower back in fs log schemes | `Construction.tower` and `.pullback : LogBlowupComparison quotientMap (P.tower ...) tower`. Its recorded fields give recursive fs Cartesian squares and equality of actual pulled log centers. `fullPullback : Function.Bijective pullback.count` retains all quotient stages on this pullback, not an extra contraction along the quotient cover. |
| Underlying normalized blowup towers with ordered ideal centers | `Construction.center` is an actual `IdealSheafData` at each ordered stage. `normalized` uses the existing `Monoscheme.IsNormalizedBlowup` of precisely that ideal and arrow. `algebraized` identifies each center in geometric strict local rings with the span of the structural images of the actual pulled log ideal. |
| Induced quotient morphism and its strictness | `Comparison.quotientMap`, `quotientSquare : B.quotientMap.Square quotientMap f.logMap A.quotientMap`, and `quotientStrict`. The square is equality on all relative log sections as well as scheme maps, so it specifies the induced quotient morphism. |
| Tower on Y is contracted pullback of tower on X | `Comparison.logComparison`, using the existing `LogBlowupComparison` with its monotone `count`, ordered embedding `retained`, endpoints, kept steps, deleted identity steps, and fs pullback squares. `schemeCartesian` asserts the ordinary scheme pullback squares, without assuming phi flat or smooth. |
| Actual ordered scheme ideal centers preserved | `Comparison.centers` identifies each source center with the extension of the target center at the retained index. The corresponding log-center equality is also retained by `logComparison.centers`. |
| Delete precisely unit-center stages | `Comparison.unitCenter` is the iff between absence from `retained` and the extended scheme ideal being top. `logComparison.whole` is the corresponding iff for the log ideal. Thus consecutive unit stages are deleted and no proper principal center is removed merely because its blowup is an isomorphism. |
| Scheme pullback equals the strict-transform tower | `Comparison.strictTransform` says the canonical `strictTransformι` into the ordinary fibre product is an isomorphism at every step, for the complement of the actual center. Combined with `schemeCartesian`, this is an equality via the canonical inclusion, not an unnormalized abstract scheme isomorphism. |
| Canonical identity and composition laws | `ComparisonSystem.identity` gives identity on induced quotient maps, all contraction indices and all relative log maps. `.composition` equates the quotient composite, composed index maps, and actual composite relative log maps to the direct comparison. HEq only transports explicitly differing finite-index types. |
| Localizations, strict localizations, completions | `ComparisonSystem.comparison` quantifies over every strict inert map in `Hom`, with no finite-type/flatness/excellence hypothesis. It therefore applies to those maps equipped with the induced strict divisorial charts and the corresponding stabilizer homomorphism, whenever they are in the indicated class, exactly as the final sentence of the live node specifies. The docstring's step 7 explains the Noetherian regularity permanence used to apply the universal assertion. It does not assert strictness for an arbitrary unrelated log structure on a completion. |
| Finite disjoint unions | `Pair` imposes no connectedness or integrality, and all fields are componentwise; the universal comparison applies to strict component inclusions, including the associated group/stabilizer maps. The same fixed R and P are used for every component, and the identity/composition equations are global. |

Dependency declarations were read with their signatures and docstrings, not just names:

| Original statement dependency | Recorded module and declarations used |
| --- | --- |
| lem-trf-functorial-fan-desingularization | `Sheaf.AlgebraicGeometry.FunctorialFanDesingularization`, `FineFan.exists_smoothFunctorialDesingularization`; its public statement provider `FineFanBlowup` defines the actual `FineFan.SmoothFunctorialDesingularization` used by the theorem. |
| lem-trf-log-fan-chart-blowup | `Sheaf.AlgebraicGeometry.LogFanChartBlowup`, `log_fan_chart_blowup`, `LogFanChart`, `LogFanTower`, `EtaleLogHom.Square`, `EtaleLogHom.IsFSPullback`. |
| lem-trf-functorial-log-blowup-etale-descent | `Sheaf.AlgebraicGeometry.FunctorialLogBlowupEtaleDescent`, `functorial_log_blowup_etale_descent`; its public procedure provider supplies `IsLogBlowupInput`, `LogBlowupTowerOver`, `LogBlowupComparison` and `StrictEtaleLogBlowupProcedure`. |
| def-weil-regular-scheme | `Sheaf.AlgebraicGeometry.IsRegularScheme`, `IsRegularScheme`, explicitly local-Noetherian plus regular, not merely the stalk regularity class. |
| pqf-def-locnoeth | `Mathlib.AlgebraicGeometry.Noetherian`, `IsLocallyNoetherian`, affine-cover equivalences and `IsNoetherian`. No duplicate Noetherian predicate. |
| def-trf-strict-normal-crossings-boundary | `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`, `IsStrictNormalCrossingsBoundary`, including radical Cartier ideal and regular intersections of the correct codimension. |
| def-trf-fs-log-blowup | `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`, `FineSaturatedLogScheme`, `EtaleLogHom`, `.CompEq`, `SaturatedLogBlowupTower`, log ideals and geometric strict-local algebraization maps. |
| def-per-strict-log-morphism | `Sheaf.AlgebraicGeometry.FSStrictLogMorphism`, `EtaleLogHom.IsStrict`, `.CharacteristicRelation`, `.IsIdentity`, reused through the recorded provider. |
| def-per-very-tame-fs-log-action | `Sheaf.AlgebraicGeometry.VeryTameFSLogAction`, `FSLogGroupAction.IsVeryTame`. |
| def-per-fs-log-group-action | `Sheaf.AlgebraicGeometry.FSLogGroupAction`, `FSLogGroupAction`, `.IsTame`, `.IsGenericallyFree`, `.IsQuotient`; the actual invariant section construction is unchanged. |

Additional existing notions are reused, never redefined: `GabberModification.GStrict`,
`.AbelianInertia`, `.FreeOpen` and `.Inert` from `GabberModificationData`;
`divisorialLogPresheaf` and `divisorialStructuralMap` from `LogRegularPair`;
`Monoscheme.IsNormalizedBlowup` from `MonoschemeToricRealization`; and
`strictTransformι` from `WeilConjectures.Compactification.StrictTransform`.
In particular the existing `GabberModification.Rigidification` was NOT used as
an input: its global SNC requirement would improperly restrict the enlarged NC boundary,
and its fourth-stage input would add quasi-excellence. The item-specific Pair/Hom records
only bundle the corrected node's hypotheses; Construction/Comparison/System bundle its
prescribed constructions and conclusions with their canonical normalization conditions.
They introduce no independent replacement blowup, quotient or log structure.

Searches for an existing whole statement:

- `msearch.py`, LeanFinder: "Strict inert equivariant maps of very tame log schemes induce
  strict quotient maps and contracted normalized resolution tower pullback". Eight hits,
  all ordinary normalization maps/comparison lemmas, led by `Scheme.Hom.normalizationDiagramMap`;
  none gives the logarithmic quotient comparison or ordered contracted towers.
- `msearch.py`, Loogle: `"blowup", "normalization"`. Zero hits.
- `msearch.py`, Mathlib grep in AlgebraicGeometry:
  `log[Bb]low|[Vv]ery[Tt]ame|rigidified`. Zero hits.
- Direct `rg` in `lean/WeilConjectures` for the node ID and rigidified/log/inertia tower
  notions: no matching whole statement. Direct `rg` in `lean/Sheaf` found and reused the
  Gabber modification data, log procedure, fan tower, and normalized blowup notions above.
- `tools/blueprint_refs.py search 'rigidified quotient'` found zero blueprint nodes with
  that phrase. The ancestor command names `lem-per-artin-gabber-affine-curve`.
  DAG searches for G-strictness, invariant affine covers, normalized towers and divisorial
  structures identified existing dependencies rather than new independent definition nodes.

Edge cases checked against the unfolded fields before finalizing the statement:

- Length-zero towers use `Fin (n+1)` for levels and `Fin n` for stages. No artificial first
  center exists; center/strict-transform/deletion conditions are empty at n=0.
- Empty schemes and the empty divisor are allowed. The NC etale-neighborhood condition and
  geometric-point tests are vacuous on the empty scheme; SNC already allows empty components.
  A contracted tower over an empty component can have length zero.
- Disconnected regular schemes are allowed; no `IsIntegral` hypothesis slipped into Pair.
  Normalized blowups use the existing componentwise construction.
- The trivial group is allowed. Tameness is invertibility of geometric inertia order,
  and no condition says the total group order is invertible in every residue field.
- Proper principal centers, including isomorphism blowups, fail the unit-center test and
  are retained. Consecutive unit centers are handled by the existing monotone count and
  retained embedding. Both scheme and log versions of the unit test are explicit.
- Equality of reduced boundary supports alone does not imply strictness (a ramified map
  t -> t^n is the relevant warning example). `Hom.strict` is a separate indispensable field.
- No smoothness, flatness, finite type or excellence is imposed on Hom, so localization
  and completion applications are not lost. Tameness covers characteristic zero as well
  as prime-to-residue-characteristic inertia. `u` and `v` are explicitly bound; all field
  and geometric-point quantifiers use the scheme's universe u, and groups have independent v.
- The construction cannot choose unrelated log data: divisorial isomorphisms commute with
  alpha, quotient maps satisfy the exact recorded invariant-sheaf quotient, log pullbacks
  satisfy saturated universal properties, and scheme centers satisfy stalk-span equations.

## Dependency modules

`lem-trf-functorial-fan-desingularization`: the recorded file was legacy non-module.
The first required module-mode probe failed with "cannot import non-`module`
Sheaf.AlgebraicGeometry.FunctorialFanDesingularization from `module`". Its owning module
is delivered with `module`, a public import of `FineFanBlowup` and an exposed public
section. The theorem signature, sorry proof and complete proof docstring are unchanged.
Module-compatible proof import `MonoschemeToricRealization` is kept. The legacy proof
providers SmoothFunctorialNormalizedToricDesingularization, ToricMonoidComparison and
SharpeningFanBijection cannot be imported from module mode and are omitted, not rewritten.
Only this dependency node's `lean` record changes, with an explanatory note.

`def-trf-strict-etale-log-blowup-procedure`: its recorded provider was also legacy
non-module, preventing the descent dependency and GabberModificationData from being
used by the statement. The complete file is delivered with module header, public import
and exposed public section. Every one of its seven definitions/structures, all mathematical
signatures, fields, bodies, identity/composition laws, and docstrings are unchanged.
Only its node's `lean` changes, with `lean.note`. It is added as an explicit item dependency.

`lem-trf-functorial-log-blowup-etale-descent`: the recorded theorem's provider was
legacy non-module as well. The complete original signature, sorry proof and ten-step
proof docstring are preserved. Module mode, public import of the repaired procedure
provider, and exposed public section make the exact theorem usable. Existing module-mode
proof imports are retained; legacy proof-only imports FiniteCoproductLfpQcqs,
SetSheafCoverDescent and the legacy EtaleOver wrapper are omitted. Only its `lean` changes,
with an explanation. No strict-arbitrary-base-change conclusion was smuggled into this
strict-etale dependency: that conclusion remains the new item's theorem.

Some recorded proof-dependency modules have no current source even through
`scompile.py --source`: VeryTameLogQuotient, RegularBoundaryDivisorialChart and
FiniteQuotientStrictLocalInvariants returned "Module source unavailable"; an attempted
proof-only import of the last failed for a missing object file. They are not used in the
statement, and the final module does not import unavailable files. The same applies to
VeryTameEquivariantSharpChart and VeryTameLocalKummerQuotient. Their proof steps and IDs
remain in the theorem docstring and live DAG. The available module-mode proof providers
CoherentLogIdealChartConstruction, LogRegularDivisorialStructure, the two upstream
strict-henselization modules and CompletionRegularLocal are imported privately.
LogBlowupNormalization is currently legacy non-module, so its import is likewise omitted.
The genuinely unstated proof nodes GabberLogBlowupRegularization,
LogTowerContractionDescent and KummerBoundaryRestriction remain proof dependencies;
this stage-2 delivery does not assume their conclusions in the signature.

## Second reading by Q115

This is a second pass by the dispatched worker; no second agent was started, as the
human's brief prohibits that. The maintainer's independent immutable-head review remains
the independent review. I reopened the live corrected node, all delivered Lean files and
the recorded dependency declarations for this pass.

The main statement is not merely quotient strictness: opening `ComparisonSystem` then
`Comparison` exposes the contracted comparison, its ordinary Cartesian squares, equality
of actual scheme centers, exact unit-center deletion and canonical strict-transform
inclusion. Opening `Construction` exposes the actual invariant log quotient, fixed P
resolution and full fs pullback, and the stalk algebraization of every normalized center.
The `identity` and `composition` fields compare actual log maps, not only schemes or lengths.
The clause table above records every input and conclusion found in this reading.

Specific mismatches caught and repaired before delivery:

1. The returned snapshot had no stage-2 module or lean record. A new module and complete
   record now provide the live corrected statement, rather than editing stage-1 searches.
2. A generic existing rigidification interface would require the enlarged boundary to be
   globally SNC and its fourth-stage input would add excellence. The delivered Pair instead
   uses exactly the live etale-local SNC definition of NC and imposes no excellence.
3. A support-only boundary comparison would lose the Q17 correction. `Hom.strict` explicitly
   uses the recorded strict log-map predicate, separately from both radical inverse images.
4. Merely writing an fs pullback comparison would omit the scheme claim. `schemeCartesian`
   and the canonical `strictTransformι` isomorphism are both explicit conclusion fields.
5. Deleting every isomorphism blowup would delete proper principal centers. The iff in
   `unitCenter` uses only the actual extended ideal being top, preserving those stages.
6. Unspecified resolutions or maps would be hollow. `IsFanInduced` fixes the chart lift of
   the one fan rule; the quotient square, fs universal squares, normalized blowup property,
   and stalk-span condition prescribe the actual constructions up to their canonical maps.
7. Three legacy module barriers were found by a module-mode compile and repaired in the
   owning dependency modules, without changing their mathematical statements or data.
8. A raw topological open complement could not resolve `.ι` at the divisorial isomorphism.
   It now explicitly uses `Scheme.Opens.ι (X := logScheme.scheme)`; no mathematical change.

All theorem proofs introduced or retained by this packet are `sorry`: the main theorem,
the fan existence theorem and the etale descent theorem. The helper definitions contain
real data and no sorry. Four files compiled cleanly through scompile.py in dependency
order; no local/global build, no independent interactive compiler, no upstream edits.
The dry-run and final delivery results are recorded after they are run below.

Validation: `deliver2.py Q115 lem-per-rigidified-quotient-tower-comparison --no-push`
returned `OK (dry run): commit 31c6be20b01 passes the preflight and compiles; nothing pushed`.
All four files pass the server's per-file compile, including the complete seven-step docstring.
The JSON comparison confirms that the item differs only in `lean` and added `stmt_deps`,
and each of the three dependency node copies differs only in `lean`. All Lean lines are
at most 100 characters. Final publication uses the same prescribed deliver2.py wrapper.
