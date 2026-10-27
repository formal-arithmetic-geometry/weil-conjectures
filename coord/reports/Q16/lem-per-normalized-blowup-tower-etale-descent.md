## Worker report

This stage-2 delivery states `lem-per-normalized-blowup-tower-etale-descent` in
`Sheaf.AlgebraicGeometry.NormalizedBlowupTowerEtaleDescent`, using six named theorems, all
with `sorry` proofs and the node's step-by-step natural-language argument in their
source docstrings. There is no statement correction. The accepted Q43 stage-1 split,
its ten proof steps, and all proof dependencies are preserved. The inherited BLOCKED
ending concerned stage-1 resplitting; brief-stage2 §0 explicitly permits this stage-2
statement delivery. The queue names this as stage 2 and the node has no previous Lean record.

The underlying normalized blowup and finite tower are already published. In particular,
`AlgebraicGeometry.Monoscheme.NormalizedTower n` has levels indexed by `Fin (n + 1)`, an
actual ideal at each `Fin n` stage, adjacent arrows, reduced levels, and a proof that each
arrow is the specified componentwise-normalized ordinary blowup of that ideal.
`IsNormalizedBlowup` includes finite generation of each ideal on every affine open.
On the Noetherian stages here this is precisely coherence, equivalently the recorded
quasi-coherent finite-type notion of `pqf-def-coherent`. No ideal, normalization,
blowup, or tower construction is redefined. The new definition node packages only the
missing center-preserving comparisons, descent data, and actions on these existing towers.

Clause and hypothesis correspondence (names below are in namespace
`AlgebraicGeometry.Monoscheme.NormalizedTower`):

- The base is Noetherian: `[IsNoetherian X]` in `normalizedBlowupTower_etaleDescent`, or
  `[IsNoetherian (T.level 0)]` in `normalizedBlowupTower_geometry` and the étale-pullback
  clause. Mathlib's class includes local Noetherianity and quasi-compactness.
- The base is quasi-excellent: `hQE : ∀ V : X.affineOpens, IsQuasiExcellent Γ(X, V)`.
  This uses the recorded ring predicate, and requires no universal catenarity.
- Normality is the stalkwise condition `hNormal : ∀ x, IsDomain (X.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.presheaf.stalk x)`. It covers disconnected normal schemes and
  the empty scheme. The published `IsNormalScheme` is not used because it additionally
  requires integrality and would wrongly exclude both cases.
- Separatedness is `[X.IsSeparated]`; the geometry and pullback forms use the same
  class on `T.level 0`. No separatedness is imposed on the covering source.
- The cover is `uMap : T.level 0 ⟶ X` with `[Etale uMap]`, `[QuasiCompact uMap]`, and
  `[Surjective uMap]`. The hypothesis that U is Noetherian is
  `[IsNoetherian (T.level 0)]` on the local tower in the descent clause. The initial
  tower level itself is U, so no extra choice of an unidentified U is introduced.
- Finiteness and ordering are the explicit `n : ℕ` and the existing `NormalizedTower n`.
  Every center ideal remains data. `hCenters : T.HasNowhereDenseCenters` says each
  center's closed zero set is nowhere dense. The normalizations are the actual
  function-field component normalizations used by `normalizedBlowup`.
- The two scheme pullbacks and their center identification are `D : DescentData T uMap`.
  `D.level i` is the recorded `Over.DescentDatum uMap (Over.mk (T.toFirst i))`, whose
  natural point-transport is exactly the overlap isomorphism, with its diagonal identity
  and triple cocycle. `D.arrows` is compatibility with every adjacent arrow. `D.centers`
  equates the two actual extended ideals on the universal overlap `T_i ×_X U`.
  This is the usual double-overlap datum by Yoneda, without making a new normalized
  tower pullback before its existence has been asserted.
- Effective descent: `normalizedBlowupTower_etaleDescent` concludes
  `∃ S e c, S.HasNowhereDenseCenters ∧ D.Realizes S e c ∧ ...`.
  Here `e : S.level 0 ≅ X`, `c : CenterMap T S` preserves every ordered center,
  and `Realizes` requires `c.map 0 ≫ e.hom = uMap`, every actual level square
  cartesian, and invariance under the given transports. The last requirement makes
  this the given datum, not merely a tower isomorphic to the local object.
- Unique compatible isomorphism: for every other `S' e' c'` with the same realization
  conditions the conclusion is `∃! E : CenterIso S S', ...`. Its zeroth component is
  over X and `c.map i ≫ (E.iso i).hom = c'.map i` for every level. All stages have the
  same original `n`; no stage contraction or removal of unit centers occurs.
- Equality of ideal centers after any jointly surjective flat family is
  `normalizedBlowupTower_flatCenterDetection`. For arbitrary `i : Fin n`, ideals I,J,
  an arbitrary index type `A : Type v`, schemes Y and maps f, the hypotheses are exactly
  `∀ a, Flat (f a)` and `∀ x, ∃ a y, f a y = x`. The conclusion is
  `(∀ a, I.comap (f a) = J.comap (f a)) ↔ I = J`. No quasi-compactness condition is added.
- Equality of synchronized towers is `normalizedBlowupTower_flatTowerDetection`.
  `e : ∀ i, T.level i ≅ S.level i` gives the synchronized level identifications.
  Arbitrarily indexed flat families `f i` cover each level. `hArrows` tests the arrow
  equations after those covers; `hCenters` tests the actual extended ideals after them.
  The conclusion is the unique `CenterIso T S` whose component family is exactly e.
  In particular arrow compatibility is tested locally, rather than assumed globally.
  The stage-zero comparison can be fixed to the identity when the common base is fixed.
- Étale pullback compatibility is `normalizedBlowupTower_etalePullback`: for every
  scheme Y and `f : Y ⟶ T.level 0` with `[Etale f]`, it produces a tower S of the same
  length n, `e : S.level 0 ≅ Y`, and a center-preserving `c : CenterMap S T` with
  `c.map 0 = e.hom ≫ f` and `c.IsCartesian`. Its centers remain nowhere dense.
  Y need not be quasi-compact or separated; no arbitrary-flat normalization claim is made.
- Finiteness of each normalization is the geometry clause
  `∀ i : Fin n, IsFinite (T.center i).blowup.fromReducedNormalization`.
  This concerns the actual normalization map to the ordinary blowup, not only the
  composite normalized blowup arrow.
- All stages Noetherian, normal and quasi-excellent are the first conjunction of
  `normalizedBlowupTower_geometry`, quantified over every `Fin (n + 1)` level. Normality
  again means normal domains at all stalks; quasi-excellence uses every affine open.
- The final composite is `T.toFirst (Fin.last n)`, defined by actual recursive arrow
  composition. Its conclusions are `IsProjectiveBundle`, `LocallyOfFiniteType` and
  `QuasiCompact`. These are projectivity in the required P(E) convention and finite type.
- The images of all centers are the literal finite union `T.centerImages`. The geometry
  theorem supplies an open V with `(V : Set _) = T.centerImagesᶜ`, `Dense V`, and
  `∀ i, IsIso (pullback.snd (T.toFirst i) V.ι)`. Thus every stage is the identity above
  the same specified dense open complement, not an unspecified smaller open.
- If X is integral, the last implication in the geometry theorem gives
  `∀ i, IsIntegral (T.level i)` and, for every generic x of each level,
  `T.toFirst i x ∈ genericPoints (T.level 0) ∧ IsIso ((T.toFirst i).stalkMap x)`.
  The function field of an integral scheme is its generic stalk; this is the actual
  structural map on function fields, with its normalization fixed by the common dense
  open. No unrelated field isomorphism is chosen. The open-identity conclusion is the
  preceding conjunction and therefore also holds under this implication.
- Action descent is `normalizedBlowupTower_actionDescent`. A compatible action A and
  an actual realization `hc : D.Realizes S e c` give the unique action B downstairs
  with `A.act i W g x ≫ c.map i = B.act i W g (x ≫ c.map i)` for all tests W, group
  sections g and tower points x. `Action` includes group laws, naturality, all arrow
  equations and preservation of actual center ideals. Natural actions of a constant
  group presheaf recover arbitrary abstract group actions; representable group
  presheaves give scheme-valued group actions by Yoneda, including the group parameter.
  The group-value universe w and flat-family universe v are independent of scheme u.
- The assertion for an already given tower without a cover is exactly the geometry
  theorem, whose signature has neither U nor uMap nor a descent datum. Applying it to
  any descended S (transporting along e at level zero) also gives all the promised
  geometry for the descended tower.

Dependency declarations used, read in their source modules:

- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent` (with the recorded `IsExcellent`
  and its constituent definitions). Only quasi-excellence is assumed.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `AlgebraicGeometry.IsNoetherian`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalization`,
  `Scheme.fromNormalization` for integral components, imported via the recorded
  `Sheaf.AlgebraicGeometry.ReducedNormalization` definitions `reducedNormalizationComponent`,
  `reducedNormalization`, `fromReducedNormalization`.
- `Sheaf.AlgebraicGeometry.NormalizedBlowup`: `Scheme.IdealSheafData.normalizedBlowup`,
  `normalizedBlowupMap`.
- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`: `Monoscheme.IsNormalizedBlowup`,
  `Monoscheme.NormalizedTower`. Its unrelated monoscheme/toric data is not an assumption.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `AlgebraicGeometry.IsProjectiveBundle`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`; `.Flat`: `Flat`;
  `.Finite`: `IsFinite`; `.FiniteType`: `LocallyOfFiniteType`;
  `.QuasiCompact`: `QuasiCompact`; `.Proper`: `IsProper`; `.Separated`: `Scheme.IsSeparated`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: `Scheme.Modules.IsQuasiCoherentFiniteType`;
  its ideal specialization is already represented in the existing tower by affine FG.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral` and `IsReduced`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: `Scheme.functionFieldOfComponents`,
  with the arbitrary-integral clause reusing Mathlib `Scheme.functionField`, the generic
  stalk. The theorem uses the actual generic stalk map rather than arbitrary field data.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, `IsDomain`
  in the recorded stalkwise normality convention.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`, and the scheme pullback instances.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`: `Over.DescentDatum`, its
  `transport`, `toHom` and cocycle/naturality fields, reused rather than copied.
- The new node `def-per-normalized-tower-descent-data` owns the center-preserving descent
  interface in `Sheaf.AlgebraicGeometry.NormalizedTowerDescentData`.

All available proof-dependency modules are private proof imports; these include
`WeilConjectures.Blowup.FlatBaseChange` from the closed upstream audit declarations
`blowupFlatBaseChange` and `blowupFlatBaseChangeIso`, the fpqc/mathlib leaf modules, and the
recorded project blowup, normalization, projectivity and coherent-module inputs. The two
recorded modules `Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts` and
`Sheaf.AlgebraicGeometry.QuasiExcellentFiniteTypeStability` are absent locally and
`scompile.py --source` confirms their sources are unavailable on the live server. They
are proof dependencies only; their imports are omitted and their DAG records are not
changed. The unstated proof-only normality/component lemmas likewise introduce no
notion in the delivered statements. No statement depends on a missing Lean declaration.

Edge cases checked before and after writing:

- n=0: `toFirst 0` is the actual identity; there are no ideals and `centerImages` is empty.
  The common open is the whole base, normalization-finiteness is vacuous, and the final
  composite is an identity, which is projective and finite type. The descent uniqueness
  includes the level-zero identification with X.
- Empty base: normality is vacuous, the componentwise normalization is the empty coproduct,
  and the statements do not impose `Nonempty X` or integrality. Empty flat index families
  cover exactly empty stages, whose ideals and maps are uniquely determined.
- Nonintegral normal bases: disconnected finite unions are allowed. In particular the
  overly narrow integral `IsNormalScheme` interface has not been used.
- Unit centers and invertible Cartier centers: no nonempty-center assumption is added.
  Such identity blowup stages are retained by Fin n indexing in every map and datum.
- Nonseparated U: only X is assumed separated; the proof of rigidity is affine-local
  on the preceding base, as the accepted split requires.
- Non-quasi-compact flat families: the two flat detection clauses impose no qc/fpqc
  covering assumption. Detection is stalkwise; normalization is never asserted to commute
  with arbitrary flat morphisms.
- Arbitrary characteristic: no rational or finite-type-over-a-field assumption occurs.
  No Noetherian finite-dimensionality or universal catenarity assumption is introduced.
- Étale identity and composition: the cartesian comparisons keep every extended ideal
  and every original stage. They are comparisons of the actual normalized blowup
  construction, not chosen arbitrary maps. The proof specifies the ordinary coefficient
  pullback and the unique normalization comparison.
- Actions include a possibly nontrivial base action. Compatibility includes the
  zeroth descent datum, so that action is descended too; no base-fixing assumption appears.

Searches performed with the prescribed msearch wrapper:

- LeanFinder: "Effective etale descent of finite towers of normalized blowups with coherent
  ideal centers and projectivity"; eight normalization/étale facts, no tower theorem.
- LeanFinder: "Finite normalized blowup tower descent datum with ordered ideal centers";
  eight normalization facts, no center-preserving descent data or tower descent theorem.
- LeanSearch: "descent data for normalized blowup towers with ordered ideal centers";
  eight generic pseudofunctor-descent and normalization facts, no exact tower result.
- LeanSearch: "Normalized blowup tower center preserving descent data and equivariant
  actions"; eight generic stack/descent/normalization facts, none the missing interface.
- Loogle: `AlgebraicGeometry.Scheme.IdealSheafData, AlgebraicGeometry.Etale`: no hits.
  The later combined query with `CategoryTheory.Over.DescentDatum` also has no hits
  (that project declaration is not indexed in Loogle); its source was read directly.
- Mathlib grep: `normalizedBlowup|BlowupTower`, and
  `NormalizedTower|normalizedBlowup|CenterMap|CenterIso` in AlgebraicGeometry: no hits.
- `rg` in project Sheaf and upstream WeilConjectures found the existing normalized
  blowup and the existing general `Monoscheme.NormalizedTower`, which are reused.
  The ordinary tower is also present, but its step construction is ordinary blowup,
  so it does not replace the existing normalized tower. No center-preserving descent
  interface, center isomorphism or natural tower action was found.
- DAG grep for normalized blowup towers finds the current theorem and toric/regularization
  consumers, with only `def-trf-monoscheme-toric-realization` owning the existing tower.
  `tools/blueprint_refs.py search 'normalized blowup tower'` reports zero blueprint
  matches. Its ancestor command gives `lem-per-artin-gabber-affine-curve`.
- `rg` for the item id in upstream Lean finds no declaration. The CompactObject example
  module has now been withdrawn, so the delivered header follows the extant project
  module-system convention (`module`, `public import`, exposed public section).

The new node records the actual search outputs, not reconstructed search results. Searches
are also recorded by the wrapper in the sandbox search log. ILO VIII printed pp.90--91 and
128--129 were read from the local PDF, especially 2.2.5, 2.2.8--2.2.11 and 5.5.3--5.5.5.
The current blueprint ancestor in `literature/blueprint/latest` was read; the accepted
geometric modification route and all target/unit statements are unchanged.

Validation: both delivered modules compiled separately, in dependency order, through
`scompile.py`, against the live published library. There are no errors or non-sorry
warnings. All universes and variables are bound explicitly; `autoImplicit` is false.
Every definition has real data and every postponed proof is a named theorem belonging to
this item. Final dry-run and delivery results are recorded below after running the tools.

No STATEMENT-DISPUTED issue and no source-based statement correction was needed.

## New nodes

`def-per-normalized-tower-descent-data` defines the center-preserving descent interface
on the already existing finite normalized tower. Its module is
`Sheaf.AlgebraicGeometry.NormalizedTowerDescentData`. The definitions are `toFirst`,
`HasNowhereDenseCenters`, `CenterMap`, `CenterIso`, `CenterMap.IsCartesian`, `DescentData`,
`DescentData.Related`, `DescentData.Realizes`, `centerImages`, `Action` and
`Action.Compatible`. They have the explicit data described above, and no postponed
proof or undetermined object is used. The source is ILO VIII 2.2.3--2.2.11 and
5.5.3--5.5.5, with the already recorded Yoneda transport definition for ordinary scheme
descent (Stacks 023V). The existing general scheme datum has no tower arrows or center
ideals; the existing `NormalizedPullback` has smooth stage maps but no cartesian condition,
no descent datum/cocycle, and no action. Neither therefore supplies this new interface.
The wrapper searches and DAG/blueprint/project greps above found no duplicate notion.
The item's statement dependencies gain this node and the three already landed owning
nodes of the reused normalized blowup, tower, and scheme descent definitions.

Dry-run repair: the live server preflight requires `import_flags` on a new definition
node (the standing field list omits it), so this node has the empty list `import_flags: []`.
The only first-pass rejection was this missing field. Both modules compiled cleanly.
The advisory naming `Sheaf.AlgebraicGeometry.ProjectiveBundleComposition` concerns a
shared module that also owned the dropped perverse-prefixed node; this delivery imports
it for the accepted, existing `lem-sfb-projective-bundle-composition` proof dependency
already selected by Q43's reviewer, not as a new perverse proof-route input.

Final dry run: `deliver2.py Q16 lem-per-normalized-blowup-tower-etale-descent --no-push`
printed `OK (dry run)` for commit `fc9ac60231b`: both modules compile and the server
preflight passes. The final delivery reruns these same required checks before pushing.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
