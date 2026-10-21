## Worker report

The module `Sheaf.Paper.CompletedRingStrictFiniteExchange`, using the supporting
modules `Sheaf.Paper.CompletedStrictOpenExchange` and
`Sheaf.Paper.CompletedFiniteExchangeCoordinates`, states the completed-ring
strict open exchange and its finite-coordinate square. All theorem proofs are
`sorry`; definitions contain actual constructions. Maps chosen from existence
statements are uniquely determined by the displayed section or representative
equations. No family of unrelated evaluated derived maps defines the exchange.

Source read: the whole target node and its nine proof steps; the current blueprint
`main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md`;
Stacks `sites-modules.tex`, labels `lemma-extension-by-zero` (03DI),
`lemma-extension-by-zero-exact` (03DJ), and
`lemma-localize-morphism-ringed-sites` (04J0). The unit text concerns completion
after finite exchange; this node concerns only the strict exchange before Rlim.
No statement correction is made.

Hypotheses and clauses:

- The commutative Noetherian adic datum, finite generation, additive torsion,
  finite positive quotients, and perfect quotient modules are precisely the
  inherited fields of `AdicCoefficientDatum A`. `A : Type (u+1)` and
  `Scheme.{u}` preserve the small-site object universe `u+1` and Hom universe `u`.
  `cbcFiniteRing d n` bundles the existing quotient `A / I^(n+1)` once;
  `n : ℕ` represents every positive exponent, including exponent one.
- `sq : OpenImmersionSquare gU j' j g` supplies all four schemes and arrows,
  both open immersions, commutativity, and the chosen projection-compatible
  Cartesian identification. There is no condition on `g`.
- `pbcAdicCompletion T d`, `pbcTowers T (pbcAdicCompletion T d)`, and
  `completedReductionTower T d` are the existing actual limit coefficient
  sheaf, strict diagram category, and derived reduction functor. They are not
  replaced by towers in independently evaluated derived categories.
- `cbcStrictOpenModule d j hj` is whiskering by the existing `cbcOpenShriek`:
  slice transport, `SheafOfModules.extensionByZeroPresheaf`, then
  `PresheafOfModules.sheafification`. `cbcStrictOpen` is its exact termwise
  derived functor. These are exactly the stated `J_j` and `J_j'`.
- The `G` functors are the published `completedTowerPullback g d` and
  `completedTowerPullback gU d`, along the projection-induced
  `completedCoefficientMap`. No inverse completed ring map is required.
- `cbcReductionStrictExchange` is a natural isomorphism of the two displayed
  functors on **every** `DerivedCategory (pbcModules U (pbcAdicCompletion U d))`.
  Its component is the requested `b_K` in the actual derived strict tower category.
- The simultaneous representative is `cbcStrictInverseModule`: its index
  component is the existing `cbcUnderivedInverseExchange`, and its naturality
  fields are supplied by the named `cbcStrictInverseLevel_naturality` and
  `cbcStrictInverseComponent_naturality`, which state the existing ordinary
  naturality equations at each original transition and each tower morphism. Its inverse is
  an inverse in the strict diagram category. Applying `mapHomologicalComplex`
  gives simultaneous inverse chain maps. `CbcStrictExchangeNormalization`
  requires the inverse derived exchange to be exactly these maps transported
  through the two universal K-flat pullback counits. The uniquely specified
  `cbcStrictExchange` is precomposed with reduction to define `b_K`.
- `cbcFiniteProjection` is the completed projection followed by the inverse
  fixed constant-section ring comparison. `cbcFiniteRes` retains precisely that
  completed-ring action on a finite constant-coefficient module. Every arrow
  in the finite square is consequently completed-ring linear, not merely an
  arrow of underlying additive sheaves.
- `cbcFiniteReduction` is `K_n` transported to finite constant coefficients.
  `cbcFiniteSource` and `cbcFiniteTarget` are the exact finite module pullback
  and open-extension composites, followed by that scalar restriction.
  `cbcSourceFiniteComparison` and `cbcTargetFiniteComparison` identify the
  two evaluations with these objects. Their unique specifications
  `CbcSourceFiniteNormalization` and `CbcTargetFiniteNormalization` retain the
  ordinary finite-coordinate maps and all universal counits on K-flat models.
  Thus these are specified constant/completed finite comparisons, rather than
  arbitrary isomorphisms that could absorb an automorphism of the exchange.
- The map equality in `completedRingStrictFiniteExchange`, for all `K` and `n`,
  says that evaluation of `b_K` is `cbcFiniteExchange` under those comparisons.
  `cbcFiniteExchange` is the derived image of the inverse of the existing
  `singleBetaInv`, followed by the specified completed scalar restriction.
  `singleBetaInvApp` is literally the `moduleJAdj` adjoint transpose of
  finite `gU^*` applied to the open unit, followed by `moduleSquareG.inv`.
  This is the dependency's canonical finite exchange in constant-ring module
  coordinates. The recorded ordinary pro-etale comparison
  `ordinaryOpenExtensionBaseChangeIso` uses the same Cartesian right-adjoint
  conjugation in `Sheaf (ModuleCat Λ)` coordinates; no replacement exchange is
  defined here.
- The inverse finite component is fixed by the actual `cbcFiniteInverse`
  construction from `singleBetaInv`, before localization. Scalar open and
  pullback comparisons are mates of the uniquely normalized
  restriction/direct-image comparisons. Inverting the final finite square
  identifies the inverse with this specified open-unit adjunct.
- Commutation with **all** quotient transitions is built into the strict
  natural transformation, whose `naturality` quantifies over every arrow of
  `ℕᵒᵖ`, not just successors. Its mapped cochain transformation also commutes
  with differentials. The finite comparison normalizations use the same
  quotient level coordinate change and sectionwise scalar maps at every
  index. Thus identities, nonadjacent transitions and composites remain those
  of the original reduction tower. The existing finite scalar lemma supplies
  the equivalent semilinear finite-coordinate transition equations.
- No hypothesis on completeness, quasi-compactness, constructibility or
  boundedness of `K` occurs. Neither defining composite for `b_K` contains Rlim.

Dependency declarations read and used:

- `Sheaf.Paper.AdicCoefficientDatum` and its completed coefficient support:
  `AdicCoefficientDatum`, `completedReductionCoefficient`,
  `completedReductionModuleTowerFunctor`, `completedReductionTower`,
  `reductionChange`, `reductionDerivedChange`, `reductionDerivedRestrict`;
  also `Sheaf.Paper.BoundedConstructibleTower`'s definitionally identical
  `pbcModules`, `pbcTowers`, `pbcTowerEvaluation`, `pbcLevelConstantComparison`,
  `pbcRestrict`, `pbcDerivedRestrict`, and normalized `pbcComplexCounit`.
- `Sheaf.AlgebraicGeometry.OpenImmersionSquare`: `OpenImmersionSquare`.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`; Mathlib
  `Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`. These are used through the existing
  `cbcOpenShriek`, not recreated.
- `Sheaf.Paper.CompletedTowerPullback`: `completedCoefficientMap`,
  `completedModulePullback`, `completedTowerModulePullback`,
  `completedTowerPullback`, `completedTowerPullbackCounit`,
  `completedTowerPullbackComplexCounit`, `completedReductionTowerCounit`.
  This interface is available through the public import of
  `Sheaf.Paper.CompletedExtensionZeroComparison`; its owning node is unchanged.
- `Sheaf.Paper.CompletedExtensionZeroComparison`: `cbcOpenShriek`,
  `cbcOpenRestriction`, `cbcOpenAdjunction`, `cbcCompletedModuleDirectImage`,
  `cbcModulePullbackAdjunction`, `cbcUnderivedInverseExchange`, and their
  existing instance statements. Only the already published ordinary
  constructions are used; the downstream completed comparison theorem is
  not an input. The maintainer must skip any proof-import back into this
  module which would create an import cycle, as stage 2 rule 3.7 requires.
- `Sheaf.Paper.ConstantCompletionEquivalence`: the flat constant/completed
  and finite-pullback comparisons, used in the finite comparison proof plan.
  `equivalence` is only an equivalence on complete subcategories; the ambient
  finite comparison used here does not impose completeness on `K`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`:
  `ProEtale.ordinaryOpenExtensionBaseChangeIso`, and its existing normalized
  constant-ring module counterpart in
  `Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized`:
  `singleBetaInvApp`, `singleBetaInv`, `moduleSquareG`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`:
  `finiteCoefficientModulePullback_exact`, and the exact finite module
  operations used by `modulePullback`.
- `Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars`:
  `exchange_restrictScalars`, `exchange_transition`, `exchange_ambient_towers`
  provide the quotient-transition and ambient-linearity proof inputs.
  Other available proof dependency modules are imported for the supplied
  nine-step plan: localization, module adjunction, diagram K-flat resolutions,
  resolving-class descent, and open tensor normalization.

Edge cases checked before writing: the zero ring (all coefficient categories
are zero), `I = A` (all positive quotients zero), `I = 0`, exponent one,
identity and repeated quotient levels, the empty open, the empty scheme,
identity base change, arbitrary non-quasi-compact opens, and unbounded complexes.
The sectionwise and mate normalizations preserve these cases. In particular no
nonemptiness, characteristic restriction or invertibility of the completed
structure map is introduced.

Searches actually run with `msearch.py NA lem-cbc-completed-ring-strict-finite-exchange`:

- `leanfinder`: "Completed coefficient strict tower pullback open extension by
  zero exchange canonical finite reduction" returned eight adic-completion
  sequence/extension lemmas (`IsAdicComplete.StrictMono.*`); no sheaf strict exchange.
- `loogle`: `"Sheaf", "extension", "pullback"` returned zero hits.
- `grep`: `completed.*[Ee]xchange|strict.*[Ee]xchange`, in `CategoryTheory`,
  returned zero Mathlib hits.
- `leansearch`: "Strict tower open extension pullback completed coefficient
  exchange" returned ordinary topological open-pullback and geometric
  open-immersion lemmas, with no completed-ring strict exchange.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf`, for the node id and
  `completed.*[Ss]trict.*[Ee]xchange|cbcTower.*[Ee]xchange|cbc.*[Ff]inite.*[Ee]xchange`,
  found no statement of this node. Broader completed/strict/open-exchange searches
  found the ordinary canonical helpers, the finite scalar module and the
  later Rlim comparisons cited above. Their full interfaces were read; none
  supplies this simultaneous normalized strict-tower finite statement.

The displayed map equations use `HEq` for the two presentations of the same
module-map type. This is equality of the specified maps; it does not quantify
over an unspecified transport or weaken any normalization. It avoids repeated
elaboration of definitionally identical composite-functor endpoints.

The canonical strict exchange and its finite scalar coordinate system are recorded
as the two definition nodes below. The requested node only gains these two
statement dependencies and its Lean record. Its statement is unchanged.

## New nodes

`def-cbc-completed-strict-open-exchange`, module
`Sheaf.Paper.CompletedStrictOpenExchange`: the actual termwise sheafified open
extension, its strict inverse-exchange maps, the derived exchange uniquely fixed
by the universal-counit representative equation, and its precomposition with
reduction. This packages the strict construction in source proof steps 1–6 as a
named canonical notion. Ordinary extension and ordinary inverse exchange are
reused, not copied. All supporting postponed properties have named theorem
statements and complete proof docstrings. The naturality equations quantify over
every tower arrow and morphism, including identities and nonadjacent transitions.

`def-cbc-completed-finite-exchange-coordinates`, module
`Sheaf.Paper.CompletedFiniteExchangeCoordinates`: the completed action through the
finite projection, the uniquely section-normalized direct-image and open
restriction comparisons, their canonical mates, the finite reduction coordinate
change, their source/target composites, and the actual universal-counit source
and target model maps used to specify the derived finite comparisons. This is the actual finite coordinate
system needed for source proof step 7. It does not choose a bare isomorphism;
every chosen datum is uniquely determined by its section equation. The named
zero-map properties are passed explicitly when mapping these comparisons to
complexes, retaining the actual square parameter and the same maps.

For these nodes the additional LeanSearch queries were respectively
“Canonical strict tower completed ring open extension exchange specified by
universal derived counits” and “Finite coefficient scalar restriction open
extension pullback coordinate comparison normalized on sections”. The first
returned generic derived counits, Kan extensions, module scalar adjunctions and
universal derivations; the second returned ordinary scheme restriction and scalar
restriction. Loogle `"Sheaf", "restrictScalars", "pullback"` and Mathlib
CategoryTheory grep `strict.*[Ee]xchange|completed.*[Ff]inite.*[Cc]omparison` both
returned no hits. The extra LeanFinder searches returned condensed-solid/adic
completion results and ordinary module tilde/geometric restriction results.
`blueprint_refs.py search` returned zero matches for both “strict open exchange”
and “finite scalar restriction”. A DAG title/statement search and the project
`rg` search for the new declarations found no existing definition of either
construction. The ordinary helpers and related theorem nodes remain reused as
listed above. The two modules separate these canonical notions from the requested
finite-identification theorem; each is compiled separately within the unchanged
60-second limit.

Validation: all three delivered modules compile separately through the prescribed
`scompile.py`, with no errors or warnings. The complete delivery also passed the
server preflight and compile checks in `deliver2.py --no-push`. Every invocation
retained the prescribed 60-second per-file limit. No local or global build was run.

## Returned delivery repair

H13, returned head `e75eae498358`: removed the sandbox copy of
`def-weil-pbc-completed-pullback.json`. The delivery therefore leaves the live
record byte-for-byte unchanged: module `Sheaf.Paper.PbcQbarCompletedPullback`,
primary `AlgebraicGeometry.Scheme.pbcQbarCompletedPull`, `existing: false`, and
all four `pbcQbar*` declarations retain their owner. No dependency record is
rebound and no dependency module is delivered.

The required ambient `completedTowerPullback` interface already reaches
`CompletedStrictOpenExchange` through its public import of
`Sheaf.Paper.CompletedExtensionZeroComparison`, whose line 8 publicly imports
`Sheaf.Paper.CompletedTowerPullback`. Thus the ownership repair needs no Lean
change. The three Lean modules and their statement signatures remain unchanged
from the returned packet, whose mathematical substance was independently
accepted in the return. The two new definition nodes remain owned by their
respective modules, and the item still cites both.

## Repair self-check

Checked the current live completed-pullback record and the public-import path
above. The only removed packet path is the unnecessary dependency-node copy;
the report no longer claims that record is repaired or replaced. Checked that
each of the three remaining node records owns its delivered module, that its
primary signature matches the source verbatim, and that the item's only node
deltas from the current live copy are its Lean record and the two new statement
dependencies. No mathematical statement, definition, hypothesis, proof plan, or
edge case was changed by this repair. This is the dispatcher's repair self-check,
not a new independent mathematical review.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
