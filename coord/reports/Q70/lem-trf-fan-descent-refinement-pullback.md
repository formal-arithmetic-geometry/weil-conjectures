## Worker report

The module `Sheaf.TraceFormula.FanDescentRefinementPullback` states
`AlgebraicGeometry.Monoscheme.fan_descent_refinement_pullback`. Its only postponed
proof is that theorem. The auxiliary structures unpack this node's comparisons;
they neither choose towers from an undetermined existence assertion nor contain
`sorry` data. There are no new DAG nodes or repaired dependency modules, and the
node's mathematical statement, dependencies and proof remain unchanged.

Source read: ILO VIII, printed pp.100--102 (PDF pp.106--108), 3.1.11--3.1.28,
and printed p.92 (PDF p.98), Remark 2.3.5(ii)--(iii). In particular 3.1.22 fixes
recursive pullback rather than an arbitrary commuting tower; 3.1.25 fixes the
sharp ideal and fraction comparisons; 3.1.26 and Remark 2.3.5 prescribe the single
disjoint-union synchronization. This delivery does not invoke the downstream
`sharpening_fan_bijection` theorem. It imports its already existing helper
interfaces through the recorded descent dependency, as that dependency does.

Hypotheses and clauses, matched explicitly:

- The full category C with finite affine covers and both torsion-free stalk
  completions is `Monoscheme.ResolutionInput`. The hypothesis R is the recorded
  `Monoscheme.SmoothFunctorialDesingularization`, including its retained ordered
  centers, contracted smooth comparisons, and identity/composition equations.
- Fine torsion-free fans admitting finite affine covers are
  `FineFan.ResolutionInput`. Sharp finite affine covers and their actual lifted
  disjoint unions are the existing `AffineLiftCover`. No nonemptiness assumption
  on the fan, cover, or index set is imposed.
- The single rule tower and its full sharpened restrictions are
  `AffineLiftTowerDescentData R F C`, supplied for every F,C by the `descent`
  field. In particular its length is exactly `(R.resolution C.total).length`,
  its component maps are the uncontracted restriction, and its membership field
  specifies the glued ideals at every level. Its `contracted` and `smooth`
  fields retain the corresponding assertions of the descent dependency.
- The cover-independent assigned tower T_R(F) is `(Q.resolution F).tower`.
  `toAssigned` identifies each cover descent with it using the existing
  `FineFan.TowerIdentification`, whose fields preserve ordered centers and arrows.
  `based` pins the comparison to the identity on F, and `uniqueAssigned` states
  uniqueness with that pinning; this is stronger than a bare Nonempty isomorphism
  only in spelling out the node's word "canonical".
- The combined cover U+V is `CombinedAffineLiftCover`: `partition` enumerates
  precisely both original chart families, the two maps are disjoint open
  subunion inclusions with covering images, `leftOver`/`rightOver` fix their fan
  maps, and the chart-range equations identify each inherited component.
  `combined` provides it for every pair of covers. Its two
  `IsFanSubcoverCompatibility` clauses use R's actual contracted restriction
  comparison and state the index and level-map equations over the assigned
  tower. They therefore retain which stages were inserted before restriction.
- Removability on every U chart iff every V chart is the last equivalence in
  `combined`, with each original index k retained. Both tests explicitly require
  the whole ideal AND an isomorphism arrow. `localDeletion` identifies this test
  with the global test for every cover descent. No index removable on only some
  charts is deleted globally.
- Canonical identification between the two cover towers is `compare` with
  `compareBased` and `compareUnique`. `compareIndex` and `compareMap` identify it
  with the maps to the same assigned tower. `cocycleIndex` and `cocycleMap`
  quantify over ANY three finite covers; thus they include further refinements
  and express compatibility on indices and every level map.
- Replacement by another affine monoscheme lift in C is
  `arbitraryAffineLift`, for every rule input with a whole affine chart. Its
  `SharpResolutionIdentification` retains all centers, arrows and base maps
  between the sharpened R tower and the same Q tower of its sharpening. A
  specified identification of this affine fan with another presentation is
  handled by Q's comparisons for that isomorphism; no choice of splitting or
  extra condition on the lift enters the statement.
- For every smooth fan map g the existing `Q.comparison g hg` is precisely
  `FineFan.ResolutionComparison`: it supplies the recursively pulled-back tower,
  its base equation, and its contraction to Q(G), with centers and order retained.
  Thus it renders T_R(G) = (g*T_R(F))^c. Q's `identityIndex`, `identityMap`,
  `compositionIndex` and `compositionMap` supply the stated identity and
  composition equations, including exactly the successive surviving subsequence.
- `localSmoothModel` supplies `SmoothFanNeighborhoodModel` at every source point.
  Its source and target chart opens are exactly the generalization neighborhoods;
  `targetStalk` identifies the target chart monoid with its sharp stalk;
  `targetGermBijective` and `sourceGermBijective` identify sections with stalks
  using the actual canonical germ maps. `product`, `canonical`, and `overFan` realize the restricted
  fan map by the actual monoscheme spectrum map of B -> B times N^r. The
  `localized` field at EVERY prime gives B' -> B' times N^(r-t) times Z^t, fixing
  the homomorphism on the first factor, with t <= r; `smooth` also retains the
  all-stalk smoothness of that affine map.
- `smoothUnion` supplies one disjoint union of source and target affine lifts.
  Its `models` field includes the smallest source/target neighborhood model for
  every source point among those very finite covers.
  `SubunionFanTower` uses R's actual pulled tower for each open inclusion, its
  canonical base map, open restriction and inverse-image equations at every
  level. Its fan tower is descended from the sharpened full restriction by
  locally open maps covering every level. The supplied `PullbackTower` between
  the two raw fan towers retains the entire common length, the pulled-back center
  equation at every index, and all commuting arrows. The two contractions and
  the final index/level-map equations identify it with Q's smooth comparison.
- `fractions` specifies the map of saturated fraction charts by the induced
  group-completion map of the first-factor inclusion. Thus each b/a goes to
  g(b)/g(a), and elements of the original monoid go to their given images.
  The existing saturated blowup definitions use these charts and localized
  overlaps, so this equation also pins their restrictions. The overlap and
  comparison maps are canonical by the based uniqueness clauses.
- Before contraction the equality of generated ideals is `idealComposition`,
  for every composable triple with the actual composite map. The existing
  `PullbackTower.centers` fields apply it at every recursively identified level.
  Fraction substitutions are induced group homomorphisms, so composition is the
  corresponding substitution on every numerator and denominator.
- `deletedTransport` fixes the later ideal, not merely the stage's space:
  pulling an ideal back through the inverse of the deleted isomorphism and then
  pulling along the composite agrees with direct pullback. It quantifies over
  all subsequent coherent nonempty ideals and all further maps.

Dependency interfaces read and used:

- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`: `Fine`, `Hom`,
  `Hom.IsSmooth`, `Fine.toFan`, and the unsharp spaces and tower notions.
- `Sheaf.AlgebraicGeometry.FineFanBlowup`: `Fan`, `Hom.IsSmooth`,
  `ResolutionInput`, `Tower`, `PullbackTower`, `Contraction`,
  `ResolutionComparison`, `SmoothFunctorialDesingularization`,
  `pullbackAlong`, `pullbackIdeal`, `wholeIdeal`, and `saturatedChart`.
- `Sheaf.TraceFormula.AffineLiftTowerDescent`: `AffineLiftTowerDescentData`,
  `AffineComponentRestriction`, and their full field signatures. Its imported
  helper module `Sheaf.TraceFormula.SharpeningFanBijection` supplies
  `Monoscheme.ResolutionInput`, `SmoothFunctorialDesingularization`,
  `AffineLiftCover`, `Tower.toFan`, `sharpSpaceMap`, `FineFan.TowerIdentification`,
  `SharpResolutionIdentification`, `affineFine` and chart inclusions. Only these
  interfaces are used; no downstream bijection theorem is used.
- Plain proof imports: `Sheaf.AlgebraicGeometry.AffineFanHomUniversal`
  (`affine_hom_universal`), `Sheaf.AlgebraicGeometry.AffineFanLocalizationSections`
  (`affineFan_localization_sections`), and
  `Sheaf.GroupTheory.FineMonoidUnitSplitting` (`fine_monoid_unit_splitting`).
  The proof dependencies `lem-trf-smooth-tower-index-synchronization` and
  `lem-trf-sharpening-blowup-chart-comparison` currently have no recorded Lean
  declarations/modules, so no import is yet available for those proof steps.

Edge cases checked: empty fan and empty cover have no component/stage obligations
and the dependency forces zero length; Fin 0 permits all rank-zero models;
t=0 and t=r in the localization formula give the expected free/group extremes.
Disconnected fans and overlapping affine covers impose no disjointness on the
fan charts (only on their lifted coproduct components). An early draft incorrectly
required the whole covering map to be an open immersion: this was replaced by
local open immersions on a covering, since overlapping affine charts need not
map injectively from their disjoint union. The semigroup generated by 2 and 3
retains its nonidentity unit-center saturation because the deletion test also
requires IsIso. No independent smaller object or coefficient universe is used:
all monoids/spaces use the dependencies' arbitrary universe u.

Searches actually run:

- msearch LeanSearch, "Saturated blowup tower of fine fans descended from affine
  monoid spectra is independent of cover and functorial for smooth pullback":
  8 hits about saturated sieves and affine scheme covers, no monoidal statement.

- msearch LeanFinder, "Descent of saturated monoid blowup towers is independent of
  affine fan cover and compatible with smooth pullback and contraction": 8 hits
  about scheme affine-limit descent, none the monoidal statement.
- msearch Loogle, "FineFan.TowerIdentification, Monoscheme.AffineLiftCover,
  FineFan.Contraction": 0 hits, unknown identifier FineFan.TowerIdentification.
- msearch grep, "AffineLiftCover|fan_descent|TowerIdentification": 0 Mathlib hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the same expression found only
  the existing sharpening and affine descent helper interfaces, not this theorem.
- grep for this node id in `lean/WeilConjectures`: no hits.

Validation: the module is compiled through scompile.py in module mode, both as a
sandbox and under its final library module name. No auto-bound variables or local
notations/instances; all lines are at most 100 characters. Every theorem proof
in the delivery is sorry, as stage 2 requires. The dry run and delivery results
are recorded by the delivery wrapper.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
