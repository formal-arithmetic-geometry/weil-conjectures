## Worker report

Q65 states `lem-trf-descended-resolution-smooth-comparisons` without changing its
statement, proof, or proof dependencies. The theorem is
`AlgebraicGeometry.OrdinaryResolutionDescent.descendedResolution_smoothComparisons`
in `Sheaf.AlgebraicGeometry.DescendedResolutionSmoothComparisons`. Its only proof
is `sorry`; all the supporting declarations have real structure fields or explicit
transport terms. The added definition node packages the mathematical hypotheses
and conclusion so that this theorem's signature is readable and reusable.

Source read: ILO, Travaux de Gabber, Exposé VIII, 2.3.4 and Remark 2.3.5(i)--(iii),
printed pp.91--92 (PDF extraction saved in the sandbox). The source explicitly
uses equality for canonical contraction and explains uniqueness by the absence
of blowup automorphisms over the base. Remark 2.3.5(ii) explicitly resolves the
whole disjoint union of a covering to retain synchronization. The current
blueprint ancestor is the historical branch recorded in the node; no current
unit statement or route is changed.

Hypothesis correspondence (names below are in
`AlgebraicGeometry.OrdinaryResolutionDescent` unless qualified):

- A totally ordered label set is `(L : Type w) [LinearOrder L]`, with universe `w`
  independent of scheme universe `u`.
- Reduced finite-type rational schemes are the existing
  `AlgebraicGeometry.RationalResolutionInput.{u}`. This contains the structure
  morphism to `Spec (ULift ℚ)`, `IsReduced`, `LocallyOfFiniteType`, and
  `QuasiCompact`. No separatedness is imposed on these inputs.
- The domain C is `Embeddable S`: existence of a closed immersion into a smooth,
  separated, locally finite-type and quasi-compact rational scheme, with the
  factorization equation for the structure morphism. This is an intrinsic
  predicate, not a choice of ambient embedding, so A cannot depend on a chosen
  embedding. No connectedness or dimension condition occurs.
- A's assignment is `Datum.localRule : LocalRule L`. Its `tower S eS` is a
  `LabeledTower L S.scheme` on every embeddable input. The proof `eS` is in Prop
  and therefore does not distinguish multiple embeddings of the same input.
- `LabeledTower.tower` is the recorded `OrdinaryBlowupTower`, with the actual
  blowup identifications and transitions; `labels : Fin tower.length ↪o L`
  enforces distinct increasing labels. Its `regular` field is exactly the
  recorded `OrdinaryBlowupTower.IsRegularResolution`: finite-type ideals,
  nonempty nowhere dense regular centers, and regular final level. Its
  `coherent` field uses the genuine finite-type-and-kernel predicate
  `RingedSpace.IsCoherent` on the center's module. There is no support-only
  replacement of the ideal and no unnamed construction of a center.
- `LocalRule.comparison` assigns `Comparison` to every rational smooth morphism
  in C, with its equation over Q. `Comparison` extends the recorded
  `OrdinaryResolutionComparison`, so it includes the cartesian squares,
  transitions, increasing survivor embedding, monotone count equations,
  extended retained ideals, and deletion iff the extended ideal is unit.
  `Comparison.labels_eq` requires exactly the original surviving labels.
- R's assignment is `Datum.tower`, on every `RationalResolutionInput`, with
  exactly the same `LabeledTower` convention and regularity/coherence fields.
- The finite affine cover uses Mathlib's `Scheme.AffineOpenCover` and `Finite`
  on its index type. `AffineCover` adds its total rational input, component
  arrows, `IsColimit (Cofan.mk ...)`, its map to S, and the factorization and
  rational-base equations. Thus the total really is the disjoint union, not an
  arbitrary covering input. Every finite cover admits such a presentation.
  `embeddable` records the derived property that a finite disjoint union of
  finite-type rational affines embeds in a smooth separated rational scheme;
  it is not an extra restriction on the covers.
- `Datum.cover` gives `CoverIdentification` for EVERY such cover. It extends
  `OrdinaryTowerCartesianMap`, so the lengths, all level pullbacks, all adjacent
  transitions and the full center ideals agree, without deletion.
  `CoverIdentification.labels_eq` compares every label using that length
  equality. These are exactly the identifications of the glued labeled ideals.
- `Datum.cocycle_count` and `cocycle_map` state compatibility for smooth maps
  between cover disjoint unions over the same S. The counts, transported via
  the two cover length equalities, are the same global index. The level maps
  into R(S) agree. The center equation is already in `Datum.cover`; restriction
  of the same global ideal to overlaps gives equal ideals there. Refining
  source affines if necessary gives the usual overlap and triple cocycle,
  without assuming that intersections of affines are affine.

Conclusion correspondence:

- `Nonempty (DescendedRule D)` asserts the required global comparison data for
  the given A, R and specified cover identifications. It does not assume a
  preexisting global comparison. `GlobalRule.rule` reuses
  `SmoothFunctorialOrdinaryResolution` instead of copying its laws.
  `GlobalRule.tower_eq` fixes its towers to the prescribed R towers.
  `transportComparison` is literal equality transport of that existing rule's
  comparisons to those fixed towers. `GlobalRule.comparison` adds the labels.
- The underlying `OrdinaryResolutionComparison` gives the canonical contracted
  cartesian comparison at all original levels, its original order, and full
  retained extended ideals. Its count-before/after and deleted-level equations
  are the explicit retained/count data of the source statement.
- `DescendedRule.restricts` quantifies over every S,T,h, every U,V, and every
  smooth map of their disjoint unions over h. This includes the induced map of
  every subordinate affine cover. `Restricts.count_eq` and `retained_eq` match
  the ordered deletion data, and `map_eq` says the square of actual level maps
  commutes with the SPECIFIED A comparison and the SPECIFIED cover maps.
  Asking this simultaneously for all covers is cover independence, rather
  than merely existence of a cover on which some comparison works.
- `DescendedRule.deleted_locally` is exactly deletion iff, for EVERY component
  b of V, the target center pulled to the source level and then to its lifted
  V_b is the unit ideal. The lift is the actual pullback of `toBase` along
  `V.cover.f b`, using `pullback.fst`. Retained ideals remain the recorded
  comparison's `retained_ideal`; the cartesian squares are its `cartesian`.
- Identity counts and level maps are
  `SmoothFunctorialOrdinaryResolution.identity_count` and `identity_map` on
  `GlobalRule.rule`, transported via `tower_eq`. Identity survivor embeddings
  are explicit in `DescendedRule.identity_retained`.
- Composite counts and level maps are the existing `composition_count` and
  `composition_map`, including their `eqToHom` transports. Composition of
  survivor embeddings is explicit in `DescendedRule.composition_retained`.
  Cartesian-square uniqueness gives exactly the canonical pullback
  associativity identification; no independent arbitrary associator is chosen.
- `DescendedRule.canonical_steps` supplies `CanonicalSteps`. At a retained
  center, transport the lower level by `count_before`, identify the equal
  center ideals over that lower level, and compare the upper map (transported
  by `count_after`) with the published `blowupFlatBaseChangeIso` followed by
  the target blowup-level identification. The equality is required for every
  such identification over the lower base, not for an arbitrary unnormalized
  isomorphism of blowup schemes. The published map is constructed by the
  coefficientwise Rees pullback and relative Proj; on affine charts this is
  precisely the canonical tensor base-change identification. The bound `Flat f`
  here is universally quantified when testing this property, not an added
  hypothesis of the descent theorem. The lower map is flat since its square
  is cartesian over smooth h; the center-identifying isomorphism exists by
  `retained_ideal`. Thus the normalization is not vacuous. Unit stages already
  have constant count and the existing transition naturality equations.
- Surjective smooth nondeletion is
  `SmoothFunctorialOrdinaryResolution.surjective_no_deletion`. It states actual
  surjectivity of the retained-stage embedding, not just equality of lengths.
- There is no fixed relative dimension and no connectedness anywhere. Every
  rational input is allowed, and a cover total is always a whole disjoint union.
- `DescendedRule.empty_trivial` applies to every empty rational input: if A's
  tower on it has length zero, R's tower has length zero. The zero-stage
  ordinary tower's initial isomorphism is exactly triviality of that tower.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`:
  `RationalResolutionInput`, `OrdinaryBlowupTower`, `.toBase`,
  `.IsRegularResolution`, `OrdinaryResolutionComparison`, and
  `SmoothFunctorialOrdinaryResolution`, including all their field signatures.
- `Sheaf.AlgebraicGeometry.OrdinaryTowerCartesianMap`:
  `AlgebraicGeometry.OrdinaryTowerCartesianMap`, reused in full. This is the
  just-landed definition node `def-per-ordinary-tower-cartesian-map`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `.Smooth`, `.Proper`,
  `.Separated`, and `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `IsClosedImmersion`, `Smooth`, `IsSeparated`, `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Cover.Open`: `Scheme.AffineOpenCover` and its
  existing affine-spectrum components and cover arrows.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `.blowupMap`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`:
  `Scheme.IdealSheafData.comap`; `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`; cartesianness is `CategoryTheory.IsPullback`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, explicitly
  including local Noetherianity as required by the recorded node.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes the recorded
  `AlgebraicGeometry.RingedSpace.IsCoherent`; ideals as modules use
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`.
- `WeilConjectures.Blowup.FlatBaseChange`: `blowupFlatBaseChangeIso` and its
  underlying coefficientwise Rees map. The node has no `lean` record but its
  closed upstream audit identifies this exact declaration; no copy is written.
- Proof-only imports are `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`
  (the recorded smooth/flat criterion), `Mathlib.AlgebraicGeometry.Gluing`
  (scheme morphism gluing), and `.PullbackCarrier` (surjective base change).
  Flat and smooth restriction/locality modules are already public dependencies.
  `lem-sfb-flat-pullback-blowup-chart-restrictions` has neither a usable `lean`
  nor a Mathlib match at this base, so it has no module to import. It is a proof
  dependency, not a missing statement notion, and its use is preserved in the
  theorem's complete proof docstring.

Edge cases checked before and after writing: length zero gives empty survivor
embeddings; no arbitrary positive-length assumption occurs. The empty scheme
has an empty finite affine cover (the covering condition has no points), and
empty affine opens are allowed. A non-surjective open immersion may miss a
center, so the local-unit iff permits deletion; a surjective smooth map cannot.
Two-component covers carry a single common labeled tower; centers absent on
one component remain present on the total if present on the other. A composite
can delete a label retained by its first factor; the composite count and
survivor equations cover this. Non-separated schemes are allowed; overlap
refinements do not require affine intersections. Different smooth relative
dimensions on components and arbitrary scheme/label universes are allowed.

Searches: the prescribed msearch wrapper ran LeanFinder for descent of smooth
cartesian comparisons of labeled ordinary towers (8 unrelated affine-limit,
smoothness and cover-refinement hits), Loogle for OrdinaryResolutionComparison
and Scheme.OpenCover (0 hits; the project name is unknown to Loogle), grep for
`OrdinaryResolution|contracted.*tower|resolution.*descent` (3 unrelated injective
resolution hits), and LeanSearch for labeled ordinary blowup towers with affine
resolution descent (8 affine-cover/general morphism descent hits). Exact wrapper
JSONL results are preserved in the new node's mathlib_searches. Project/DAG rg
and `tools/blueprint_refs.py search 'ordinary resolution'` found no such datum.
Existing project ordinary towers/cartesian maps and Mathlib affine open covers
are used, not duplicated. The existing embedded labeled towers are ambient
strict-transform diagrams indexed by lower cuts, and cannot express this
intrinsic finite ordinary-tower datum unchanged. No existing upstream file
contains the item id or the conditional statement.

No statement is disputed and no dependency interface is changed. Both delivered
modules compiled separately in dependency order via scompile.py, clean except
for the intended sorry theorem. The wrapper's local attempt encountered a full
scratch filesystem; its normal server fallback succeeded (2.7s for the data
module and 1.5s for the theorem), so no tool workaround was used.

## New nodes

`def-trf-labeled-ordinary-resolution-descent-data` defines the additional labeled
ordinary towers, intrinsic embeddable domain, whole-disjoint-union affine cover
data, specified local rule, cover identifications and cocycle, and the precise
global descent conclusion. Source: ILO VIII 2.1.4--2.1.9 and 2.3.4--2.3.5(ii).
All source theorem hypotheses and clauses are spelled out above. Searches of
all three required kinds are recorded in its JSON, plus the DAG/project search.
The existing ordinary tower, contracted comparison, uncontracted cartesian
comparison, coherent module predicate and affine open covers are reused.
The module has no postponed theorem or data chosen from a sorry existence.
Its two helper definitions only perform equality transport or build a labeled
record from the existing comparison data. The item cites the new node.

## Second reading by Q65

I re-read the node and both files against the correspondence above after the
first clean compilation. In this dispatcher assignment no other worker may be
started; this is a self-rereading for the delivery, and the maintainer's review
is the independent reading. The audit found and fixed these issues during
preparation: imported the existing ideal-to-module interface; explicitly bound
the center index to eliminate an ambiguous Fin inference; replaced a manually
repeated affine-cover structure by Mathlib's `AffineOpenCover`; and reused the
existing `SmoothFunctorialOrdinaryResolution` for global count/map coherence
instead of declaring a parallel set of laws. I checked the directions of both
count equality transports in `Restricts.map_eq` and the `count_before` and
`count_after` transports in `CanonicalSteps` against their source signatures.
The local deletion equation uses the first projection from the actual lifted
open and quantifies over all source cover components. The subordinate-cover
restriction preserves the specified A maps, not merely their isomorphism
classes. Every retained label, every count, every level map, ideal, chart map,
identity/composition law, nondeletion and empty clause has a corresponding
field described above. No node statement correction was needed.
