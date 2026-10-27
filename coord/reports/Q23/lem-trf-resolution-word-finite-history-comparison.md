## Worker report

Item: `lem-trf-resolution-word-finite-history-comparison`, Q23, stage 2.
Module: `Sheaf.AlgebraicGeometry.ResolutionWordFiniteHistoryComparison`.
Main declaration:
`AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_finite_history_comparison`.
There is one postponed theorem, with `sorry`; all ten helper definitions have actual bodies.
The existing item's JSON is changed only in `lean`. No new nodes or dependency repairs.

Sources read: the item's complete statement and seven proof steps; every statement dependency
and its recorded Lean declaration; ILO VIII, printed pp. 92--94, especially Remark 2.3.5(i)
(contraction exactly when a center is missed), Remark 2.3.11 and §2.3.13 (the distinction
between equidimensional smooth functoriality and synchronization for arbitrary smooth maps).
The PDF was read with `pdftotext -layout`, searching the numbered passages. ILO refers to
BMT §6.3; that detailed source remains WANTED as recorded in the node. No unverified claim
of reading BMT is made. The module docstring retains the node's seven-step proof route.

Hypothesis and conclusion correspondence:

- Over Q, reduced X, closed embedding into smooth, separated finite-type P:
  `EmbeddedResolutionPair.{u}` is precisely the dependency's bundle. Its fields are
  `X`, `P`, `base`, `inclusion`, `closed`, `reduced`, `smooth`, `separated`, `finiteType`,
  `quasiCompact`. Its base is `Spec (.of (ULift.{u} ℚ))`, not a size-zero restriction.
- Fix the normalized assignment from the gluing node:
  `R : MarkedIdeal.NumericalResolution.{u}`, `ν : ValueFamily HilbertSamuel.ResolutionWord`,
  and `hν` reproduce exactly the full predicate under the existential in
  `normalized_resolution_word_gluing`. In particular charts exist at every singular point;
  every chart computes ν and has numerical leading entry one; ν is bottom exactly at regular
  points. The finite-image, closed-upper-level and auxiliary-summation clauses are retained.
  This does not assume an arbitrary smooth-invariant function in place of the fixed word.
- The normalized head and marked tail use the existing `HilbertSamuel.normalizedHead`,
  `ResolutionWordChart.word` and `ResolutionWordChart.tail`, via `hν`. The head is
  `(c, Δ^q h)` and the tail is the fixed engine's actual numerical word with its first
  entry removed. The helper does not introduce a second resolution word or presentation.
- Finite admissible histories and all earlier centers in order:
  `EmbeddedResolutionHistory`, `Admissible ν`, `SmoothPullback` and `IntrinsicComparison`
  are the recorded dependency declarations. `wordPrefix` restricts their actual functors,
  natural inclusion, blowup isomorphisms, strict-transform isomorphisms and center data;
  it never filters an identity intrinsic blowup. `wordAtStage` evaluates ν on this actual
  finite prefix, so all comparison clauses cover every stage, not just the endpoint.
- Smooth initial pullback Q → P, with Q separated and finite type over Q:
  the second conjunct explicitly quantifies `B`, `Q`, `g : Q ⟶ B.P`, with `Smooth g`,
  `IsSeparated (g ≫ B.base)`, `LocallyOfFiniteType (g ≫ B.base)` and
  `QuasiCompact (g ≫ B.base)`. It concludes `IsReduced (pullback B.inclusion g)`.
  Smoothness of Q over Q follows from `Smooth g` and `B.smooth`. Together these give the
  pair Y in Q that can be used in `EmbeddedResolutionSmoothMap`; reducedness of that
  initial pullback is a conclusion, not an extra hypothesis.
- Existence of the pulled-back history, precisely empty stages deleted:
  for any `f : EmbeddedResolutionSmoothMap A B` and admissible original `K`, the third
  conjunct gives `∃ m H, Nonempty (SmoothPullback f H K)`. The dependency's `index` is a
  monotone surjection; its `centers` says exactly that a collapsed stage has unit extended
  ambient ideal, whereas a retained stage has a nonempty center and its actual extended
  ideal. Cartesian ambient and intrinsic squares and all diagram maps are part of the
  existing structure. Once the comparison is chosen, `Admissible.pullback` gives
  admissibility of H. No termination hypothesis occurs.
- Geometry at every stage:
  the first conjunct is `∀ K, Admissible ν K → WordHistoryGeometry K`.
  Its body quantifies every `j : Fin (n+1)` and states `Smooth`, `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact` of the recorded rational structure map
  `wordStageBase j`, and `IsReduced` of the actual intrinsic stage. It applies equally
  to original and pulled-back admissible histories.
- Stagewise word equality at corresponding points:
  the fourth conjunct universally covers every actual `SmoothPullback` c, not only the
  existentially supplied choice. `WordSmoothComparison` states for every original stage
  j and every point y of source stage `c.index j`:
  `wordAtStage ν H (c.index j) y = wordAtStage ν K j (c.intrinsic j y)`.
  There is no `SmoothOfRelativeDimension` or constant-dimension assumption.
- The local head formulas:
  the same pointwise clause gives a natural s whose value is the actual `ringKrullDim`
  of the local ring of the smooth fibre at `asFiber y`, then states
  `localFunction(source,y) = (summation^[s]) localFunction(target,c.intrinsic j y)`,
  `minimumComponentDimension(source,y) = minimumComponentDimension(target,x) + s`,
  and equality of `componentDimensionCount`. Thus s is chosen separately at each point,
  including nonclosed points; it is not confused with global relative dimension.
- Agreement of marked tails:
  `WordSmoothComparison` quantifies every source chart C and target chart D on those
  prefixes, at corresponding points, and concludes `C.tail = D.tail`. The charts are
  the fixed dependency's controlled-history charts with ordered earlier centers and births,
  rather than arbitrary local tails.
- Every full original maximum stratum:
  `WordSmoothComparison` quantifies v and a closed subset T with
  `IsGreatest (Set.range (wordAtStage ν K j)) v` and
  `(T : Set _) = {x | wordAtStage ν K j x = v}`. The first ideal equality is
  `(vanishingIdeal T).comap (c.intrinsic j) = vanishingIdeal (T.preimage ...)`.
  This is equality of ideal sheaves, not only supports or set-theoretic centers.
- Ambient ideal equality:
  `wordAmbientIdeal K j T` is the kernel ideal of the reduced stratum's closed immersion
  into that stage of K's ambient scheme. Its comap along `c.ambient j` is explicitly
  equal to the corresponding ambient ideal of the inverse-image closed stratum in H.
  No assumption says the inverse-image stratum is maximal on H.
- An empty inverse-image stratum:
  the final implication in `WordSmoothComparison` concludes that BOTH of the extended
  ideals above are `⊤`. Here `⊤` is the unit ideal, the center whose blowup stage is deleted.
- Intrinsic comparison over an initial reduced-scheme isomorphism, possibly different
  ambient embeddings:
  the fifth conjunct takes `c : IntrinsicComparison e H K`, with both histories admissible,
  and concludes `WordIntrinsicComparison ν c`. The dependency's natural isomorphism of
  intrinsic diagrams and its center-kernel equalities retain every earlier ideal in order.
  There is no ambient isomorphism binder. At every stage the words agree under
  `(c.iso.app (op j)).hom`, and the reduced intrinsic ideals of their maximum strata
  agree by comap. Its T and U are the whole equality loci of the same greatest value v.
- Compatibility with open restriction and further smooth pullback:
  every comparison above is universal and includes open immersions. The final conjunction
  `WordPullbackCoherence ν` additionally states equality of composite and successive
  deletion-index maps, final intrinsic maps, final ambient maps, words, intrinsic maximum
  ideal extensions and ambient maximum ideal extensions. It quantifies actual comparison
  data over initial maps whose composites agree, so these are equalities for the canonical
  cartesian maps, not for arbitrary maps supplied instead of base change.
  `WordIntrinsicSmoothCoherence ν` supplies the commuting final-map square for an intrinsic
  isomorphism followed by smooth pullback, and the resulting equality of the two intrinsic
  maximum-ideal extension routes. Its only square hypothesis is the corresponding square
  on the initial intrinsic schemes. Both original histories are admissible; their source
  histories are admissible by the existing pullback constructor.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` (and its Separated import):
  `AlgebraicGeometry.IsSeparated`. Properness itself is not imposed on the ambient pair.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.EmbeddedResolutionHistory`: the raw history, its actual diagrams
  and ideals, `ValueFamily`, `Admissible`, `SmoothPullback` and `IntrinsicComparison`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `.blowupMap`, used through
  the raw history's ambient blowup records.
- `WeilConjectures.Compactification.StrictTransform`: `AlgebraicGeometry.strictTransform`
  and `Scheme.IdealSheafData.strictTransform`, through the raw history's strict transforms.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: the scheme regularity notion is reused through
  the gluing dependency; point regularity is its existing `IsRegularLocalRing` stalk test.
- `Sheaf.AlgebraicGeometry.NormalizedResolutionWordGluing`:
  `HilbertSamuel.ResolutionWord`, `normalized_resolution_word_gluing`, `ResolutionWordChart`
  and its `.tail`; no replacement numerical assignment is defined.
- `Sheaf.AlgebraicGeometry.HilbertSamuelSmoothDimensionProfile`:
  `localFunction`, `summation`, `minimumComponentDimension`, `componentDimensionCount`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  the published `Scheme.IdealSheafData.vanishingIdeal` interface, and the recognition theorem
  used in the proof plan. The selected upstream module imports cleanly with all the stated
  proof dependencies; no duplicate declaration was introduced.

Public imports give the notions occurring in the statement. Ordinary imports include the
published proof-plan modules for maximum-center descent, smooth-center blowup geometry,
locally closed finite-type strata, strict-transform flat base change, blowup complements,
geometrically reduced smooth maps, going down and Noetherianity. The proof-only nodes
`def-nagata-blowup-flat-base-change-map`, `thm-nagata-blowup-flat-base-change` and
`lem-trf-reduced-flat-pullback-recognition` have no recorded module on the read base, so no
invented import is supplied for them. They remain named in the proof docstring. No statement
object depends on those absent proof-only modules.

Edge cases checked before writing and again against the final file:

- Length zero: the prefix construction and stage formulas have stage 0 and no centers.
- Empty schemes and an empty smooth source: pointwise clauses are empty; the pullback
  existence still allows length zero and deletion of every center. No nonempty assumption
  on a pair, initial scheme or smooth morphism was added.
- Pullback misses every center: `SmoothPullback.centers` forces their unit ideals and
  collapses every transition. Both intrinsic and ambient maximum ideals become `⊤`.
- Intrinsic identity blowups: `wordPrefix` keeps each original `center` and its original
  position. Deletion is determined by the ambient extended ideal, not intrinsic identity.
- Nonconstant relative dimension and nonclosed points: s is the local fibre-ring dimension
  at each y, exactly as the published smooth-dimension profile states.
- Source maximum disappears, or its inverse image is not the source's maximum:
  greatest-value hypotheses refer only to the original K. The equality remains about
  that individual inverse-image stratum; it never replaces it by a new maximum.
- Regular stages and a greatest value of bottom are not excluded. Empty original schemes
  have no attained greatest value, so no nonexistent maximum is required.
- Different ambient embeddings: intrinsic clauses have no ambient comparison or equal
  ambient dimension; all information passes through the intrinsic diagram and ideals.
- Two pullbacks: already-unit ideals remain unit; additional centers may become empty.
  Composition of deletion indices retains exactly the original chronological positions.
- Universe u is explicit throughout; the rational base is lifted to the same universe.
  `set_option autoImplicit false` rejects accidental unbound variables.

Searches performed:

1. `msearch.py ... leanfinder`:
   "Smooth pullback invariance and intrinsic embedding independence of finite resolution
   histories and normalized Hilbert Samuel words". OK, 8 hits about standard-smooth
   algebra presentations (`Algebra.IsStandardSmooth...`, `Algebra.SubmersivePresentation...`,
   `RingHom.IsStandardSmooth...`); none states this history comparison.
2. `msearch.py ... loogle`:
   `AlgebraicGeometry.Smooth, AlgebraicGeometry.IsReduced`. OK, 0 hits.
3. `msearch.py ... grep`:
   `ResolutionWord|EmbeddedResolutionHistory`, subdirectory `AlgebraicGeometry`. OK, 0 hits.
4. `rg -n 'ResolutionWord|finite.history.comparison|def .*prefix|def .*truncate' lean/Sheaf/AlgebraicGeometry`:
   found the gluing module and maximum-center descent, not this comparison or a history prefix.
5. `rg -n 'resolutionWord|EmbeddedResolutionHistory|normalized_resolution' lean/WeilConjectures`
   and `grep -rn 'lem-trf-resolution-word-finite-history-comparison' lean/WeilConjectures`:
   no hits. A subsequent capitalization/underscore search also found no upstream copy.
6. Direct reads of Mathlib `Fin.castLEOrderEmb`, `Monotone.functor`,
   `Functor.whiskerLeft`, `TopologicalSpace.Closeds.preimage` and scheme ideal interfaces
   supplied the prefix and ideal constructions. These reuse existing general operations.

Validation: `scompile.py` compiles the standalone sandbox and the final named library module.
The first attempt exposed the namespace qualification `Functor.whiskerLeft`; corrected after
reading its definition. The next attempt passed. The extended compatibility version also
passed. Final source and delivery preflight validation are recorded by the delivery wrapper.
No mathematical statement fault or `STATEMENT-DISPUTED` issue was found.

## Second reading by Q23

This is a separate second pass by the assigned worker; no sub-agent was started, as required
by the dispatcher's instructions. The maintainer supplies the independent delivery review.

I reopened the item's statement and compared its three paragraphs with the helper definitions
and theorem. The initial pair uses all six geometric hypotheses; raw histories do not assume
later smoothness. The hν binder reproduces the published gluing predicate, including singular
chart existence and every-chart computation, so the fixed word is not weakened to an arbitrary
function. I checked the actual `wordPrefix` record: its centers, ambient blowup maps and both
strict-transform maps are the original data at the same numerical indices. None are discarded
because an intrinsic blowup is an identity.

The stagewise comparison is indexed by every original stage j and evaluated on the retained
source stage `c.index j`. The dimension parameter is the dimension of the local fibre ring,
not the rank of differentials. The original maximum T is allowed to become empty or cease to
be maximal upstairs; both ideal equalities retain T. In the intrinsic clause the two ambient
schemes are entirely unrelated, while the given natural isomorphism preserves ordered center
kernels. There is no missing ambient-isomorphism hypothesis and no extra one was imposed.

This pass found that a first draft's repeated-pullback compatibility included intrinsic ideal
extension only. I added the actual final ambient comparison map and the corresponding ambient
ideal equality. I also added the intrinsic/smooth commuting-square clause so the last sentence
of the node is explicit for intrinsic comparisons as well as repeated smooth comparisons.
A redundant application-of-equal-maps value equality was removed from that square clause;
the natural map equality already supplies it. Every helper is listed in `lean.declarations`,
has the owning node's source docstring, and contains actual definitional data. No additional
DAG statement or mathematical assumption was introduced.
