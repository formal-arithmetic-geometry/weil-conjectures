## Worker report

Item: lem-trf-resolution-word-progress-termination. The single module is
`Sheaf.AlgebraicGeometry.ResolutionWordProgressTermination`. Its primary declaration is
`AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_termination`; its nine
named theorem statements together render all clauses of the node. Every theorem has only
`sorry` as its proof. The five helpers have real definitions or structure/inductive data.
Only the item's `lean` field is changed. There are no new nodes or dependency repairs.

The source read was ILO VIII, printed pp. 92–93, especially Remark 2.3.11: discard
exceptional cleanup and keep only the singular-locus part of the ordinary algorithm.
Remark 2.3.5(ii) describes synchronization with empty stages on a fixed finite family.
The cited detailed BMT input is still marked WANTED in the DAG; this delivery assembles
the already recorded numerical-engine, presentation, profile, gluing and center interfaces,
without claiming a new source proof. I also read the current blueprint's
`sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`: it now uses
Varshavsky, as the accepted split report already records. This historical auxiliary node
is not a correction of that blueprint unit.

Hypotheses, with the node and the source signatures open:

- Over Q and arbitrary scheme universe: `EmbeddedResolutionPair.{u}` uses
  `Spec (.of (ULift.{u} ℚ))`; this changes size only. There is no universe-zero restriction.
- Closed embedding: `A.inclusion` and `A.closed : IsClosedImmersion A.inclusion`.
- Reduced initial scheme: `A.reduced : IsReduced A.X`.
- Smooth, separated finite-type ambient: `A.smooth`, `A.separated`, `A.finiteType` and
  `A.quasiCompact`. Finite type is `LocallyOfFiniteType` and `QuasiCompact`, as recorded.
  There is no properness assumption: the proper-morphism node also owns separatedness.
- Empty schemes and finite disjoint unions are included: neither the pair nor any theorem
  imposes nonemptiness, connectedness, integrality, equidimensionality or a fixed dimension.
- The fixed assignment: `R : MarkedIdeal.NumericalResolution.{u}` and `ν`, with
  `hν : IsNormalizedResolutionWord R ν`. That predicate is verbatim the entire output
  property of `normalized_resolution_word_gluing`, including the existence of genuine
  charts at every singular point, leading one, every representative's actual engine word,
  finite image, closed upper levels, bottom exactly at regular points and comparison under
  summation. It is not a freely assumed order-decreasing function.
- Raw stages: `EmbeddedResolutionHistory A n` retains the actual blowup isomorphisms,
  ideal centers and schematic strict transforms. `Extension` identifies the full preceding
  diagram and every old ideal in chronological order.
- Admissibility: `Admissible ν H`; process reachability from empty initial history is
  `MaximumHistory ν H`, using only the already defined `IsMaximumStep` and `Extension`.
- Geometric stage hypothesis: `HasResolutionGeometry H` names exactly ambient smoothness,
  separatedness, finite type and reducedness of the current strict transform. It is not
  built into raw histories. Nonregularity is `¬ IsRegularScheme H.X`.

Conclusions, clause by clause:

1. The reduced full positive maximum is the existing `IsMaximumStep ν E`: an attained
   greatest word greater than bottom, a reduced center, and equality of its entire image
   with the word equality stratum. `resolution_word_progress` asserts existence of a next
   such extension from a nonregular stage and preservation of `HasResolutionGeometry`
   for every such extension. Thus reducedness is not silently imposed on later raw stages.
2. Permissibility for local presentations is `resolution_word_permissible`. Every point
   of the actual global center has an actual `ResolutionWordChart R H x`, its etale
   `finalMap`, and an actual `MarkedIdeal.Extension` which is an engine maximum step.
   The center is reduced, has `HasAdaptedNormalCrossingsCenter` with the ordered boundary,
   and a closed immersion `c` whose triangle commutes and whose ideal satisfies
   `c.ker = E.centerMap.ker.comap C.finalMap`. This is scheme-theoretic ideal identification,
   including when the step removes the head altogether.
3. Strict word progress: the second clause of `resolution_word_progress` says `m' < m`
   for attained greatest old/new words when the new scheme is nonregular. The current
   finite-image gluing theorem guarantees greatest words in that case; no supremum is used.
4. Head nonincrease: `resolution_word_head_nonincrease` compares the normalized heads
   pointwise along `E.resolutionMap`, the canonical recorded strict-transform projection.
   It also compares attained greatest heads, after adjoining bottom to include the empty
   scheme: `b ≤ a`. The underlying normalized head is reused, not redefined.
5. Only finitely many strict head changes for a fixed input:
   `resolution_word_finitely_many_head_drops` rules out an infinite strictly descending
   sequence of attained greatest heads of `MaximumHistory` prefixes of the same `A`.
   Prefix lengths may have arbitrary finite gaps. Thus this includes the subsequence after
   successive strict changes, rather than only excluding a drop at every adjacent stage.
6. Exact constant-head evolution: `resolution_word_constant_head_presentations` quantifies
   over every finite interval starting at any length `n`, its actual extensions, and a fixed
   attained greatest singular head `a` with `regularHead < a`. Its conclusion supplies
   `HeadIntervalPresentations`, a finite family of actual starting word charts continued
   by controlled marked-history extensions. The starting histories and maps are identified
   by `initial`, `chartLength` and `initialMap`; no older history is erased to synchronize
   their possibly different lengths. `MarkedIdeal.Extension` preserves states, steps and
   birth data. `transitionSquare` and `cartesian` pin the continued intrinsic charts to
   the canonical global strict transforms. `cosupportSquare`, `retained` and `cover` say
   exactly that cosupport is the retained-head locus on a fixed covering family.
   `word` and `leadingOne` use the same actual engine words with precisely `.drop 1`.
   `centers` identifies actual pulled-back ideals. `synchronized` takes the attained tail
   maximum over the whole finite family and identifies each selected center with its
   full maximum locus; a patch with no global maximum has empty center. Smoothness,
   adapted normal crossings and controlled ideal transforms are already data of every
   `MarkedIdeal.HistoryStep`, and are not replaced by an arbitrary map or existence choice.
7. Empty cosupport removes the head: `resolution_word_empty_cosupport_removes_head` says
   every final point has normalized head different from `a` if every final local cosupport
   is empty. It follows from the exact retained-locus and covering clauses, even without
   a maximum-head hypothesis. This is also the intended presentation property when a
   head has just disappeared. There is no false claim of head retention after emptying.
8. No infinite constant-head interval: `resolution_word_no_constant_head_tail` starts
   at any finite length `n`, retaining admissibility and geometry at that point, and
   rules out the same attained singular greatest head at every later maximum step.
9. No infinite sequence from empty initial history: `resolution_word_termination` rules
   out `H : ∀ n, EmbeddedResolutionHistory A n` with compatible `E n` and all maximum
   steps. The stage-zero history is necessarily empty. No completed finite resolution
   tower or termination hypothesis is supplied as input.
10. Regular or empty initial input: `resolution_word_zero_extensions` takes exactly
    `IsRegularScheme A.X ∨ IsEmpty A.X` and excludes a first maximum extension for
    every empty initial history. Consequently such inputs have zero extensions.
11. Scope of the conclusion: none of the theorems asserts `WellFounded` on
    `HilbertSamuel.ResolutionWord` or termination of arbitrary descending words. Both
    descending-chain and infinite-process statements are restricted to this fixed
    normalized construction and one fixed input.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion` (closed
  embedding and surjective stalk maps); `Mathlib.AlgebraicGeometry.Properties`:
  `IsReduced` (all section rings reduced).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`; the proper-morphism dependency
  records `Mathlib.AlgebraicGeometry.Morphisms.Proper`, which supplies the imported
  separatedness interface `IsSeparated` defined by the closed diagonal. No `IsProper`
  condition was inserted. `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`, exactly
  `IsLocallyNoetherian X ∧ IsRegular X`, including both parts of the recorded notion.
- `Sheaf.AlgebraicGeometry.EmbeddedResolutionHistory`: `EmbeddedResolutionHistory`,
  `Extension`, `Extension.centerMap`, `ValueFamily`, `IsMaximumStep`, `Admissible`.
  Its imported `Sheaf.AlgebraicGeometry.LabeledEmbeddedResolution` provides
  `EmbeddedResolutionPair` with precisely the initial geometric data.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`;
  `WeilConjectures.Compactification.StrictTransform`: `strictTransform`,
  `strictTransformToSource`, and the ideal-sheaf specialization of `strictTransform`.
  These are the actual constructions already used by the history interfaces.
- `Sheaf.AlgebraicGeometry.NormalizedResolutionWordGluing`:
  `normalized_resolution_word_gluing`, `ResolutionWordChart`, its `.word`/`.tail`, and
  `HilbertSamuel.ResolutionWord`. `Sheaf.AlgebraicGeometry.ResolutionWordMaximumCenterDescent`:
  `resolution_word_maximum_center_descent` and `ResolutionWordChart.finalMap`.
- Proof interfaces: `HilbertSamuel.local_presentations` and the retained-level
  interface reexported by `Sheaf.AlgebraicGeometry.HilbertSamuelReachableLevels`;
  `Sheaf.AlgebraicGeometry.HilbertSamuelSmoothDimensionProfile`:
  `normalizedHead`, `regularHead`, `modifiedHead_nonincrease`,
  `modifiedHead_no_infinite_drops`, `modified_presentation_empty_maximum`;
  `Sheaf.AlgebraicGeometry.MarkedIdealNumericalResolutionEngine`:
  `MarkedIdeal.exists_numerical_resolution`, using the actual `NumericalResolution`
  and controlled histories of `MarkedIdealInvariantData`/`MarkedIdealData`;
  `WeilConjectures.AlgebraicGeometry.Regular`: `smooth_of_isRegular`;
  `Sheaf.SecTraceFormula.SmoothCenterBlowupGeometry`: `smooth_center_blowup_geometry`.
  The latter source declaration is currently universe zero; the mathematical chart proof
  is size-independent. This statement module keeps the general universe of the actual
  pair/history and gluing interfaces instead of imposing a false universe equality.

Searches for an existing statement and helper names:

- `msearch.py ... leanfinder`: “The normalized Hilbert Samuel and marked ideal resolution
  word strictly drops under maximum center blowups and this process terminates”. Eight
  results about prime chains, adic filtrations and local cohomology; no resolution process.
- `msearch.py ... loogle`: `"HilbertSamuel", "resolution"`. No hits.
- `msearch.py ... grep`: `resolution.*word|desingulariz|marked.ideal`, subdirectory
  `AlgebraicGeometry`. No Mathlib hits.
- `msearch.py ... leansearch`: “Termination of desingularization by blowing up maximum
  strata of a normalized Hilbert Samuel and marked ideal invariant”. Eight results on
  normalization and polynomial normalization, not the stated resolution algorithm.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for normalized words, resolution word
  progress/termination and this blueprint id: only the existing gluing and maximum-center
  modules are relevant; no existing declaration states this result. An exact blueprint-id
  search in the source root has no result. `rg` also checked every introduced full-name
  component and `dag/lean_names_upstream.json`; `resolutionMap` occurs in unrelated
  namespaces, but no new full declaration name collides. All actual mathematical notions
  (heads, words, controlled transforms, centers, histories) are reused. The five helpers
  only name this node's fixed-word hypothesis, geometric induction condition, process
  prefixes, canonical projection and finite interval continuation, under the same-node
  helper authorization; they do not introduce an independent missing mathematical notion.

Edge cases checked: empty X with nonempty ambient; both empty; regular input; dimension
zero; regular plus singular components of different dimensions; intervals of length zero;
finite local families with patches missing the global center; a step emptying the retained
head; distinct initial local history lengths; head plateaus separated by drops. Greatest
word assumptions are used only for actual attained values; empty head comparisons adjoin
bottom. No empty scheme is forced to have an attained nonbottom value. No statement
correction or disputed mathematical assertion is needed.

## Second reading by Q31

Author's separate rereading with the node and full module open, not an independent agent
review: the dispatcher explicitly prohibits starting another agent; the maintainer provides
the independent review of the delivery. I checked each hypothesis and clause against the
mapping above. The rereading caught two presentation hazards and fixed them: the local
ambient transition must transport the last recorded `MarkedIdeal.Extension.states` equality,
and the empty-stage head comparison must use the actual `WithBot` coercion rather than
`Option.some` with the wrong inferred instance. Separating a local chart's length into a
field with `chartLength` and explicitly binding all interval indices removed an elaboration
heartbeat failure without raising any compiler limit. The next compile passed; its single
long-line warning was repaired. I then made local permissibility an explicit theorem, since
progress of the global word alone would omit that clause when a head disappears. The
fixed-word input is the full gluing output, the process starts at length zero, and the
constant-head comparison retains all earlier centers and identifies ideals rather than
only sets. Every postponed theorem carries its source, this node id and a natural-language
proof covering the corresponding node proof steps. No independent second reading is claimed.
