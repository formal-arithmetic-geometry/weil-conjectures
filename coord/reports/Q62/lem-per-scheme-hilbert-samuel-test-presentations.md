## Worker report

Item: lem-per-scheme-hilbert-samuel-test-presentations. Module:
`Sheaf.AlgebraicGeometry.SchemeHilbertSamuelTestPresentations`, namespace
`AlgebraicGeometry.HilbertSamuel`. All 19 theorems have exactly `by sorry` proofs.
No definitions, axioms, new nodes, dependency repairs, or statement corrections are introduced.
The original node is changed only in `lean`.

Source read: BMT arXiv:0905.3580v1, sections 5.1--5.2 and 6.1--6.3,
https://arxiv.org/html/0905.3580 . The local archival PDF is absent, as the node already
records. The online source explicitly defines varieties as finite-type schemes, without
requiring reducedness. The blueprint was searched only in `literature/blueprint/latest/`;
this auxiliary node is not itself a blueprint unit statement.

Hypotheses and clauses, in order:

- Schemes of finite type over Q: the base is `Spec (.of (ULift.{u} ℚ))`, with `universe u`
  explicit. `LocallyOfFiniteType` and `QuasiCompact` on the structure morphism express
  finite type; `IsImmersion i` expresses the locally closed embedding, and `Smooth p`,
  `LocallyOfFiniteType p`, `QuasiCompact p` give the smooth finite-type envelope.
  No declaration assumes `IsReduced`, generic reducedness, or a closed point.
- The raw sequence, inclusive sum, and transcendence-degree extension are exactly the
  existing `localFunction`, `summation`, and `function` of `HilbertSamuelInvariant`.
  The finite-length clause of `scheme_function_local_finite_upperSemicontinuous` ensures
  that its natural conversion is literal. Its second clause is global finite image,
  `(Set.range (function (i ≫ p))).Finite`; its third clause is closed upper level sets
  for the existing lexicographic `le`.
- Smooth constant-level blowup nonincrease is `scheme_function_nonincrease`, using
  `LocallyConstantCenter`, the actual center blowup and scheme-theoretic `strictTransform`.
  It holds on the entire strict transform, hence in particular over the center and under
  the additional normal-crossings restrictions of a permissible test.
- `scheme_function_reachable_stabilizes` quantifies over all levels realized after
  `Relation.ReflTransGen BlowupTransition` from the same initial finite-type smooth
  ambient input. It asserts eventual equality for a decreasing sequence. Thus arbitrary
  finite histories, subsequences, plateaus, and zero blowups are included. The separate
  `scheme_function_no_infinite_drops` is its consecutive-history specialization.
- Local existence is `scheme_local_presentations`, using `LocalPresentationAt p i x`.
  `scheme_local_presentations_surjective` spells out a chart `f : S.Z ⟶ V.toScheme`,
  `Etale f`, `Function.Surjective f`, `i x ∈ V`, its cartesian identification with the
  intrinsic scheme, specified lift `g a = x`, intrinsic level, `Presents M`, and the
  maximal-level bound everywhere on the chart.
- The support, coherence, positive mark and order cosupport are precisely `Marked`,
  `Marked.cosupport`, and `Presents` from the recorded dependency. `Marked` contains
  smooth closed `N`, its coherent finite-type quasi-coherent ideal, and positive mark;
  smoothness makes its support locally Noetherian, so the recorded coherent interface
  agrees with `RingedSpace.IsCoherent`. No substitute coherence predicate is introduced.
- All finite tests are the existing `Step`, `Step.Transforms`, `PresentsThrough` and
  `Presents`. Admissible tests use smooth normal-crossings centers and controlled
  transforms; line tests pull back and sum the level, and exceptional tests use the
  ordinary pullback convention of the dependency. `scheme_presentation_finite_history`
  explicitly quantifies over all finite prefixes and every subsequent test depth.
- The item's strict-transform convention for exceptional tests is explicitly covered by
  `scheme_exceptional_strict_retaining_locus`: after any finite permissible prefix, the
  image of the retaining locus of the actual scheme-theoretic strict transform equals
  `T.locus`, computed by the ordinary-pullback test. Thus the difference in scheme
  conventions is not silently discarded. Admissible blowups already use strict transform.
- `scheme_presentation_empty_level` makes empty final cosupport exclude the specified
  final level after any finite tests. `scheme_presentation_empty_maximum` additionally
  gives a strict drop below the original maximum for an admissible blowup history.
- `scheme_local_minimal_presentations` supplies a local minimal envelope;
  `scheme_presentation_full_maximalOrder` assumes `MinimalAt S x` and the nonregular
  local ring `¬ IsRegularLocalRing ...`, and concludes etale-local equivalence with
  `FullMaximalOrder Q`. This predicate says `IsIso Q.j` and order exactly its mark at
  every cosupport point. It deliberately imposes no finite-order claim on regular germs.
- `scheme_presentation_intrinsic_comparison` compares minimal envelopes of the same
  pointed intrinsic scheme using `CommonComparison`, actual cartesian squares and
  ordered earlier intrinsic center ideals mapped into the respective envelopes.
  Its conclusion supplies actual marked pullbacks and `Equivalent M' P'`.
- `scheme_presentation_history_comparison` does the same for any supplied pointed common
  etale comparison and its already identified earlier lists, without requiring minimality
  anew at a transformed stage. The predicate quantifies over all finite subsequent tests.
- `scheme_function_smooth_pullback` gives extended summation by relative dimension on
  every constant-relative-dimension piece. `scheme_localFunction_smooth_pullback` instead
  uses an arbitrary point `y : f.fiber x`, the dimension of its actual fibre local ring,
  and gives `localFunction Y ... = (summation^[s]) (localFunction X x)`. It does not
  conflate fibre-local dimension with the relative dimension, or identify residue fields.
- `scheme_presentation_smooth_pullback` supplies actual `MarkedPullback` data, the inverse
  image retaining locus, and presentation for every such pullback. Its finite-test
  quantifiers include centers upstairs that do not descend.
- `scheme_presentation_intrinsic_smooth_charts` handles an intrinsic smooth `f : Y ⟶ X`
  through local embeddings: a cartesian etale target localization, a pointed etale chart
  over Y, an actual smooth ambient lift `F`, cartesian embedded schemes and
  `q ≫ gX = gY ≫ f`. It supplies presentations and marked pullback, both correct
  intrinsic levels, and actual pullback of every earlier ideal in its original order.
  Smooth maps of varying relative dimension are treated on their locally constant pieces.
- `scheme_presentation_smooth_comparison` compares possibly different envelope dimensions
  on a common smooth extension: `Pullback f r` and `Pullback g s` impose the respective
  summations, and equality of the pulled-back earlier ideal lists retains their order.
  It concludes `Equivalent` for actual marked pullbacks. Equal-dimensional common etale
  comparison is supplied by the intrinsic/history comparison theorems, not an assertion
  that different dimensional envelopes have a common etale cover.
- History and birth data use the original ordered earlier ideals, including unit ideals
  of intrinsic identity stages. They remain separate from `S.boundary = []` in a newly
  chosen `Presents`; test boundaries are transformed using the existing ordered lists.
  The finite-history theorem preserves the existing boundary and does not reset it.
  No numerical resolution word, choice of global maximum center, or resolution algorithm
  is asserted.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`; its immersion
  clause is `IsImmersion` in `Morphisms.Immersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `Morphisms.QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `SmoothOfRelativeDimension`;
  `Morphisms.Etale`: `Etale`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `WeilConjectures.Compactification.StrictTransform`: `strictTransform`, `strictTransformMap`,
  `strictTransformToSource`, and the center-specific `IdealSheafData.strictTransform`.
- `Mathlib.RingTheory.Length`: `Module.length`; `RingTheory.AlgebraicIndependent.Basic`:
  `Algebra.trdeg`; `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`. These are used in the recorded invariant, not redefined.
- `Sheaf.AlgebraicGeometry.HilbertSamuelPresentation`: `Embedded`, `Marked`, `Step`,
  `Step.Transforms`, `PresentsThrough`, `Presents`, `Equivalent`, `Pullback`, `MarkedPullback`,
  `MinimalAt`, `FullMaximalOrder`, `CommonComparison`, `LocallyConstantCenter`,
  `BlowupTransition`, and `LocalPresentationAt`; all signatures and docstrings were read.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: `Scheme.Modules.IsQuasiCoherentFiniteType`
  and exposed `RingedSpace.IsCoherent`; `Sheaf.AlgebraicGeometry.MarkedIdealOrder`:
  `stalkIdeal` and `order`; `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`,
  exposing the regular local-ring notion used in the singular-germ hypothesis.
- The invariant is publicly available from the presentation dependency. Its owning node is
  `def-trf-hilbert-samuel-invariant`, already transitively cited; no new definition is needed.
- Every currently recorded proof-dependency module is imported privately unless already
  public for the statement. The seven proof nodes without a recorded declaration are
  not restated or imported; their proof steps remain explicitly documented for stage 3.

Searches:

- `msearch.py ... leansearch "Hilbert Samuel function presentation marked ideal smooth blowup"`:
  eight generic smoothness hits, no presentation theorem.
- `msearch.py ... leanfinder "Hilbert Samuel function finite image upper semicontinuous marked
  ideal presentation scheme nilpotents smooth blowups"`: eight generic smooth/local-algebra
  hits, no theorem matching this node.
- `msearch.py ... loogle "HilbertSamuel, AlgebraicGeometry.HilbertSamuel.Presents,
  IsRegularLocalRing"`: zero hits, unknown identifier HilbertSamuel in the search index.
- `msearch.py ... grep "HilbertSamuel|hilbertSamuel|hilbert.samu" AlgebraicGeometry`: zero hits.
- `rg` in Mathlib RingTheory and `lean/WeilConjectures` for HilbertSamuel/hilbertSamuel:
  no presentation statement. Broader Hilbert searches find unrelated Hilbert functors and
  Hilbert 90. The exact item-id search in `lean/WeilConjectures` has no match.
- `rg` in `lean/Sheaf` finds `HilbertSamuelLocalPresentations` and
  `HilbertSamuelReachableLevels`. These require `IsReduced X`, so neither states this node.
  Their common notions are reused, while the reduced hypothesis is absent here. The new
  theorem names were searched and have no collision. The relevant DAG records and their
  declaration source/docstrings were read, including the reachable-level interface repair.

Edge cases checked before and during writing:

- Empty X: numerical finite image is empty and all quantified point claims are vacuous;
  no nonempty hypothesis or chart point is introduced without a given point.
- Nilpotents: a double point defined by z^2 keeps its actual local length sequence; none
  of the statements replaces it by its reduction, and no `IsReduced` binder remains.
- Regular codimension-zero germ and zero coefficient ideal: order is infinite, so full
  finite maximal order is asserted only under the nonregular local-ring hypothesis.
- Nonclosed points: residue transcendence degree remains in `function`; fibre-local
  dimension and relative dimension use different formulas as required.
- Mark b is positive because `Marked.positive` is part of the actual data; empty coefficient
  families allow the zero ideal marked by one in the proof, not an impossible positive order.
- Depth zero, zero-length history, no earlier ideals and identity stages are allowed.
  `ReflTransGen` includes reflexivity, so plateaus and separated strict drops are covered.
- Relative dimension zero gives identity summation and includes etale/open localizations;
  all universes and variables are explicitly bound with `autoImplicit false`.

No STATEMENT-DISPUTED flag or node fault remains. The exceptional-pullback distinction is
handled by an explicit theorem rather than silently changing the dependency convention.

Validation: prescribed `scompile.py` only, separately compiling the module in sandbox and
library mode against the live published build, initially 3.2/3.3 seconds and after adding
the intrinsic smooth chart statement 2.7/2.6 seconds. Final import and delivery checks follow.

## Second reading by Q62

This is the worker's own second pass with both the JSON node and the complete Lean file
open; the maintainer supplies the independent reading after delivery. No other agent was
started, as required by the dispatcher brief.

The pass found and removed the inherited reducedness assumptions from the comparison
module template. It replaced merely local finite image by global finite image, added
surjectivity over a specified open neighbourhood and the maximum-level bound, and added
reachable-history stabilization rather than only forbidding consecutive strict drops.
It distinguished the raw fibre-local summation formula from extended relative-dimension
summation. It added explicit exceptional strict-transform retaining-locus equality, finite
history and empty-level assertions, smooth common-extension comparison, and the pointed
intrinsic smooth ambient lift with actual ordered earlier-ideal pullback. All nineteen
signatures were checked against the clause mapping above. No node statement was changed,
no private replacement of a recorded notion was introduced, and every theorem proof is
exactly `by sorry` with the relevant original natural-language proof steps in its docstring.
