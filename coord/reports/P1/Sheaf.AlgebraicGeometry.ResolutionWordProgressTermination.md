## What changed

Filled four proof bodies in `Sheaf.AlgebraicGeometry.ResolutionWordProgressTermination`,
without changing any existing declaration signature, definition, visibility, or public import.

* `resolution_word_permissible` applies maximum-center descent. Uniqueness of the greatest
  value identifies the extension's center support with the descended closed stratum;
  reducedness identifies its actual kernel ideal with that stratum's vanishing ideal.
  Rewriting this equality preserves all the supplied local histories and boundary conditions.
* `resolution_word_empty_cosupport_removes_head` uses the covering and retained-locus fields
  to turn any purported surviving point into an element of an empty cosupport.
* `resolution_word_termination` inductively obtains admissibility, MaximumHistory, and
  geometry. A proved private helper obtains an attained greatest singular head from the
  positive maximum word, the fixed charts, and `normalizedHead_regular`. Another proved
  private helper shows that an antitone sequence with no strictly descending selection of
  values has a constant final tail. The existing head-drop and constant-tail statements
  then exclude the hypothetical infinite run. These constituent geometric statements are
  still open, as listed below; no additional geometric result is assumed.
* `resolution_word_zero_extensions` transports regularity or emptiness along the recorded
  initial intrinsic isomorphism and contradicts the required positive attained maximum.

Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic` for the proved
`Scheme.Hom.ker_eq_vanishingIdeal` lemma. Updated the item's node proof to match these
arguments, retaining the plans needed by the five remaining holes. No other existing
module or node was changed. The reduced-induced-closed-subscheme dependency is used as
an ideal-identification tool already underlying maximum-center descent; it does not replace
the unit route.

Validation: the final single-file server compile succeeded in 5.2 seconds with no
errors or warnings. The added proof import passes the import-direction check.

## Proved and sorry left

Closed 4 of the original 9 holes, by complete Lean proofs from the existing declarations:

* `AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_permissible`
* `AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_empty_cosupport_removes_head`
* `AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_termination`
* `AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_zero_extensions`

Five unchanged named theorem holes remain, all on node
`lem-trf-resolution-word-progress-termination` with their original source and proof docstrings:

* `AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_progress`
* `AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_head_nonincrease`
* `AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_finitely_many_head_drops`
* `AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_constant_head_presentations`
* `AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_no_constant_head_tail`

Added 0 holes and split off 0 statements. Both new private helpers are fully proved. In
particular the termination proof still depends on the listed existing geometric holes;
this delivery does not claim that the whole resolution algorithm is sorry-free.

## No longer needed

Removed the following proof-only imports, unused by the four completed proofs:

* `Sheaf.AlgebraicGeometry.HilbertSamuelReachableLevels`
* `Sheaf.AlgebraicGeometry.MarkedIdealNumericalResolutionEngine`
* `Sheaf.SecTraceFormula.SmoothCenterBlowupGeometry`

The first two remain available transitively through public statement dependencies. Their
DAG nodes and the smooth-center geometry node remain needed for the unproved geometric
clauses, so no node or module is withdrawn or claimed globally pruned. Every public import
is preserved.

## Where the brief, the DAG or earlier work was wrong

The main termination assembly does not need a separate well-foundedness theorem for the
whole head or word alphabet. A recursively chosen descending sequence of attained heads
contradicts exactly the already stated reachable-head condition.

The remaining geometric assembly is not a direct application of the cited APIs:
`smooth_center_blowup_geometry` is restricted to `Scheme.{0}` over `Spec ℚ`, whereas the
item is universe-polymorphic over `Spec (ULift ℚ)`. Also, the engine's synchronized
termination API uses local histories of a common length n and `PatchedPresentations`
with ambient open charts, whereas `HeadIntervalPresentations` permits different initial
history lengths and supplies intrinsic etale maps. These are interface gaps to bridge,
not grounds to change the item's statements. No statement is marked disputed and none
is weakened. The five remaining proof plans and dependencies are retained.

Read ILO VIII Remarks 2.3.5(ii) and 2.3.11 (printed pp. 92--93) in the supplied PDF,
and the latest blueprint unit record. Searches via LeanFinder, Loogle, and Mathlib grep
found general order results but no shorter geometric resolution theorem. The private
order helper proves only stabilization of this particular sequence, without assuming a
well-founded alphabet.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
