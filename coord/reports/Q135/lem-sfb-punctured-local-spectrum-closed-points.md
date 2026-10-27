## Worker report

Bind `lem-sfb-punctured-local-spectrum-closed-points` to the exact existing declaration
`PrimeSpectrum.exists_isClosed_singleton_of_isLocallyClosed_punctured` in
`Sheaf.RingTheory.PuncturedLocalClosedPoints` (source file
`lean/Sheaf/RingTheory/PuncturedLocalClosedPoints.lean`, lines 55–62).
No Lean module is added, no statement is corrected, and only the item's `lean` record changes.
The signature is copied verbatim, preserving its line breaks, up to `:=`.

Read Stacks Properties `lemma-complement-closed-point-Jacobson`, Tag 02IM (1)
(properties.tex lines 818–858), including its direct proof, and Morphisms
`lemma-ubiquity-Jacobson-schemes`, Tag 02J6 (4) (morphisms.tex lines 3039–3061).
These assert that the punctured spectrum of a Noetherian local ring is Jacobson;
the conclusion here is its nonempty locally closed subset characterization (005U).
Read the existing declaration's entire signature and proof-plan docstring both
locally and from the current server with
`scompile.py --source Sheaf.RingTheory.PuncturedLocalClosedPoints`.

Hypothesis and clause correspondence:

- The arbitrary commutative ring A is `(A : Type u) [CommRing A]`, with explicit
  `universe u` in the owning module. No size or characteristic restriction is imposed.
- Noetherianity is `[IsNoetherianRing A]`, the recorded declaration of
  `def-weil-pbc-noetherian-ring`, from `Mathlib.RingTheory.Noetherian.Defs`.
  Read its docstring, definition, `isNoetherianRing_iff`, and
  `isNoetherianRing_iff_ideal_fg`: exactly every ideal is finitely generated.
- Locality and A nonzero are `[IsLocalRing A]`. Mathlib's class extends
  `Nontrivial A` (LocalRing/Defs.lean:30); it encodes the usual unique maximal
  ideal condition. The nonzero hypothesis is therefore present without a redundant binder.
- X = Spec A is `AlgebraicGeometry.Spec (CommRingCat.of A)`, the recorded
  `def-weil-affine-spectrum` declaration from `Mathlib.AlgebraicGeometry.Scheme`.
  Read `Spec`, `Spec.map`, and `Spec.topObj`; the underlying space is definitionally
  `PrimeSpectrum A` with its Zariski topology.
- The unique maximal ideal m, as a point, is `IsLocalRing.closedPoint A`.
  Its definition in `Mathlib.RingTheory.Spectrum.Prime.Topology` is
  `⟨maximalIdeal A, (maximalIdeal.isMaximal A).isPrime⟩`.
- U = X minus {m}, with the subspace topology, is the literal subtype
  `{x : AlgebraicGeometry.Spec (CommRingCat.of A) | x ≠ IsLocalRing.closedPoint A}`.
  This uses the existing subtype topology; it introduces no second definition.
- A subset W of U is `(W : Set {x : ... | x ≠ ...})`; its nonemptiness is
  `(hW : W.Nonempty)`.
- The locally closed hypothesis is `(hWlc : IsLocallyClosed W)` from
  `Mathlib.Topology.LocallyClosed`. Read its actual definition in
  `Mathlib.Topology.Defs.Basic`: `∃ U Z, IsOpen U ∧ IsClosed Z ∧ W = U ∩ Z`.
  All these sets and topology predicates are in the punctured subspace.
- The conclusion `∃ w ∈ W, IsClosed ({w} : Set {x : ... | x ≠ ...})` says both
  that w belongs to W and that its singleton is closed in U. It does not assert
  closedness in X. There are no additional hypotheses or conclusions.
- When U is empty, there is no W with `W.Nonempty`; this case is retained vacuously.

Edge cases checked mathematically: for a field or a nonzero Artinian local ring,
U is empty. For a DVR, U consists of its generic point; it is closed in U but
usually not in X, precisely matching the type of the conclusion. For a local
ring of dimension at least two, no finiteness or discreteness of U is assumed.
Nilpotents and reducible spectra are allowed (for example k[[s,t]]/(st)); no
domain, reducedness, excellence, or Jacobson-ring assumption appears.

Searches actually run in this assignment:

- `msearch.py ... leanfinder` with query "Every nonempty locally closed subset of
  the punctured spectrum of a Noetherian local ring contains a point whose
  singleton is closed in the punctured spectrum": eight hits, including
  `nonempty_inter_closedPoints`, `jacobsonSpace_iff_locallyClosed`,
  `PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing`,
  `IsLocalRing.isClosed_singleton_closedPoint`, and
  `PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal`. These do not themselves
  provide the assertion for a merely Noetherian local ring.
- `msearch.py ... loogle "PrimeSpectrum, IsLocalRing, IsClosed"`: one hit,
  `IsLocalRing.isClosed_singleton_closedPoint`; this concerns the removed point.
- `msearch.py ... grep "punctur|closedPoint|[Jj]acobson" RingTheory/Spectrum/Prime`:
  15 hits in Module, Jacobson, LTSeries and Topology; no exact Mathlib statement.
- `msearch.py ... leansearch "The punctured spectrum of a Noetherian local ring
  is Jacobson"`: eight hits concerning Jacobson rings and Noetherian spectra,
  rather than this punctured-space assertion.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for punctured/Jacobson,
  the item id, and then `exists_isClosed_singleton_of_isLocallyClosed_punctured`:
  found the exact theorem in `Sheaf.RingTheory.PuncturedLocalClosedPoints`;
  no occurrence of this item's id in upstream WeilConjectures.
- `rg` over `dag/nodes` for that theorem and its module identified the owning
  node `lem-per-punctured-local-closed-points`. Its current `reviewed_lean`
  explicitly records the Q134 restoration on 2026-10-24 and recommends binding
  this DAG twin with `existing: true`.

The existing module's historical proof plan uses the other node's dimension route;
this item's accepted eight-step proof and proof dependencies remain untouched.
Its conclusion is nevertheless exactly the same proposition, so one-definition-per-notion
requires reuse. The owning module was historically on the drop list, but the current
server source exists and Q134's reviewed restoration explicitly confirms its live reuse.
No dropped DAG node is added as a dependency. No mathematical statement fault or
STATEMENT-DISPUTED finding.

Validation: the prescribed dry run checks the existing declaration with a real server
`#check` using scompile.py and runs the server preflight. No new Lean files need compiling.

## Second reading by Q135

No independent second worker was started: the dispatcher explicitly forbids subagents,
and the current delivery procedure assigns the independent reading to the maintainer.
A separate self-check against the opened node and theorem found exact correspondence:
CommRing, Noetherian, local and nonzero; the actual Spec subtype excluding the maximal
ideal; W nonempty and locally closed in U; and a member with singleton closed in U.
The field and DVR checks distinguish the vacuous case and the required ambient topology.
No signature mismatch was found and no statement change was made.
