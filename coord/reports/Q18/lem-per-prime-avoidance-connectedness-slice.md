## Worker report

The module `Sheaf.RingTheory.PrimeAvoidanceConnectednessSlice` states
`PrimeSpectrum.exists_zeroLocus_inter_eq_closedPoint_meeting`, with `sorry` as its
whole proof. It introduces no definitions. The item node changes only in `lean`.

The previous worker's stale-assignment diagnosis concerned Q72's stage-1 split:
the shared node has `reviewed` from Q72 but no `lean` or `reviewed_lean`. This
delivery states that reviewed split without changing or splitting it again.
There is no repair note for the item.

Hypothesis and conclusion correspondence:

- The commutative ring is `A : Type u` with `[CommRing A]`; all universes are
  explicitly bound. `[IsLocalRing A]` encodes locality and nonzeroness: its
  definition extends `Nontrivial A`, so no redundant nontriviality binder is added.
- Noetherianity is `[IsNoetherianRing A]`.
- `X = Spec A` is literally `AlgebraicGeometry.Spec (.of A)`. Mathlib's underlying
  space is definitionally `PrimeSpectrum A`, with its Zariski topology; compilation
  checks that the sets, closed point, and zero locus use this same type and topology.
- Finite dimension is `hfinite : topologicalKrullDim
  (AlgebraicGeometry.Spec (.of A)) < ⊤`. With a nonzero local ring the spectrum is
  nonempty, so this is exactly finite (nonnegative integer) dimension.
- `T` is a subset of that spectrum; `hTclosed : IsClosed T` and
  `hTnonempty : T.Nonempty` give its two specified properties.
- The nonnegative integer `e : ℕ` and `hTdim : topologicalKrullDim T = e`
  give its exact dimension, with Mathlib's subspace topology on `T`.
- The finite family is `s : ℕ` and `W : Fin s → Set (Spec (.of A))`.
  No positivity assumption on `s` is made.
- `hWnonempty` gives nonemptiness of each piece. `hWlocallyClosed` uses Mathlib's
  `IsLocallyClosed`, defined as an intersection of an open and a closed subset.
- `hWsubset` places every piece inside `{IsLocalRing.closedPoint A}ᶜ \ T`,
  exactly `U \ T`. This is open: the closed point has closed singleton, and `T`
  is closed. A subset locally closed in this open subspace is locally closed in
  `X`: write its relative closed part as the intersection with an ambient closed
  set, and its relative open part as an ambient open set intersected with the open
  subspace. Conversely ambient locally closedness restricts to any subspace.
  Thus the chosen ambient formulation neither adds nor drops a hypothesis.
- The witnesses are `f : Fin e → A`, exactly `e` elements, allowing repetitions.
  `∀ i : Fin e, f i ∈ IsLocalRing.maximalIdeal A` places every one in `m`.
- `T ∩ zeroLocus (Set.range f) = {IsLocalRing.closedPoint A}` is exactly the
  required singleton cut. The definition of `zeroLocus` is the set of primes
  containing the entire given set of elements.
- `∀ j : Fin s, (W j ∩ zeroLocus (Set.range f)).Nonempty` is exactly the
  meeting condition for each prescribed piece.

Recorded statement dependencies used, with declarations and source read:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; read its definition/docstring and
  `isNoetherianRing_iff_ideal_fg` (every ideal finitely generated).
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`; read both full
  definitions/docstrings. The map is not needed in this statement. Read also
  `Spec.topObj` in `Mathlib.AlgebraicGeometry.Spec`: it is `TopCat.of (PrimeSpectrum R)`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`; read its definition/docstring as
  `Order.krullDim (IrreducibleCloseds T)` with values in `WithBot ℕ∞`.

The available proof dependencies are Mathlib's spectrum topology, radical/ideal
operations, Noetherian-ring definitions, topological dimension, finite irreducible
components, and prime avoidance. Their modules are imported, with proof-only
imports nonpublic. `lem-per-punctured-local-closed-points` currently has no Lean
record and is not a statement dependency; no import is fabricated for it. Its
role is explicitly retained in the eight-step proof docstring. Nothing is proved.

Source reading: `literature/stacks-project/algebraization.tex`, lines 4368–4445,
Tag 0ECR, especially the second half's equations and closed-point constraints;
`literature/stacks-project/morphisms.tex`, lines 3038–3066, Tag 02J6(4), which
makes the punctured local spectrum Jacobson. The reviewed node expands the
source's two-piece argument to any finite family, with the same prime avoidance
construction; no completeness or catenarity assumption is needed by that step.

Edge cases checked before writing:

- `e = 0`: `Fin 0 → A` is the empty list; its range is empty and its zero locus
  is the full spectrum. A nonempty closed zero-dimensional subset of a local
  spectrum is exactly the closed point, so the equality and all meeting conditions
  retain the intended meaning.
- `s = 0`: all three piece hypotheses and the meeting conclusion quantify over
  the empty type; only cutting `T` remains, with no hidden witness to a piece.
- Fields and nonzero Artinian local rings: the spectrum is a singleton and its
  puncture is empty. The hypotheses force `s = 0` and `e = 0`, as expected.
- A DVR with `T` the closed point: `e = 0`; the generic-point piece survives the
  empty cut. With `T = X`, the punctured complement is empty and no pieces exist.
- `T = X` in any finite dimension is allowed; the theorem provides parameters
  whose common zero locus is the closed point. The empty `T` is excluded exactly
  as in the node. No characteristic or ring universe is restricted.

Searches (all prescribed Mathlib tools were run through `msearch.py` for Q18/item):

- `leanfinder`: “In a Noetherian local spectrum cut a nonempty closed subset of
  dimension e to the closed point by e equations while meeting finitely many
  prescribed nonempty locally closed subsets of its punctured complement”. Eight
  hits included `PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal`,
  `exist_ltSeries_mem_one_of_mem_last`, Noetherian-spectrum instances and
  `Ideal.exists_finset_card_eq_height_of_isNoetherianRing`. None states this
  simultaneous cutting and meeting assertion.
- `loogle`: `PrimeSpectrum.zeroLocus, IsLocalRing.maximalIdeal, topologicalKrullDim`:
  zero hits.
- `leansearch`: “In a Noetherian local ring finitely many elements cut a closed
  subset to the maximal ideal while their common zero locus meets a finite family
  of nonempty locally closed subsets”. Eight hits gave zero-locus definitions,
  `IsLocalRing.closedPoint`, and unrelated filtration/zero-locus identities, not
  this assertion.
- `grep` via `msearch.py`: `prime_avoidance|connectedness_slice|exists.*zeroLocus`
  in `RingTheory`: two unrelated textual hits (`Topology.lean:366` and
  `IsOpenComapC.lean:48`).
- `rg` of that pattern in the upstream `WeilConjectures` and project `lean/Sheaf`:
  unrelated zero-locus, ample-module, relative-component, and pro-etale results;
  no matching local slicing assertion. `grep -rn` for the exact item id upstream:
  no hits.
- `rg` for `connectednessSlice|exists.*zeroLocus.*closedPoint|exists.*zeroLocus.*locallyClosed|primeAvoidance`
  across Mathlib/upstream/project: only an unrelated pro-etale closed-points
  retraction theorem. The new full declaration name was also searched across those
  trees and `dag/lean_names_upstream.json`: no collision.

Validation: `scompile.py Q18 lem-per-prime-avoidance-connectedness-slice` compiled
this single file successfully as both sandbox (4.2 seconds) and library module
(2.6 seconds), with no errors or warnings. No global build was run.
No disputed statement, new node, dependency repair, or statement correction.

## Second reading by Q18

Author's separate self-check, not a claim of an independent second reader (the
maintainer supplies independent review). Reopened the JSON statement and full
module after compiling. Matched the ring/local/nonzero/Noetherian/finite-dimension
assumptions, the closed nonempty subset and its exact dimension, each of the three
piece hypotheses, and all three witness clauses as listed above. In particular
`Fin e` gives exactly `e` equations, `Fin s` admits zero pieces, and neither the
locally closed condition nor the complement removes generic points or imposes
closedness in the full spectrum. Confirmed that `IsLocalRing` itself includes
nonzeroness and that the ambient locally closed formulation is equivalent because
the containing subspace is open. All eight proof steps of the reviewed node are
in the theorem docstring, including the zero-component fallback and both empty
index cases. Only a syntax parenthesis was corrected before the successful compile;
no mathematical mismatch, change of node statement, or duplicate notion was found.
