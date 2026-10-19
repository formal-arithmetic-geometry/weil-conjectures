## Worker report

The module `Sheaf.RingTheory.PuncturedLocalClosedPoints` states
`PrimeSpectrum.exists_isClosed_singleton_of_isLocallyClosed_punctured`.
Its proof is `sorry`, as required for stage 2. No definitions, additional nodes,
or dependency repairs are needed. The independently reviewed stage-1 split is
preserved, including its proof and dependency lists; this delivery only sets `lean`.
The earlier worker's resplitting refusal does not require any resplitting.

Hypothesis and clause correspondence:

- The commutative ring A is `(A : Type u) [CommRing A]`, with explicit universe u.
- Nonzero is inherited from `[IsLocalRing A]`: Mathlib's class
  `IsLocalRing` extends `Nontrivial`. An explicit second `Nontrivial` binder
  was removed after the overlapping-instance linter identified it as redundant.
- Noetherian is `[IsNoetherianRing A]`, the recorded declaration of
  `def-weil-pbc-noetherian-ring`; it means every ideal is finitely generated.
- Local is `[IsLocalRing A]`. `IsLocalRing.closedPoint A` is the prime with ideal
  `IsLocalRing.maximalIdeal A`, the unique maximal ideal. No independent choice
  of maximal ideal or extra residue-field assumption is made.
- X is `AlgebraicGeometry.Spec (.of A)`, using `def-weil-affine-spectrum`'s
  recorded scheme spectrum, whose underlying space is PrimeSpectrum A.
- U with the subspace topology is the subtype
  `{x : AlgebraicGeometry.Spec (.of A) // x ≠ IsLocalRing.closedPoint A}`.
  Its predicate is exactly the complement of the singleton maximal point.
- W is a `Set` of that subtype; its nonemptiness is `hWnonempty : W.Nonempty`.
- Locally closed in U is `hWlocallyClosed : IsLocallyClosed W`. Mathlib defines
  this literally as existence of an open U' and closed Z' with W = U' ∩ Z'.
- The conclusion `∃ w ∈ W, IsClosed ({w} : Set {x : ... // ...})` gives membership
  in W and closedness of the singleton in the whole puncture, not just in W.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and
  `isNoetherianRing_iff`, with `isNoetherianRing_iff_ideal_fg` confirming the
  finite-generation meaning.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`;
  the statement uses Spec (no map is involved in this node).
- `Mathlib.RingTheory.Spectrum.Prime.Topology`: `IsLocalRing.closedPoint`.
- `Mathlib.Topology.Defs.Basic`: `IsLocallyClosed`.

Proof-only imports include the modules recorded by all stated proof dependencies:
`Mathlib.RingTheory.Ideal.Operations`, `Mathlib.RingTheory.LocalRing.Quotient`,
`Mathlib.Topology.NoetherianSpace`, `Mathlib.Topology.Separation.Basic`, and
`Mathlib.Topology.KrullDimension`. The spectrum topology and ideal-maximality
inputs are already transitively present through the statement imports.
`lem-per-noetherian-local-domain-open-infinite` has neither a Lean record nor a
Mathlib match, so there is no proof module to import yet; its full role remains
in the declaration docstring and the unchanged DAG proof.

Source checked: `literature/stacks-project/morphisms.tex`,
`lemma-ubiquity-Jacobson-schemes` (Tag 02J6), case (4), and
`literature/stacks-project/properties.tex`,
`lemma-complement-closed-point-Jacobson` (Tag 02IM), case (1), including its
prime-quotient direct proof. The docstring expands all six reviewed proof steps.
No statement correction and no STATEMENT-DISPUTED flag are needed.

Edge cases checked: a field or an Artinian local ring has empty puncture, so no
nonempty W exists and the implication is vacuous. A DVR has a one-point puncture,
which is closed in itself even though its generic point is not closed in X;
the subtype in the conclusion correctly includes this case. Nilpotents are
allowed; no reducedness, domain, completeness, dimension bound, characteristic,
or finite residue-field hypothesis is imposed. W may be arbitrary and need not
be open, closed, or irreducible. Empty W is excluded only by the explicit node
hypothesis. Universes and all variables are explicitly bound.

Searches performed using `/home/ubuntu/weil-launcher-nt/msearch.py`:

- `leanfinder`: "Every nonempty locally closed subset of the punctured spectrum
  of a Noetherian local ring contains a point closed in the punctured spectrum".
  Eight hits. `nonempty_inter_closedPoints` and
  `jacobsonSpace_iff_locallyClosed` require JacobsonSpace for the puncture;
  `exists_isClosed_singleton_of_isJacobsonRing` assumes a Jacobson ring.
  The other hits concern prime insertion, sobriety, or the original local closed
  point. None supplies this node's conclusion under its hypotheses.
- `leansearch`: "A punctured spectrum of a noetherian local ring is a Jacobson
  space". Eight hits: spectrum Jacobson equivalences/instances, fibres of finite
  type morphisms, and Noetherian spectra; no punctured-local Jacobson theorem.
- `loogle`: `IsLocallyClosed, IsLocalRing.closedPoint`: zero hits.
- `grep`: `punctured|complement.*closedPoint|jacobsonSpace_iff_locallyClosed`:
  broad search returned unrelated punctured analytic-neighborhood hits.
- `grep` restricted to `RingTheory/Spectrum/Prime`:
  `jacobsonSpace_iff_locallyClosed|closedPoint|punctured`: eleven hits, closedPoint
  definition/support/prime insertion and Jacobson-ring theorem, no exact match.
- `rg` in the upstream WeilConjectures and project lean/Sheaf source trees for
  punctured/closedPoint/Jacobson names, followed by the narrower
  `punctured.*(closed|jacobson)|puncturedSpectrum|punctured_local|puncturedLocal`:
  no existing declaration of this result. The prime-avoidance slicing consumer
  cites this item in its proof docstring but does not state it.
- `grep -rn` for `lem-per-punctured-local-closed-points` in upstream
  WeilConjectures: no hits. No conflicting declaration name was found.

Validation uses only the authorized scompile.py and deliver2.py wrappers.
The first compile identified only the redundant Nontrivial binder; it was
removed without changing the mathematical assumptions.

## Second reading by N3

Author's second pass (no separate reader or sub-agent was started, in accordance
with the dispatcher brief): compared the node and declaration again. The ring
hypotheses are all present, with nonzero included in the local-ring class. The same scheme spectrum and its maximal-point
complement occur in both the W binder and the conclusion. `IsLocallyClosed` is
on the complement subtype, and `IsClosed` is on that same subtype; thus the
conclusion does not accidentally ask for closedness in W or in Spec A. No
hypotheses or clauses are missing or added. The docstring retains every step
of the reviewed proof, and only the node's lean field changes. Independent
mathematical review remains with the maintainer, as specified by the brief.
