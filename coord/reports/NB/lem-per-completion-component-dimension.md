## Worker report

The module `Sheaf.AlgebraicGeometry.CompletionComponentDimension` states
`AlgebraicGeometry.completion_component_dimension`, with one `sorry` and no new definitions.
The node's statement is unchanged. Source checked directly: Illusie–Laszlo–Orgogozo,
Travaux de Gabber, Exposé XIV, Lemma 2.1.6, printed pages 210–211 (PDF pages 216–217).
It states the forward implication for every Noetherian local scheme and the converse
under universal catenarity, then reduces both assertions to reduced irreducible components.

Hypothesis and clause correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`, with the universe explicitly bound.
- Noetherian: `[IsNoetherianRing A]`; this is the recorded Mathlib predicate that all ideals
  are finitely generated.
- Local with maximal ideal m: `[IsLocalRing A]` and `IsLocalRing.maximalIdeal A`. Mathlib's
  local rings are nonzero and have a unique maximal ideal, exactly as the node requires.
- T = Spec A: `Spec (CommRingCat.of A)`, the recorded affine spectrum construction.
- The maximal-ideal completion: `AdicCompletion (IsLocalRing.maximalIdeal A) A`, with its
  actual compatible-sequence construction and commutative-ring structure; its spectrum is
  `Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))`.
- An irreducible component of dimension one: `∃ Z : Set ..., Z ∈ irreducibleComponents ... ∧
  topologicalKrullDim Z = (1 : WithBot ℕ∞)`. The dimension is that of the subtype Z with
  the subspace topology. Components are maximal nonempty irreducible subsets, automatically
  closed; these are the usual components, with no reducedness hypothesis on A.
- Forward assertion: the first conjunct is the implication from existence of such a Z in T
  to existence in the completed spectrum. Universal catenarity is absent here.
- Universal catenarity: the second conjunct begins `IsUniversallyCatenary A →`, using the
  dependency's recorded predicate, not a private replacement or an excellence hypothesis.
- Converse assertion: inside that second conjunct, existence in the completed spectrum implies
  existence in T. This retains both conditional directions of the node, rather than assuming
  universal catenarity for the whole theorem.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with
  `isNoetherianRing_iff_ideal_fg` confirming the finite-generation meaning.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, exposed by the public import
  `Mathlib.RingTheory.AdicCompletion.Algebra`, which supplies the ring structure.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.RingTheory.ExcellentRing`: `IsUniversallyCatenary`; its full definition quantifies
  over finite-type algebras in the ring's universe and includes Noetherianity.
- Supporting Mathlib notions: `IsLocalRing`, `IsLocalRing.maximalIdeal`, and
  `irreducibleComponents`. No dependency interface required repair.

All currently stated proof dependencies are imported without `public`: local completion
quotient, completion dimension, completion Noetherianity, local completion/local hom,
faithful flatness, flat going down, minimal primes, and spectrum dimension/components.
The completion-Noetherianity module was read via `scompile.py --source
WeilConjectures.RingTheory.AdicCompletionNoetherian`, since it is absent from the older
source checkout. `lem-per-ratliff-formal-catenarity` has neither a Lean record nor a Mathlib
match at inspection time, so there is no module to import for this proof-only dependency.
Its use is retained explicitly in the theorem's natural-language proof; it is not needed
to type the statement. The docstring follows all six proof steps in the DAG.

Edge cases checked:

- A field or an Artinian local ring has dimension zero; no one-dimensional component is
  asserted without the corresponding premise.
- Empty components cannot witness either existential because Mathlib irreducibility includes
  nonemptiness. The empty spectrum/zero ring is already excluded by unique-maximal-ideal
  locality, not by an added binder.
- A may be reducible, nonreduced, nonexcellent, or of mixed characteristic. No domain,
  equidimensionality, reducedness, characteristic, or excellence hypothesis was introduced.
- Catenarity is conditional only in the second conjunct. The first direction remains usable
  for arbitrary Noetherian local rings.
- `u` is arbitrary; completion stays in the same universe. There is no test-object universe
  restriction, finite enumeration of components, or choice of a particular component.

Searches for an existing statement (retained wrapper results in sandbox `searches.jsonl`):

- LeanFinder: “For a Noetherian local ring its spectrum has an irreducible component of
  dimension one only if the spectrum of its maximal ideal completion does, and conversely
  for universally catenary rings”. Eight hits concerned finite local dimension, DVR criteria,
  and height-one ideals; none stated this result.
- LeanFinder: “completion preserves and reflects one-dimensional irreducible components
  universally catenary”. Eight hits concerned spectrum irreducibility, integral schemes,
  and dimension-one rings; no match.
- Loogle: `AdicCompletion, irreducibleComponents, topologicalKrullDim`: zero hits.
- Mathlib grep: `completion.*component|component.*completion|[Cc]atenary` in RingTheory,
  and the lower-case catenary variant: three unrelated AdicCompletion functoriality hits.
- `rg` over upstream WeilConjectures and project lean/Sheaf for
  `completion.*component|component.*completion|completion_component_dimension`: no theorem
  matching this statement, only unrelated componentwise completion constructions.
- `grep -rn` for this node id in upstream WeilConjectures and `rg` of the proposed declaration
  and node id in `dag/lean_names_upstream.json`: no match.

No new nodes, dependency repairs, statement corrections, or STATEMENT-DISPUTED faults.
Validation: `scompile.py NB lem-per-completion-component-dimension` compiled the draft
as an isolated file without errors or warnings. The final module path and docstring are
validated again by the delivery dry run.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
