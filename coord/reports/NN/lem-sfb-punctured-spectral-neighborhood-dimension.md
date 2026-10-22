## Worker report

Stage 2 statement of lem-sfb-punctured-spectral-neighborhood-dimension in
`Sheaf.Topology.PuncturedSpectralNeighborhoodDimension`, declaration
`Topology.spectralSpace_puncturedGeneralizations_and_dimension`. The only theorem
has proof `sorry`; no new definition or helper theorem is introduced. The existing
stage-1 split and its review are preserved. This is a stage-2 attachment, not a re-split.
The previous attempt reported an unchanged node; this packet adds the actual Lean record
and its module.

Hypotheses and clauses, matched to the node:

- The topological space X is `(X : Type u) [TopologicalSpace X]`, with arbitrary
  explicit universe u. Its spectrality is `[SpectralSpace X]`, the recorded Mathlib
  definition: compact, T0, quasi-sober, quasi-separated and a compact-open basis.
- The positive integer bound is `(n : ℕ) (hn : 1 ≤ n)`. Positive integers are precisely
  positive naturals, so this parameterization covers every permitted integer bound.
  The hypothesis dim X ≤ n is `hdim : topologicalKrullDim X ≤ (n : WithBot ℕ∞)`.
- The subset is `(Z : Set X)`; closedness is `hZ : IsClosed Z`.
  Quasi-compactness of X minus Z is `hU : IsCompact Zᶜ`.
- The point set W = {x : closure {x} meets Z}, followed by S = W minus Z,
  is exactly the existing `TopCat.puncturedGeneralizations Z`, whose full definition
  is `{t | (closure ({t} : Set X) ∩ Z).Nonempty ∧ t ∉ Z}`. Its subtype topology
  is the subspace topology specified in the node. There is no arbitrary map or object.
- The first conjunct is `SpectralSpace (TopCat.puncturedGeneralizations Z)`.
- The second conjunct is
  `topologicalKrullDim (TopCat.puncturedGeneralizations Z) ≤
  ((n - 1 : ℕ) : WithBot ℕ∞)`.
  Subtraction takes place in ℕ before casting; since 1 ≤ n, it is ordinary integer
  subtraction at every admissible bound. Mathlib's bottom dimension is minus infinity.
- There is no `Nonempty X`, `Nonempty Z`, properness of Z, or nonemptiness of S
  hypothesis, so all explicitly stated endpoint cases remain included.

Dependency declarations read and used:

- `Mathlib.Topology.Spectral.Basic`: `SpectralSpace`, the declaration recorded on
  def-weil-spectral-space. Read its full definition and docstring (Stacks 08YG).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, recorded on
  def-kun-topological-krull-dimension. It is `Order.krullDim (IrreducibleCloseds X)`
  in `WithBot ℕ∞`, the supremum of strict-chain lengths with empty supremum bottom.
- `Sheaf.Topology.PuncturedNeighborhoodCohomologyDiagram`:
  `TopCat.puncturedGeneralizations`. Read its definition and source docstring,
  recorded in lean.declarations of the already landed
  def-weil-pbc-punctured-neighborhood-cohomology-diagram. Added this node to
  stmt_deps under the authorized landed-dependency rule; no duplicate notion.
- Proof-only import `WeilConjectures.Topology.SpectralGeneralizations`:
  `Topology.generalizations_isCompact_sInter_isCompactOpen`, recorded on
  lem-weil-pbc-spectral-generalizations-of-quasi-compact. Read full signature
  and docstring: the hull of compact E is compact and the intersection of compact
  open neighborhoods of E.
- Proof-only import `Sheaf.Topology.SpectralDirectedLimit`:
  `Topology.spectralSpace_directedLimit`, recorded on
  lem-weil-pbc-spectral-directed-limit-spectral. Read the signature and docstring:
  nonempty directed set, spectral spaces and transition maps, compatible continuous
  projections, bijective tuple map, and initial topology imply spectrality and
  spectral projections. The index set of ambient compact-open neighborhoods can
  live in the same universe u as X, so this interface suffices.

Source and proof reading:

Read `literature/stacks-project/topology.tex`, lemma-make-spectral-space-minus
(Tag 0AP0): for constructible E its generalizations minus E are spectral.
A closed subset with compact open complement is constructible, so it applies.
Read `literature/stacks-project/cohomology.tex`,
proposition-cohomological-dimension-spectral (Tag 0A3G), induction step (2): the
punctured hull has strictly lower dimension. The docstring includes all six
reviewed DAG proof steps: the compact-open neighborhood intersection, spectrality
of compact opens and the transitions, the topological inverse limit, lifting
irreducible chains by ambient closure, prepending a specialization in Z, and
empty cases. No change of source statement was required.

Edge cases checked before writing:

- Z empty: its generalization hull and S are empty, so dim S is bottom.
- Z = X: every point is in W but no point survives removal of Z; S is empty.
- X empty: Z and S are empty. Empty spectral spaces are allowed by Mathlib.
- n = 1: the conclusion is dim S ≤ 0, including empty S.
- Zero-dimensional X with any n ≥ 1: the hypotheses allow it and S is empty;
  no equality between n and the actual dimension has been added.
- A three-point specialization chain η → y → z, Z = {z}, n = 2 has
  S = {η,y} and dimension 1, showing the precise bound is sharp.
- A two-point specialization chain (e.g. Spec of a DVR), Z the closed point,
  n = 1 has S the generic point and dimension 0.

Searches for existing declarations (2026-10-22):

- msearch.py leanfinder, query: "The generalizations of a closed subset of a
  spectral space with compact open complement, minus that subset, form a spectral
  space with Krull dimension at most one less". Eight hits: spectral-space
  structure projections, prime-spectrum spectrality/prespectrality,
  `SpectralSpace`, `PrespectralSpace`, and `topologicalKrullDim`. No matching theorem.
- msearch.py loogle, query: "SpectralSpace, topologicalKrullDim". No hits.
- msearch.py leansearch, query: "The punctured generalization subspace of a closed
  subset in a spectral space has strictly smaller Krull dimension". Eight hits:
  `topologicalKrullDim`, subspace/inducing dimension monotonicity, ring Krull
  dimension, prime-spectrum dimension equality, and dimension-zero results.
  None proves the spectrality and strict dimension drop in this statement.
- msearch.py grep, query: "punctured|generalizations|topologicalKrullDim",
  Mathlib/Topology. Twenty-five hits, mostly ordinary dimension monotonicity
  and punctured neighborhood filters; no combined statement.
- rg on `lean/WeilConjectures/` and `lean/Sheaf/` for punctured and spectral
  dimension terms; focused rg on their Topology directories and
  `dag/lean_names_upstream.json` for `puncturedGeneralizations`,
  `spectralSpace.*punctured`, `topologicalKrullDim`. Found and reused the
  puncturedGeneralizations definition. The private
  `puncturedGeneralizations_dimension` in TopDegreeAbelianNeighborhoodZero
  supplies only a dimension inequality, not the required spectrality, and is
  private; it is not an exact existing declaration for this conjunction.
- grep -rn for the item id in `lean/WeilConjectures/`: no declaration.

No statement dispute, statement correction, new node, or dependency-interface
repair is needed. Only lean and the permitted addition to stmt_deps change.

Validation: scompile.py compiled the module in sandbox and library modes, each
in 1.9 seconds, with no errors or unexpected warnings. deliver2.py --no-push
reported OK: the packet passes server preflight and per-file compilation.
The local record check confirms the only changed fields are lean and stmt_deps,
the recorded signature is verbatim, there is exactly one sorry, and all Lean
lines are at most 100 characters.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
