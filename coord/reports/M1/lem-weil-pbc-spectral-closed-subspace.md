## Worker report

The module `Sheaf.Topology.SpectralClosedSubspace` states
`Topology.spectral_closed_subspace`, with its sole proof left as `sorry`.
No definitions, additional nodes or dependency modules are needed.

Hypothesis and clause correspondence:
- A spectral space X: `{X : Type u} [TopologicalSpace X] [SpectralSpace X]`.
- A closed subset E of X: `(E : Set X) (hE : IsClosed E)`.
- E with the induced topology: the subtype `E`, with Mathlib's canonical subtype topology.
- E is spectral: the first conjunct `SpectralSpace E`.
- Its quasi-compact opens are exactly traces of ambient quasi-compact opens:
  `∀ V : Set E, (IsOpen V ∧ IsCompact V) ↔
  ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ V = Subtype.val ⁻¹' U`.
  Preimage under the subtype inclusion is E ∩ U as a subset of E. The equivalence gives
  both directions, without assuming V open or compact in advance.

Dependency: `def-weil-spectral-space` is a Mathlib leaf whose `mathlib_match` names
`SpectralSpace` in `Mathlib.Topology.Spectral.Basic`. Read its full class signature and
module docstring: T0 + QuasiSober give sobriety with unique generic points; CompactSpace
is quasi-compactness; QuasiSeparatedSpace and PrespectralSpace supply the other two clauses.
This is precisely the node's definition, so no dependency replacement is needed.

Edge cases checked mathematically before drafting: E empty (spectral vacuously; its only
open is the empty trace, witnessed by U empty); E = X (the usual compact opens); V empty
(witness U empty); empty ambient X. Neither nonemptiness, Hausdorffness, nor a separation
condition beyond spectrality is added. The single explicit universe u accommodates every
ambient space and all its subsets. There are no auto-bound variables or universes.

Searches:
- msearch.py leanfinder: "A closed subset of a spectral space is spectral and its compact
  open subsets are traces of compact opens". Eight results: SpectralSpace and component
  projections, PrespectralSpace.of_isClosedEmbedding, and the retrocompact/spectral-map
  characterization. None states both conclusions of this node.
- msearch.py loogle: "SpectralSpace, IsClosed". Zero hits.
- msearch.py grep: "SpectralSpace|of_isClosedEmbedding" in Topology/Spectral. Thirteen
  results, including only the open-embedding spectrality theorem and component results.
- rg of Mathlib.Topology.Spectral.Basic and Prespectral: read the spectral class and
  PrespectralSpace.of_isClosedEmbedding. No theorem for closed-subspace spectrality
  together with the exact compact-open trace characterization.
- rg "spectral.*closed|closed.*spectral|spectralClosed|spectral_closed" in
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures and repository lean/Sheaf found
  sheaf-restriction statements and commentary, not this statement. Read the upstream
  Mathlib/Topology/Spectral/Prespectral.lean; it concerns separation by compact opens.
- grep -rn "lem-weil-pbc-spectral-closed-subspace" in upstream WeilConjectures: no hits.
- rg "spectral_closed_subspace" in dag/lean_names_upstream.json: no name collision.

Source verification: local literature/stacks-project/topology.tex is unavailable on this
machine. Read the official [Stacks Tag 0902](https://stacks.math.columbia.edu/tag/0902)
(Lemma 5.23.5), which includes closed subsets as a case and describes compact opens as
traces. The original seven-step DAG proof is reproduced in the theorem docstring.
No statement correction or STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled the module on the server in 1.0 s, exit code 0,
with no errors or warnings. The delivery dry run is the final gate; the second reader
will supply the independent reading before pushing.

## Second reading by M1

Independent review of the node, its seven proof steps, the delivered module, and
`def-weil-spectral-space` in `sec-nagata-compactification`. The source TeX was fetched
into this item's scratchpad from the official Stacks repository. Read
`topology.tex`, label `lemma-spectral-sub`, lines 4427–4458 (Tag 0902), and the
[official rendered lemma](https://stacks.math.columbia.edu/tag/0902).
The source assumes only a spectral space and a subset closed in the constructible
topology; it explicitly includes ordinarily closed subsets. This node intentionally
states that closed case. The compact-open description is in the source proof,
lines 4450–4457. No background algebraic or nonemptiness hypotheses apply.

Object, hypothesis, and conclusion checklist (H3):
- Ambient topological space X: `{X : Type u} [TopologicalSpace X]`. Exact; arbitrary
  universe, no restriction to schemes or Hausdorff spaces.
- X spectral: `[SpectralSpace X]`. Exact match with the dependency's Mathlib leaf
  `SpectralSpace` in `Mathlib.Topology.Spectral.Basic`, whose signature I opened.
  Also opened the signatures of `PrespectralSpace`, `QuasiSeparatedSpace`, and
  `QuasiSober`. `CompactSpace` means quasi-compactness without separation;
  `QuasiSeparatedSpace.inter_isCompact` is exactly compact-open intersection
  compactness; `PrespectralSpace.isTopologicalBasis` is the compact-open basis.
  `QuasiSober.sober` provides existence of generic points, and `T0Space` gives
  uniqueness. Together these say exactly what the dependency node says.
- Closed subset E: `(E : Set X) (hE : IsClosed E)`. Exact, closed in the original
  topology, with no assumption that E is open, constructible, or nonempty.
- Induced topology on E: the subtype `E` with the canonical subtype topology.
  Exact; no independent topology or instance is imposed on E.
- E spectral: `SpectralSpace E`, the first conjunct. Exact, including every
  component of the dependency definition, rather than only prespectrality.
- All compact open subsets of E: `∀ V : Set E, (IsOpen V ∧ IsCompact V) ↔ ...`.
  Exact, with V quantified after X and E. `IsCompact` here is quasi-compactness
  in E; it adds no Hausdorff condition.
- Exactly the traces of ambient compact opens:
  `∃ U : Set X, IsOpen U ∧ IsCompact U ∧ V = Subtype.val ⁻¹' U`.
  Exact. For x in E, membership in this preimage is membership of its ambient
  value in U, hence precisely E intersect U as a subset of E. The equivalence
  asserts both directions, and U may depend on V. No extra uniqueness or
  injectivity of the trace operation is claimed.

Edge cases: E empty and V empty are covered (U empty witnesses the trace);
X empty is allowed and spectral vacuously; E = univ gives the original topology.
Empty finite subcovers in proof step 4 give the empty ambient open. The theorem
has no indices, degree n, ring characteristic, zero object, or scheme; those
checks impose no extra restriction here. The explicit universe u binds X and
its subtype and sets, covering every universe of topological spaces. All
variables and universes are bound by eye, with no auto-implicit names.

Independent searches, using different words from the first reading:
- leanfinder: "compact open subsets of closed subspaces are inverse images of
  compact open sets in a spectral topological space". Eight results, including
  `PrespectralSpace.of_isClosedEmbedding`,
  `Topology.IsOpenEmbedding.spectralSpace`, and spectral-map preimage lemmas.
  Opened the relevant spectral and prespectral modules. None gives this whole
  statement; the closed-embedding result gives only a basis condition, and the
  spectral-space result requires an open embedding.
- loogle: `SpectralSpace, Set.preimage`: zero hits.
- leansearch: "closed embedding into a spectral space gives a spectral domain
  and all compact opens extend to the codomain": service unavailable (Internal
  Server Error), recorded as unavailable, with no mathematical verdict inferred.
- msearch grep in Topology:
  `IsClosedEmbedding.*spectral|compact.*open.*(preimage|subtype)|spectral_closed_subspace`:
  eleven hits, including only the prespectral closed-embedding result and
  related preimage results; no exact existing statement.
- Direct rg on upstream WeilConjectures, repository lean/Sheaf, Mathlib Topology,
  and dag/lean_names_upstream.json for spectral/closed/subspace and compact-open
  trace combinations. Opened upstream `Mathlib/Topology/Spectral/Prespectral.lean`
  (separation of closed sets by compact opens) and repository
  `Topology/SpectralClosedRestriction.lean` (sheaf-section restriction), neither
  of which states this node. No full-name collision or exact existing declaration.

H4/H5/H6/H8/H9: the sole imported module is used for the dependency definition;
there is no duplicate or hollow definition, no new node or dependency module,
and the only proof is the required `sorry`. Both docstrings identify Tag 0902
and the item. The theorem docstring records all seven node proof steps, including
finite extraction and ambient union in the nontrivial converse, and names the
proof dependencies. Namespace, topic, header, and line widths satisfy the brief.
The node's `lean.statement` is verbatim the file's signature before `:=`.
No statement correction is present or needed, so the citer-correction check
is inapplicable. No mismatch found; retained the correct Lean and node unchanged.
Only this independent second-reading report and search evidence were added.

Validation: recompiled the delivered module with scompile.py using its absolute
sandbox path; the delivery dry run and push below enforce the final compile and
preflight checks.
