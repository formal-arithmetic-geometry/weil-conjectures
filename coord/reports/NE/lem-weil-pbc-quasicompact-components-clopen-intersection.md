## Worker report

Existing declaration: `sInter_isClopen_and_mem_eq_connectedComponent`, in
`WeilConjectures.Topology.SpectralSpace.ConnectedComponent`, source lines 65–66.
No module is written: this already states the whole node, with the equality reversed.
The upstream theorem has no declaration docstring; its `[stacks 005F]` attribute and
module documentation identify the source. Its full proof was read (lines 67–142).
The source statement was checked in `literature/stacks-project/topology.tex`,
`lemma-connected-component-intersection` (Tag 005F), lines 1816–1830.

Hypothesis and conclusion matching:

- A topological space `T`: `{X : Type u} [TopologicalSpace X]`, with arbitrary universe `u`.
- Quasi-compactness: `[CompactSpace X]`; Mathlib compactness does not impose Hausdorffness.
- A basis of quasi-compact opens: `[PrespectralSpace X]`, whose field is
  `IsTopologicalBasis {U : Set X | IsOpen U ∧ IsCompact U}`.
- Intersections of two quasi-compact opens are quasi-compact: `[QuasiSeparatedSpace X]`,
  whose `inter_isCompact` field quantifies over every pair of open compact subsets.
- No sobriety assumption: neither `QuasiSober`, `T0Space`, `T2Space`, nor the stronger
  bundled `SpectralSpace X` is required by the theorem.
- Every point `t`: implicit `{x : X}`, universally quantified in the declaration.
- Its connected component: Mathlib `connectedComponent x`.
- All clopen neighbourhoods: the subtype `{U : Set X // IsClopen U ∧ x ∈ U}`.
- Their intersection: `⋂ (U : {U : Set X // IsClopen U ∧ x ∈ U}), U`.
- Equality with the component: `... = connectedComponent x`; reversing the equality
  does not change the proposition's content.

Statement dependency read: `def-weil-spectral-space`, recorded as `SpectralSpace` in
`Mathlib.Topology.Spectral.Basic`. Its full signature and docstring were read:
it extends `T0Space`, `CompactSpace`, `QuasiSober`, `QuasiSeparatedSpace`, and
`PrespectralSpace`. The item explicitly selects only the last three conditions and
excludes sobriety. The existing upstream theorem uses precisely these recorded
Mathlib component notions; imposing the whole `SpectralSpace` would be incorrect.
No replacement definition or dependency module is needed.

Edge cases: the empty space is allowed (the point-quantified assertion is vacuous);
no `Nonempty X` is assumed. For every actual point the clopen-neighbourhood subtype
contains the whole space. Singleton, indiscrete, and non-Hausdorff spaces are not
excluded; the connected indiscrete case gives the whole space on both sides.
No finite, nonempty, or small-index restriction is introduced.

Searches (2026-10-15):

- `msearch.py leanfinder`, query “connected components are intersections of clopen
  neighborhoods in a compact quasi-separated space with a basis of compact open sets”:
  eight hits, including Mathlib `connectedComponent_eq_iInter_isClopen` (requires T2)
  and `connectedComponent_subset_iInter_isClopen` (only inclusion). Neither is exact.
- `msearch.py loogle`, query `connectedComponent, IsClopen`: six hits; same two
  candidates. Their full source signatures and docstrings were inspected.
- `msearch.py grep`, query
  `connectedComponent_eq_iInter_isClopen|connectedComponent_subset_iInter_isClopen`,
  subdirectory `Topology`: eight hits; no exact general equality in Mathlib.
- `rg` in the upstream `WeilConjectures` tree for
  `sInter_isClopen_and_mem_eq_connectedComponent|connectedComponent.*(iInter|sInter)`:
  found the exact theorem in `Topology/SpectralSpace/ConnectedComponent.lean`.
- The same `rg` in `lean/Sheaf`: no matches.
- `rg` for the item id in upstream `WeilConjectures`: no matches.
- `rg` for the declaration name in `dag/lean_names_upstream.json`: no matches;
  direct source inspection establishes its existence and exact signature.

No statement correction, new nodes, dependency modules, or disputed statement.

Validation: server-only `scompile.py` probe checks the existing declaration's full
signature and prints its axioms; the required `deliver2.py --no-push` checks the
existing declaration again and runs delivery preflight. Results are recorded below.

Server probe passed cleanly (1.2 s, nice 19, two threads, 60 s limit).
The elaborated type has exactly `TopologicalSpace`, `PrespectralSpace`,
`CompactSpace`, and `QuasiSeparatedSpace` as instance binders.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Second reading by NE

I independently opened the item node, its sandbox copy, the dependency node
`def-weil-spectral-space`, the recorded Mathlib declarations, and the upstream
theorem (including its inherited variables and full proof). I read Stacks
`topology.tex`, Tag 005F, lemma-connected-component-intersection, statement and
proof at lines 1816 onward. The source introduces an arbitrary topological space
and lists exactly three assumptions; the preceding Kolmogorov lemmas do not
impose any standing assumption on this lemma.

Object, hypothesis, and conclusion checklist:

- Space T: `{X : Type u} [TopologicalSpace X]`. Exact; u is arbitrary.
- T quasi-compact: `[CompactSpace X]`. Exact; no Hausdorff axiom is included.
- Basis of quasi-compact opens: `[PrespectralSpace X]`. Exact: its sole field
  is `IsTopologicalBasis {U : Set X | IsOpen U ∧ IsCompact U}`. The nearby
  `PrespectralSpace.of_isTopologicalBasis` confirms that existence of such a
  basis suffices, so taking all compact opens adds no assumption.
- Pairwise intersections of quasi-compact opens quasi-compact:
  `[QuasiSeparatedSpace X]`. Exact: its field quantifies over arbitrary U, V
  with `IsOpen U`, `IsCompact U`, `IsOpen V`, `IsCompact V`, and concludes
  `IsCompact (U ∩ V)`.
- No sobriety: exact. `SpectralSpace` in the dependency additionally extends
  `T0Space` and `QuasiSober`; the node explicitly selects its three other
  component conditions. The upstream theorem uses those components directly,
  not the stronger class. No dependency replacement is needed.
- Every point t of T: implicit `{x : X}`, after the space and its assumptions.
  Exact universal quantification, not a selected point.
- Connected component of t: Mathlib `connectedComponent x`. Exact.
- All open and closed subsets containing t:
  `{U : Set X // IsClopen U ∧ x ∈ U}`. Exact, without a compactness restriction
  on the indexing subsets.
- Intersection and equality: `⋂ (U : {U : Set X // IsClopen U ∧ x ∈ U}), U =
  connectedComponent x`. Exact full equality; its orientation is immaterial.

Edge cases: the empty space is admitted, with no point to quantify over.
For an actual point, the index subtype always contains `Set.univ`; no
nonemptiness hypothesis is added. Arbitrary infinite intersections are used,
with no finite or small-index condition. Singleton and indiscrete spaces are
covered (including non-T0 examples), as are non-Hausdorff spaces satisfying
the three assumptions. Rings, characteristic, schemes, and n are not objects
of this statement. All inherited variables and universes are bound.

Independent searches on 2026-10-15:

- `msearch.py leanfinder`: "quasicomponents equal components for coherent
  compact topological spaces" returned eight hits. The equality candidate
  `connectedComponent_eq_iInter_isClopen` requires `[T2Space X]`; I opened its
  source at Mathlib/Topology/Separation/Regular.lean:725 and rejected it.
- `msearch.py loogle`: `"connectedComponent", "IsClopen"` returned twelve
  hits. I opened Mathlib/Topology/Connected/Clopen.lean:368: its unrestricted
  `connectedComponent_subset_iInter_isClopen` gives only one inclusion.
- `rg` for `quasi[Cc]omponent|sInter.*connectedComponent|connectedComponent_eq_iInter`
  across Mathlib/Topology, upstream WeilConjectures, and project lean/Sheaf
  found the exact upstream theorem at ConnectedComponent.lean:65; no project
  duplicate appeared. This uses alternative terminology as well as names.

No mismatch was found. No statement, signature, node record, or upstream file
was changed; only this independent review was appended. There are no new
definition nodes or dependency modules to review. H5, H6, and new-declaration
docstring/convention checks require no new code: this is an existing theorem
attachment, whose source `[stacks 005F]` attribute identifies the lemma.
The existing source lacks a declaration docstring, as the worker noted; it
is read-only and is not duplicated to add one.

I reran the scratch probe with server-only `scompile.py`: clean in 1.1 s,
nice 19, two threads, 60 s limit. Its printed full type has exactly the four
instance binders listed above; its axioms are `propext`, `Classical.choice`,
and `Quot.sound`. There is no delivered Lean module to compile.
