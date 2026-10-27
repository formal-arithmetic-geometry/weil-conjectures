## Worker report

The module `Sheaf.Topology.Connected.ComponentQuotientClopenNaturality` states
`ConnectedComponents.clopen_descent_naturality`. Its only proof is `sorry`; no definitions,
axioms, helper theorems, new nodes, or dependency repairs are introduced. The item node is
changed only in `lean`.

Hypotheses and clauses, in order:

- The size convention is rendered by explicit universe levels `u v w`. The dependency
  `def-weil-size-convention` has `lean.convention: true` and no module or declaration to
  import. No sites or derived categories occur here; no additional smallness is needed.
- Arbitrary spaces are `{X : Type u} {Y : Type v}` with their `TopologicalSpace` instances.
  The continuous map is `(f : X → Y) (hf : Continuous f)`. There are no other hypotheses.
- `TopologicalSpace.Clopens Z` is Mathlib's bundled open and closed subset, not a private
  notion. `ConnectedComponents Z` is Mathlib's quotient by equality of point components,
  with its existing quotient topology. `ConnectedComponents.mk` is exactly the map q_Z.
  A component is `connectedComponent x`; its defining union of preconnected sets through
  x equals the union of connected sets through x because each such set contains x.
- The existential `h : ContinuousMap (ConnectedComponents X) (ConnectedComponents Y)`
  gives continuity. The first conjunct is the normalization `h ∘ mk = mk ∘ f`.
- The second conjunct quantifies over **every** continuous `g` satisfying normalization
  and concludes `g = h`. Uniqueness is not restricted to maps already satisfying the
  later naturality or bijectivity clauses.
- The third conjunct, `∀ x : X, h (mk x) = mk (f x)`, is the specified point formula.
- The fourth conjunct quantifies over every `(Z : Type w) [TopologicalSpace Z]`.
  `Function.Bijective (fun V : Clopens (ConnectedComponents Z) ↦ ⟨mk ⁻¹' V, ...⟩)`
  is precisely bijectivity of beta_Z. Continuity of mk supplies its clopen-valuedness.
  Its remaining two subclauses, for every `U : Clopens Z`, are `IsClopen (mk '' U)`
  and `mk ⁻¹' (mk '' U) = U`. Together with bijectivity these specify the inverse:
  the clopen whose carrier is `mk '' U` maps to U and hence is the unique inverse value.
  No arbitrary inverse function or extra choice is used.
- The fifth conjunct is naturality, as an equality of underlying subsets:
  `mk ⁻¹' (h ⁻¹' V) = f ⁻¹' (mk ⁻¹' V)` for every bundled clopen V of pi_0(Y).
  Every term is clopen by the continuity of h, f, and the two quotient maps; equality
  of carriers is equivalent to equality of the bundled clopens by `Clopens.ext`.
- The final conjunct compares `Function.Bijective` of the two bundled inverse-image
  maps, along f and h respectively, with `↔`, in the order given in the node.
- The binder list has no compactness, separation, local connectedness, inhabitedness,
  or nonemptiness instance. All variables and universes are explicit; `autoImplicit`
  is disabled. The globally quantified Z has its own polymorphic universe w.

Dependencies and existing declarations read:

- `def-weil-size-convention`: metatheoretic convention; explicit universe binders as above.
- Proof dependency `lem-sfb-connected-component-maximality`: Mathlib leaf in
  `Mathlib.Topology.Connected.Basic`. Read `connectedComponent`, `mem_connectedComponent`,
  `isConnected_connectedComponent`, and `IsConnected.subset_connectedComponent`, including
  their complete signatures and the definition of the union. This module is explicitly
  imported as a proof dependency.
- Proof dependency `def-weil-connected-scheme`: Mathlib leaf `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`, and its equivalent `connectedSpace_iff_clopen` in
  `Mathlib.Topology.Connected.Clopen`. The latter is transitively available through the
  public import `Mathlib.Topology.Connected.TotallyDisconnected`.
- `Mathlib.Topology.Connected.Clopen`: `ConnectedComponents`, `mk`, its topology,
  `surjective_coe`, `isQuotientMap_coe`, and `continuous_coe`.
- `Mathlib.Topology.Connected.TotallyDisconnected`: read the genuine quotient construction
  `Continuous.connectedComponentsLift`, its continuity/uniqueness statements, and
  `Continuous.connectedComponentsMap` with its normalization and continuity lemmas.
  These provide the canonical witness for the existential in stage 3.
- `Mathlib.Topology.Sets.Closeds`: `TopologicalSpace.Clopens`, its carrier, `isClopen`,
  and extensionality. `IsClopen.preimage` supplies the proof fields of the inline maps.
- Also read upstream
  `WeilConjectures.Mathlib.Topology.Connected.TotallyDisconnected`, particularly
  `IsClopen.connectedComponents_image_isClopen`. This is only one constituent, not the
  entire node statement, and does not require a new definition or duplicate statement.

Sources checked in local `literature/stacks-project/topology.tex`: the definitions and
component argument at lines 620–695, quotient construction at lemma-space-connected-components,
and the clopen-saturation sentence in Tag 0900 at lines 4232–4261. The last sentence uses
no compactness or separation hypothesis; those apply to the tag's subsequent profiniteness
conclusion, which this statement does not assert. The module docstring carries all seven
steps of the node proof and identifies both proof dependencies.

Edge cases checked before writing:

- Empty X: its quotient is empty, and all source clopen sets consist only of the empty
  subset. There is one normalized map, even when Y is nonempty. Both final bijectivity
  conditions hold exactly when the target has only one clopen.
- Empty Y: an f can exist only when X is empty. Both quotient spaces and both clopen maps
  then have the required unique-map/one-element behavior.
- The general Z clause includes empty Z and the empty and full clopens. The image and
  saturation formulas give the empty set and the whole quotient, respectively.
- Nonempty connected spaces, including the non-Hausdorff Sierpinski space: the quotient
  is one point and both sides of beta have two clopens.
- Discrete spaces: every component is a singleton and the result is the ordinary
  inverse-image naturality for subsets.
- The rationals and infinite products of two-point discrete spaces have components
  which need not be open. Only saturation of **clopen U** is used, never openness of
  individual components. No extra local connectedness has slipped in.
- Different universe levels for X and Y are allowed; Z is separately universe polymorphic.

Searches performed with the prescribed wrapper, group Q119 and this item:

- LeanFinder: `A continuous map induces a unique continuous map of connected component
  quotients and natural bijections on clopen subsets`. Eight hits, chiefly
  `Continuous.connectedComponentsMap`, `Continuous.connectedComponentsLift`, continuity,
  uniqueness, and normalization lemmas. None states the entire clopen descent result.
- Loogle: `"ConnectedComponents", "Clopens"`. Zero hits.
- Mathlib grep: `ConnectedComponents.*(map|clopen)|Clopens.*(comap|preimage)` in `Topology`.
  Twelve hits, providing the component map, its continuity, and quotient criteria,
  without the full natural clopen comparison.
- LeanSearch: `Clopen subsets are naturally in bijection with clopen subsets of the
  quotient by connected components`. Eight hits include `TopologicalSpace.Clopens`,
  `ConnectedComponents.isQuotientMap_coe`, `Topology.IsQuotientMap.isClopen_preimage`,
  and `DiscreteQuotient.ofIsClopen`; none includes this full result.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for component/clopen combinations
  found the upstream clopen-image constituent and the spectral-specialized consumer
  `isHomeomorph_connectedComponentsMap_of_bijective_clopen_preimage`. The latter assumes
  spectral spaces and has a different conclusion. Neither is an exact existing match.
- `grep -rn` for the exact blueprint id in `lean/WeilConjectures` found no declaration.
  Read the relevant Mathlib and upstream source signatures in full as listed above.

No statement correction or STATEMENT-DISPUTED issue was needed. The inherited stage-1
review's advisory about the connectedness citation is handled by using the existing
Mathlib definition and explicit proof imports; the accepted split is unchanged.

Validation: the prescribed `scompile.py Q119 lem-sfb-component-quotient-clopen-naturality`
command compiled the sandbox module and the correctly named library module successfully,
with no errors or unexpected warnings. No local compiler or global build was run.

## Second reading by Q119

Clause-by-clause second pass by the same worker; no independent agent was started, as
the dispatcher explicitly forbids it. The maintainer supplies the independent review.
Compared the complete node with the module after writing: normalization and uniqueness
are separate conjuncts, with uniqueness ranging over all normalized continuous maps;
the point formula is explicit. The general Z clause contains both beta bijectivity and
the actual set image/saturation formulas, which determine its inverse without adding a
choice. Naturality is stated on carriers, which faithfully renders bundled-clopen equality.
The final iff is about the two bundled-clopen inverse-image functions, with proof fields
supplied by exactly the given continuities. No hypothesis, clause, or edge case was lost,
and no additional mathematical assumption was introduced. No mismatch was found.
