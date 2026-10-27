## Worker report

The module `Sheaf.Topology.ClosedOrbitComponentMap` states
`Topology.closed_orbit_component_map`, with its single proof `sorry`.
No definition is introduced, no theorem is proved, and the node copy changes
only `lean`. There are no statement faults or disputed clauses.

The source read was `literature/stacks-project/topology.tex`,
`definition-irreducible-components` (Tag 004V, lines 854–863),
`definition-generic-point` (Tag 004X, lines 971–998), and the adjacent
`lemma-image-irreducible-space`. I also read
`literature/stacks-project/groupoids.tex`, `lemma-points` (Tag 03BL,
lines 4452–4472), whose point-orbit conclusion is assumed here, not
silently proved or imported from a scheme-theoretic result.
This node is the elementary topological auxiliary to the finite-quotient
input; its own seven-step proof is reproduced in the theorem docstring.

Every hypothesis and clause is rendered as follows:

| Node text | Lean |
| --- | --- |
| Topological spaces X and Z | `{X : Type u} {Z : Type v}` and the two `TopologicalSpace` instances |
| Each space is sober | `[QuasiSober X] [T0Space X] [QuasiSober Z] [T0Space Z]`; Mathlib Sober.lean explicitly identifies these with sobriety, as does 004X after the definition |
| Finitely many irreducible components | `hXfinite : (irreducibleComponents X).Finite` and `hZfinite` |
| Disjoint components | `hXdisjoint : (irreducibleComponents X).PairwiseDisjoint id` and `hZdisjoint` |
| The components cover each space | Mathlib `sUnion_irreducibleComponents` (Irreducible.lean:353) proves this for every topological space; no extra hypothesis is necessary |
| All components are open and closed | `hXclopen : ∀ C ∈ irreducibleComponents X, IsClopen C` and `hZclopen` |
| A finite group H acts on X | `{H : Type w} [Group H] [Finite H] [MulAction H X]` |
| The action is by homeomorphisms | `[ContinuousConstSMul H X]` says every `x ↦ h • x` is continuous; the inverse is `x ↦ h⁻¹ • x` and is continuous by the same instance, so this is exactly an action by homeomorphisms, without requiring a topology on H |
| The named map q | `(q : X → Z)` |
| q is continuous | `hqcontinuous : Continuous q` |
| q is surjective | `hqsurjective : Function.Surjective q` |
| Images of closed sets are closed | `hqclosed : IsClosedMap q`, the exact predicate from Topology.Defs.Basic:166 |
| q is invariant | `hqinvariant : ∀ (h : H) (x : X), q (h • x) = q x` |
| Equal images iff points are in the same orbit | `hqfibres : ∀ x y : X, q x = q y ↔ ∃ h : H, y = h • x` |
| O is an orbit of components | `O : Set (Set X)` with `∃ C ∈ irreducibleComponents X, O = MulAction.orbit H C` |
| The union T_O | `⋃₀ O`, Mathlib's union of a family of subsets |
| q⁻¹(q(T_O)) = T_O | `q ⁻¹' (q '' (⋃₀ O)) = ⋃₀ O` |
| q(T_O) is open and closed | `IsClopen (q '' (⋃₀ O))` |
| q(T_O) = q(C) for every C in O | `∀ C ∈ O, q '' (⋃₀ O) = q '' C` |
| Each image is an irreducible component of Z | The `MapsTo` clause of `Set.BijOn ... (irreducibleComponents Z)` |
| O ↦ q(T_O) is a bijection onto all components of Z | The entire `Set.BijOn (fun O : Set (Set X) ↦ q '' (⋃₀ O)) {O | ∃ C ∈ irreducibleComponents X, O = MulAction.orbit H C} (irreducibleComponents Z)`; its remaining clauses are injectivity on this set of orbits and surjectivity onto the component set |
| η_C is generic for C | `∀ C ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η C → ...`; sobriety supplies its existence and uniqueness |
| q(η_C) is generic for q(C) | `IsGenericPoint (q η) (q '' C)` |
| Equality of the point and component stabilizers | `{h : H | h • η = η} = {h : H | h • C = C}` |
| Empty spaces allowed | No `Nonempty X`, `Nonempty Z`, component choice, or nonempty orbit-domain assumption; the generic point is quantified only after a component is given |

Dependency declarations read and used:

- `def-sc-generic-point`: the recorded Mathlib declaration `IsGenericPoint`
  from `Mathlib.Topology.Sober`, line 39, is exactly `closure {x} = S`.
  Its docstring, membership consequence, and uniqueness theorem were read.
- `def-weil-irreducible-components`: its `mathlib_match` is
  `irreducibleComponents` from `Mathlib.Topology.Irreducible`, line 107,
  defined as the maximal `IsIrreducible` subsets. I read `IsIrreducible`
  (line 52), closedness of components (line 111), and the cover theorem.
  This Mathlib leaf needs no replacement Lean record or dependency module.
- Both dependency modules are public imports. Both proof dependencies are
  those same nodes, so their imports also supply the entire proof plan.
- `MulAction.orbit` from `Mathlib.GroupTheory.GroupAction.Defs`, line 49,
  is `Set.range fun h ↦ h • C`. The set action from
  `Mathlib.Algebra.Group.Action.Pointwise.Set.Basic` uses the image scalar
  action in `Mathlib.Algebra.Group.Pointwise.Set.Scalar`, line 71.
  Thus the orbits in the theorem really are sets of component subsets,
  not point orbits or a new, arbitrary action on component labels.
- `ContinuousConstSMul` from `Mathlib.Topology.Algebra.ConstMulAction`,
  line 60, is continuity of every scalar action map.
- `Set.BijOn` from `Mathlib.Data.Set.Operations`, line 322, unfolds to
  `MapsTo ∧ InjOn ∧ SurjOn`. It specifies the actual image-of-orbit-union
  map rather than asserting an unspecified abstract equivalence.

Searches actually made (the msearch calls are logged in `searches.jsonl`):

- LeanFinder: “A closed surjective continuous map with finite group orbit
  fibres on spaces with finitely many disjoint clopen irreducible components
  induces a component orbit bijection and preserves generic points”.
  Eight hits: quotient covering trivializations, the irreducible-fibre
  component equivalence, and a Galois-category decomposition. No exact
  match: covering trivializations require disjoint translates, and the
  component equivalence assumes preirreducible fibres, whereas a finite
  orbit can be disconnected. I read the relevant signatures in
  Topology/Irreducible.lean:463–520.
- Loogle: `IsClosedMap, irreducibleComponents`; zero hits.
- msearch grep in `Topology`:
  `orbit.*irreducible|irreducible.*orbit|image_mem_irreducibleComponents`;
  five hits, all in Topology/Irreducible.lean, requiring irreducible fibres.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `orbit.*irreducible|irreducible.*orbit|closed.orbit.component|ClosedOrbitComponent`;
  only an unrelated `attribute [irreducible]` on the split-torus module's
  action/orbit declarations. No component-orbit statement.
- Required `grep -rn 'lem-sfb-closed-orbit-component-map'
  lean/WeilConjectures`: no hits.
- Name collision rg for `closedOrbitComponentMap|closed_orbit_component_map`
  across Mathlib, WeilConjectures, Sheaf, and `dag/lean_names_upstream.json`:
  no hits. The upstream-name index was consulted.

Edge cases checked before writing:

- Empty X and Z: there are no components and no O in the orbit domain,
  so `Set.BijOn` is the empty-to-empty bijection and the other clauses
  are vacuous. Surjectivity rules out empty X with nonempty Z; existence
  of q rules out nonempty X with empty Z.
- A two-point discrete X with the order-two swap, mapping to a singleton:
  there is one orbit of two components; its union maps to the unique
  target component. This confirms why a preirreducible-fibre theorem
  would not supply this statement.
- Trivial and nonfaithful actions: every component orbit can be a singleton,
  and stabilizers may be all of H. No freeness or effectiveness is assumed.
- One Sierpinski component: its dense generic point has the stated closure;
  the theorem is not restricted to closed generic points or T1 spaces.
- X, Z, and H use independent explicitly bound universes u, v, and w.
  No choice of a finite index type or a component rules out empty spaces.

Validation: prescribed `scompile.py ND lem-sfb-closed-orbit-component-map`
compiled the delivered file in sandbox and library module modes against
live server artifacts, with no error or warning (12.9 s and 2.4 s).

## Second reading by ND

I reread the node and delivered file clause by clause after the clean compile.
This is the author's second pass; the dispatcher explicitly prohibits starting
another agent, and the maintainer supplies the independent delivery review.
The match table above records this pass, including the hypotheses on Z that
are mathematically redundant but are retained because the node states them.
The orbit domain consists of orbits of actual irreducible-component subsets;
Mathlib's pointwise set action means `h • C` is the image of C under h.
I checked that the final `∀ C ∈ O` is inside the first conjunction and that
`Set.BijOn` includes membership in the target component set as well as both
bijection directions. The generic-point clause is quantified over every
component and its generic point, so it does not lose any component outside
a chosen orbit. Both sobriety assumptions mean existence plus uniqueness,
not just existence. No extra conclusion or missing hypothesis was found;
no changes were necessary in this pass. The single sorry is exactly the
node's theorem and its docstring contains all seven proof steps. There are
no new nodes, dependency modules, definition choices, or statement changes.
