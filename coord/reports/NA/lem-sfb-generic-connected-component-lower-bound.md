## Worker report

Item: `lem-sfb-generic-connected-component-lower-bound`.
Module: `Sheaf.AlgebraicGeometry.GenericConnectedComponentLowerBound`.
Declaration: `AlgebraicGeometry.exists_open_connectedComponents_fiber_lower_bound`.
The module states the unchanged node, with one theorem whose proof is `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 055D,
`lemma-connected-components-in-neighbourhood`, statement and full proof, lines
7847–7881. The source gives a nonempty open in an irreducible base; such an open
contains its generic point, and its proof explicitly constructs a neighbourhood
of that point. The node's neighbourhood formulation agrees with both. A search
of `literature/blueprint/latest/` for the tag, source label, and item id had no
matching blueprint statement, consistently with this supporting node's split report.
The declaration docstring gives all four DAG proof steps, their cited nodes,
and the zero-component case.

Hypothesis and conclusion mapping:

- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`; the universe `u`
  is explicit and arbitrary.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the conjunction
  in `def-weil-finite-type-morphism`. No finite-presentation condition is used.
- Nonempty irreducible base: `[IrreducibleSpace S]`. Mathlib's class extends
  `PreirreducibleSpace S` and includes `Nonempty S`; its definition is the
  condition that any two nonempty opens intersect.
- Specified generic point of all of S: `(η : S) (hη : IsGenericPoint η Set.univ)`.
  The recorded definition is exactly `closure {η} = Set.univ`.
- Natural number: `(n : ℕ)`.
- Ordinary scheme-theoretic generic fibre: `f.fiber η`, Mathlib's pullback along
  `S.fromSpecResidueField η`; no field extension or geometric fibre is introduced.
- Exactly n connected components: `hn : Nonempty (ConnectedComponents (f.fiber η)
  ≃ Fin n)`. An equivalence exists precisely when this component type has n
  elements; it does not supply any additional choice or structure as a hypothesis.
  `ConnectedComponents` is the quotient by equality of `connectedComponent` sets.
  `mem_connectedComponent`, `isConnected_connectedComponent`, and
  `IsConnected.subset_connectedComponent` identify these sets with exactly the
  maximal nonempty connected subsets in the node. Every such subset contains a
  point, and maximality identifies it with that point's component.
- Open neighbourhood: `∃ W : Set S, IsOpen W ∧ η ∈ W ∧ ...`. This includes
  nonemptiness because η is in W.
- Every point in that open: `∀ s ∈ W, ...`.
- At least n distinct ordinary connected components: `Nonempty (Fin n ↪
  ConnectedComponents (f.fiber s))`. An embedding is an injective function;
  its n images are the required distinct components. This permits more than n,
  including an infinite number, and adds no upper bound or finiteness hypothesis.
- The clause permitting the empty generic fibre and n = 0 requires no separate
  disjunct: equivalence to `Fin 0` says the generic component type is empty, and
  the empty embedding into every nearby component type exists.
- The negative restrictions in the node are respected: no Noetherian, flat,
  finite-presentation, separatedness, reducedness, or field-extension binder occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (their full structure signatures and docstrings).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; the node's quasi-compact clause uses
  `AlgebraicGeometry.QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`, with
  `fiberι`, `fiberToSpecResidueField`, and `fiberHomeo` read for the fibre's meaning.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, the recorded match of
  `def-weil-connected-scheme`, is exposed through the public import of
  `Mathlib.Topology.Connected.Clopen`; the latter provides `ConnectedComponents`.
  The component maximality proof dependency is the existing Mathlib leaf
  `isConnected_connectedComponent`, together with `mem_connectedComponent` and
  `IsConnected.subset_connectedComponent`.
- All three stated non-Mathlib proof dependencies are plain imports:
  `WeilConjectures.AlgebraicGeometry.GenericFibreClosedCoverSpread`, declaration
  `AlgebraicGeometry.exists_open_generic_fibre_closed_cover`;
  `WeilConjectures.AlgebraicGeometry.GenericFibreClosedAvoidance`, declaration
  `AlgebraicGeometry.exists_open_generic_fibre_closed_avoidance`;
  `WeilConjectures.AlgebraicGeometry.GenericClosedSubsetFibreNonempty`, declaration
  `AlgebraicGeometry.exists_open_closed_subset_fibre_nonempty`.
  Their full signatures and proof docstrings were read; their hypotheses are
  precisely finite type and the relevant closed-set/fibre conditions. No import
  cycle is introduced. The item retains all its original dependency lists.

Edge cases checked before writing:

- Empty X and n = 0: the component quotient is empty and the conclusion is
  the empty embedding, with W the whole base. No `Nonempty X` binder occurs.
- Empty generic fibre with nonempty special fibres: also allowed for n = 0;
  the conclusion only asserts the zero lower bound.
- n = 1: the generic fibre is nonempty connected; the assertion requires nearby
  fibres to be nonempty, without requiring them to remain connected.
- Components merging on a special closed locus (e.g. x(x-t) over k[t]): the
  conclusion permits removal of that locus; it asserts nothing outside W.
- Nonreduced or non-Noetherian irreducible bases and nonseparated X remain in
  the scope. No characteristic restriction is present.
- An empty base cannot have the bound point η or `IrreducibleSpace S`; excluding
  it agrees with the explicit nonempty hypothesis of the node.

Searches for an existing declaration (all successful searches, no exact match):

- `msearch.py ... leanfinder`: “For a finite type morphism over an irreducible
  scheme the ordinary fibres have at least as many connected components as the
  generic fibre on some open neighbourhood of the generic point”. Eight hits:
  finite-fibre finiteness, Jacobson fibres, discrete finite fibres,
  `specializingMap_isZariskiLocalAtTarget`, `IsDominant`,
  `genericPoint_eq_of_isOpenImmersion`, closed-point fibre containment, and
  `IsFinite.finite_preimage_singleton`. None states the lower bound.
- `msearch.py ... loogle`: `ConnectedComponents, AlgebraicGeometry.LocallyOfFiniteType`.
  Zero hits.
- `msearch.py ... grep`: `055D|connectedComponents.*(fiber|generic)|generic.*connectedComponents`.
  Zero hits.
- `msearch.py ... leansearch`: “The fibres of a finite type scheme morphism have
  at least n connected components near a generic point whose fibre has exactly n
  connected components”. Eight hits: `Scheme.Hom.fiber`, finite-fibre finiteness,
  finite preimages, locally quasi-finite finite maps, `LocallyQuasiFinite`,
  `IsFinite.recOn`, finite irreducible components for Noetherian schemes, and the
  canonical-over instance of a fibre. None is the asserted statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `055D|[Cc]onnected[Cc]omponents.*(fiber|generic)|generic.*[Cc]onnected[Cc]omponents|lem-sfb-generic-connected-component-lower-bound`
  found a topological pullback-fibre result and the parent generic-constancy
  theorem's proof citation, not this assertion. Its parent module was read.
- `grep -rn` of the item id in `lean/WeilConjectures` had no hit.
- `rg` for `exists_open_connectedComponents_fiber_lower_bound` in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` had no hit.
- Direct source searches/readings found the existing Mathlib component quotient,
  connected-component maximality, generic-point definition, and scheme fibre,
  so no private notion was introduced.

Validation: prescribed `scompile.py` compiled this file cleanly both as a sandbox
module (3.7 s) and as its intended library module (3.5 s), with no warnings.
The prescribed `deliver2.py --no-push` also passed the server preflight and
compilation (dry-run commit d1ec24bf527). There is no statement dispute or known
node fault.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
