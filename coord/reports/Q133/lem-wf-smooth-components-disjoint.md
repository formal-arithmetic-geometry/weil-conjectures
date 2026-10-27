## Worker report

The module `Sheaf.AlgebraicGeometry.RegularClosedPointComponents` states
`AlgebraicGeometry.components_of_regular_closed_points`, with its whole proof
`sorry`. It supplies the scheme formulation of the node. No definitions,
additional assumptions, new nodes, dependency repairs or statement corrections
are needed. The accepted stage-1 split and every non-lean field are unchanged.

The previous BLOCKED ending concerned stage 1, not this delivery. The current
`coord/brief-stage2.md` section 0 explicitly permits stage 2 after that refusal.
The live node is split, reviewed by NN, has no Lean record, and is listed at
stage 2 in `coord/queue.tsv`. There is no released repair note for this item.

Source read: `literature/blueprint/latest/blueprint/sec-algebraic-groups-lie-algebras/`
`sk-p-geometry/lem-wf-smooth-components-disjoint.md` and its `.proof.md`.
The source statement agrees verbatim with the node, including regularity only
at closed points. The file's six proof paragraphs follow the accepted six-step
DAG proof, naming its dependencies explicitly.

Hypotheses and conclusions, clause by clause:

| Node | Lean |
| --- | --- |
| A field k | `{k : Type u} [Field k]` |
| An affine scheme X | `(X : Scheme.{u}) [IsAffine X]` |
| X over k | `[X.Over (Spec (.of k))]`, whose structure morphism is `X ↘ Spec (.of k)` |
| Of finite type | `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and `[QuasiCompact (X ↘ Spec (.of k))]`, precisely the dependency's definition |
| Every closed point has a regular local ring | `hreg : ∀ x : X, x ∈ closedPoints X → IsRegularLocalRing (X.presheaf.stalk x)` |
| Finitely many irreducible components | `(irreducibleComponents X).Finite` |
| Any two distinct irreducible components are disjoint | `(irreducibleComponents X).Pairwise Disjoint`; `Set.Pairwise` quantifies two members and requires inequality |
| Every irreducible component is open and closed | `∀ C ∈ irreducibleComponents X, IsClopen C` |
| These are exactly the connected components | `irreducibleComponents X = Set.range (fun x : X => connectedComponent x)` |

The parenthetical smooth-variety example is explanatory, not an extra hypothesis.
The final equality asserts both directions, including that every connected
component arises; it does not merely assert that irreducible components are
connected. There is no assumption of nonemptiness, smoothness, perfectness,
algebraic closedness, or regularity at nonclosed points. Universes are declared
explicitly, with `set_option autoImplicit false` and no implicit autobinders.

Statement dependencies read and reused (full signatures/docstrings read):

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; affineness uses `IsAffine` from
  `Mathlib.AlgebraicGeometry.AffineScheme`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-regular-scheme`: its ring clause is the recorded mathlib match
  `IsRegularLocalRing`, `Mathlib.RingTheory.RegularLocalRing.Defs`.
  Its recorded module `Sheaf.AlgebraicGeometry.IsRegularScheme` is publicly
  imported. The scheme predicate `IsRegularScheme` is not assumed: it would
  strengthen the node's closed-point hypothesis to every point.
- `def-weil-closed-points`: `closedPoints`, `Mathlib.Topology.JacobsonSpace`.
- `def-weil-irreducible-components`: `irreducibleComponents`,
  `Mathlib.Topology.Irreducible`.
- `def-weil-connected-scheme`: `ConnectedSpace` and the corresponding maximal
  connected subsets `connectedComponent`, `Mathlib.Topology.Connected.Basic`.
  The latter is defined as the union of preconnected subsets through a point;
  these subsets are nonempty, hence connected, exactly as the node requires.

All stated proof dependencies are imported, with plain imports when they are
not also needed by the statement. Their declarations were inspected:
`affine_finiteType_algebra_of_field` in
`Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra`;
`PrimeSpectrum.zeroLocus_minimalPrimes` in
`Mathlib.RingTheory.Spectrum.Prime.Topology`;
`Ideal.exists_le_maximal` in `Mathlib.RingTheory.Ideal.Maximal`;
`IsAffineOpen.fromSpec_app_self`, `IsAffineOpen.fromSpec_primeIdealOf`,
`IsAffineOpen.isLocalization_stalk` in `Mathlib.AlgebraicGeometry.AffineScheme`,
`IsIso` for open-immersion stalk maps in `Mathlib.AlgebraicGeometry.OpenImmersion`,
and `Scheme.Hom.germ_stalkMap` in `Mathlib.AlgebraicGeometry.Scheme`;
`IsRegularLocalRing.isDomain` in
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`;
`Localization.AtPrime` in `Mathlib.RingTheory.Localization.AtPrime.Basic`;
`Algebra.FiniteType.isNoetherianRing` in `Mathlib.RingTheory.FiniteType`,
the Noetherian spectrum instance in `Mathlib.RingTheory.Spectrum.Prime.Noetherian`,
and `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents` in
`Mathlib.Topology.NoetherianSpace`;
`exists_mem_irreducibleComponents_subset_of_isIrreducible`,
`mem_irreducibleComponent`, `irreducibleComponent_mem_irreducibleComponents`
in `Mathlib.Topology.Irreducible`;
`IrreducibleSpace.connectedSpace`, `mem_connectedComponent`,
`isConnected_connectedComponent`, `IsConnected.subset_connectedComponent`
in `Mathlib.Topology.Connected.Basic`.

Edge cases checked before writing:

- Empty affine scheme (zero coordinate ring): no closed points, no nonempty
  irreducible components, and the range of connectedComponent is empty. All
  four conjuncts hold; the signature imposes no Nonempty X.
- `Spec k`: one irreducible/connected component; pairwise disjointness only
  concerns distinct members, so no self-disjointness is asserted.
- `Spec (k × k)`: two clopen singleton components, both connected components.
- `Spec k[s,t]/(s*t)`: the origin is closed and its local ring is not regular,
  so the intersecting components do not contradict the stated hypothesis.
- `Spec k[e]/(e^2)`: its closed stalk is not regular, so the hypothesis fails;
  neither reducedness nor integrality is silently assumed in the signature.
- Arbitrary field characteristic is permitted. The conclusion refers to
  components over k, without passing to an algebraic closure.

Searches for an existing statement (2026-10-24):

- msearch.py leanfinder: "An affine scheme of finite type over a field with
  regular local rings at all closed points has pairwise disjoint clopen
  irreducible components equal to its connected components". Eight hits,
  including scheme Noetherian finiteness and a clopen-set union of connected
  components; none states the regular-closed-point scheme implication.
- msearch.py leansearch: "An affine scheme of finite type over a field whose
  stalks at closed points are regular has disjoint irreducible components
  which are clopen and equal to connected components". Eight hits, including
  `finite_irreducibleComponents_of_isNoetherian`, `isAffine_Spec`, and the
  Noetherian-space instance; no full match.
- msearch.py loogle: "irreducibleComponents, IsClopen". Zero hits.
- msearch.py grep:
  "disjoint.*irreducibleComponents|isClopen.*irreducibleComponents|connectedComponent.*irreducibleComponents".
  Zero Mathlib hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the same component names,
  and grep for the item id in `lean/WeilConjectures`, found the three results
  `PrimeSpectrum.disjoint_of_mem_irreducibleComponents`,
  `PrimeSpectrum.isClopen_of_mem_irreducibleComponents`, and
  `PrimeSpectrum.connectedComponent_eq_of_mem_irreducibleComponents` in
  `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`.
  Their full docstrings and signatures were read: they take a ring A and
  regularity of its maximal localizations, not a scheme X and its closed
  stalks. They are used through the proof import, not restated at ring level.
  The stage-1 reviewer also explicitly distinguished them from the scheme
  statement. The other hit,
  `disjoint_of_mem_irreducibleComponents_of_forall_closedPoints` in
  `WeilConjectures.Mathlib.Topology.JacobsonSpace`, assumes transitivity of
  homeomorphisms on closed points instead of regular stalks; its signature
  and docstring were read and it is not the item.
- rg for `components_of_regular_closed_points` in `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing name.

Validation: prescribed scompile.py compiled the module in sandbox and library
positions, cleanly in 16.3 s and 6.3 s, respectively. No compiler diagnostics.
The sole postponed proof belongs to the item and carries the complete proof
plan with source and blueprint references in its docstring.

## Second reading by Q133

A second pass by this same worker reopened the exact node and module. No
independent worker was started, following the dispatcher's explicit prohibition;
the maintainer's independent delivery review remains required. This paragraph
records only the worker's own second pass.

Checked the field and scheme binders, affineness, the canonical structure
morphism, and both finite-type classes against the first sentence. Checked
that `hreg` is restricted to `closedPoints X` and uses the actual stalk, rather
than assuming IsRegular X or smoothness. Expanded the meaning of Set.Pairwise
to verify the distinctness premise. Read each of the four conjuncts against
the final two sentences; finiteness is explicit, IsClopen includes both open
and closed, and the equality with the range includes all connected components.
Rechecked the empty range when X is empty and absence of Nonempty X. The only
sorry is the theorem proof, with no new data definition. No mismatch or node
fault was found and no statement was changed.
