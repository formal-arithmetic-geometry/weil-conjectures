## Worker report

The module `Sheaf.AlgebraicGeometry.GenericFibreAssassinContainmentSpreads` states
`AlgebraicGeometry.Scheme.Modules.genericFibreAssassinContainment_spreads`, with `sorry`.
It states Stacks Project Tag 05KP, `lemma-good-case`, read in full in
`literature/stacks-project/more-morphisms.tex`, lines 6940–7024. No definitions or
new nodes are needed. The node is unchanged except for its `lean` record.

The previous BLOCKED ending concerned the prohibition on reopening a reviewed stage-1
split. The current `coord/brief-stage2.md` §0 explicitly authorizes this stage-2 handoff;
the queue lists this item at stage 2, the node has no Lean record, and there is no repair
note. This delivery preserves the accepted stage-1 split.

Every hypothesis and conclusion is represented as follows:

- Schemes X and Y: `{X Y : Scheme.{u}}`, with the arbitrary universe `u` explicit.
- Morphism f: `(f : X ⟶ Y)`.
- Finite type of f: `[LocallyOfFiniteType f] [QuasiCompact f]`, the conjunction specified
  by the recorded finite-type node. This is not finite presentation.
- The O_X-module: `(F : X.Modules)`.
- Quasi-coherence and finite type of F: `(hF : F.IsQuasiCoherentFiniteType)`.
  This recorded definition unfolds to `SheafOfModules.IsQuasicoherent F ∧
  SheafOfModules.IsFiniteType F`; no coherence or finite presentation is assumed.
- The arbitrary open subscheme U: `(U : X.Opens)`. A scheme open set gives its canonical
  open subscheme, and its base change to a fibre has underlying set
  `(f.fiberι y) ⁻¹' (U : Set X)`. There is no compactness restriction on U.
- Irreducibility of the base: `[IrreducibleSpace Y]`, including its nonemptiness.
- Its specified generic point: `(η : Y) (hη : IsGenericPoint η Set.univ)`.
  An explicit generic-point argument retains the node's chosen point. The equation
  `closure {η} = Set.univ` is precisely the recorded generic-point definition.
- Scheme-theoretic fibre X_y: `f.fiber y`; its canonical projection is `f.fiberι y`.
- Tensor pullback F_y: `(tensorPullback (f.fiberι y)).obj F`.
- Associated fibre points: `associatedPoints ((tensorPullback (f.fiberι y)).obj F)`.
  These use element-annihilator associated primes of the stalk module, not weakly
  associated points or the total-space assassin.
- Generic containment: `hU` is the subset relation between that associated-point set
  for η and the preimage of U along the fibre projection.
- Existence of the base open: `∃ V : Y.Opens`.
- Nonemptiness: `(V : Set Y).Nonempty`.
- Containment for every y in V: `∀ (y : Y), y ∈ V →` followed by the same subset
  relation for the fibre at y.
- No Noetherian base hypothesis and no quasi-compact U hypothesis appear. In particular,
  neither reduction nor flatness from the proof is imposed on f or Y in the statement.

Recorded statement dependencies used, with their source declarations inspected:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `Scheme.Opens`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  used through the canonical open-subscheme encoding `X.Opens`.
- `Mathlib.Topology.Irreducible`: `IrreducibleSpace` (the irreducibility notion of
  the irreducible-components node); `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, the module recorded for
  `def-pc-module-pullback`, publicly supplies the original
  `WeilConjectures.AlgebraicGeometry.TensorPullback` declaration
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`. The actual tensor construction is
  reused, without choosing an arbitrary functor or map.
- `Sheaf.AlgebraicGeometry.RelativeAssassin`:
  `AlgebraicGeometry.Scheme.Modules.associatedPoints`. This module also exposes the
  canonical `Mathlib.AlgebraicGeometry.Fiber` declarations `Scheme.Hom.fiber` and
  `Scheme.Hom.fiberι`.

All proof dependencies with existing Lean/module or Mathlib matches have plain proof
imports (unless already a public statement dependency). The currently unstated proof
nodes `lem-trf-generic-flat-reduced-base-model`,
`lem-sfb-fibre-assassin-containment-base-change`,
`lem-sfb-affine-associated-points-primes`, and
`lem-trf-algebra-module-simultaneous-generic-flatness` have no module to import yet.
They supply proof steps, not notions missing from this statement. The theorem docstring
records all eleven accepted proof steps with their node citations.

Edge cases checked against the source and the encoded predicates:

- Empty X, and F = 0: all associated fibre sets are empty; V = Y is allowed.
- Empty U (including an empty generic fibre): the hypothesis forces an empty generic
  assassin, and the conclusion requires this on a nonempty base open. No nonempty
  fibre or nonzero F hypothesis was introduced.
- U = X: all containments hold and V = Y is allowed.
- Y a field spectrum: the statement still applies to its only point.
- Nonreduced irreducible Y and non-Noetherian integral bases are admitted; reduction
  and generic flatness belong to the proof alone.
- U need not be quasi-compact: only U on the generic fibre is made compact in the proof.
- The empty base is excluded exactly by the source's irreducibility hypothesis.
- The associated-point definition is the actual stalk annihilator condition; for the
  zero stalk its only element has annihilator the whole ring, which cannot be the
  proper maximal ideal. Thus the zero case is not spuriously associated.

Searches for an existing statement:

- `msearch.py ... leanfinder` with query “For a finite type morphism and finite type
  quasi coherent module, containment of generic fibre associated points in an open
  spreads to a nonempty base open”: 8 hits, on spreading morphisms from stalks,
  vanishing sections and restriction of opens. None asserts fibre-assassin containment.
- `msearch.py ... loogle` with query `"associatedPrimes", "IsOpen"`: 0 hits.
- `msearch.py ... grep` with query `assassin|associated.*generic|generic.*associated`:
  0 Mathlib hits.
- `msearch.py ... leansearch` with query “Containment of fibre associated points in an
  open spreads from the generic point of an irreducible base”: 8 generic-point and
  irreducible-component topology hits, none stating the node.
- `rg -n 'assassin|associated.*generic|generic.*associated' lean/WeilConjectures
  lean/Sheaf`: existing relative-assassin definitions/base change, flat relative
  specialization, generic fibre components, meromorphic sections, and weakly associated
  etale algebra. None is this generic-containment spreading statement.
- Literal item-id search in `lean/WeilConjectures`: no hits.
- Exact new declaration-name search in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`
  and `dag/lean_names_upstream.json`: no hits.

Validation: `scompile.py Q33 lem-sfb-generic-fibre-assassin-containment-spreads` compiled
this delivered module in both sandbox and library modes on the server (10.0 s and
8.6 s), with no errors or non-sorry warnings. Both `autoImplicit` and
`relaxedAutoImplicit` are disabled. There is exactly one theorem and its proof is
`sorry`. No statement fault or disputed assertion was found.

## Second reading by Q33

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
