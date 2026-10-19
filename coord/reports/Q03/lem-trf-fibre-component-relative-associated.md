## Worker report

The module `Sheaf.TraceFormula.FibreComponentRelativeAssociated` states
`AlgebraicGeometry.fibre_component_relative_associated`.  It binds schemes `X`
and `S`, a morphism `f`, the typeclass hypotheses `[Flat f]` and
`[LocallyOfFiniteType f]`, a point `t : S`, a component `C` of the scheme
theoretic fibre, and a point `y` of that fibre.  The hypotheses `hC` and `hy`
say respectively that `C` is an irreducible component and that `y` is its
generic point.  The conclusion has two conjuncts: `y` is in the existing
`AlgebraicGeometry.associatedPoints` set of the fibre, and the image of `y`
under `f.fiberι t` belongs to the union over all `s : S` of the images of the
associated-point sets of `f.fiber s`.  This displayed union is the relative
assassin described by the node statement.

The Lean rendering of each hypothesis is:

- “`f : X → S` is flat” is `[Flat f]`.
- “`f` is locally of finite type” is `[LocallyOfFiniteType f]`.
- “`t ∈ S`” is `(t : S)`.
- “`C` is an irreducible component of `X_t`” is
  `(C : Set (f.fiber t))` together with
  `hC : C ∈ irreducibleComponents (f.fiber t)`.
- “`y` is the generic point of `C`” is
  `(y : f.fiber t)` together with `hy : IsGenericPoint y C`.

The Lean rendering of each conclusion clause is:

- “`y` is associated to the fibre structure sheaf” is
  `y ∈ associatedPoints (f.fiber t)`, using the existing definition node
  `def-sc-associated-points`.
- “`f.fiberι t y` belongs to the relative assassin” is
  `f.fiberι t y ∈ ⋃ s : S, (f.fiberι s) '' associatedPoints (f.fiber s)`.
  The image and union explicitly implement the node's fibrewise union.

The module uses the recorded declarations `AlgebraicGeometry.Flat` from
`Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`AlgebraicGeometry.LocallyOfFiniteType` from
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`AlgebraicGeometry.Scheme.Hom.fiber` and `Scheme.Hom.fiberι` from
`Mathlib.AlgebraicGeometry.Fiber`, `IsGenericPoint` from
`Mathlib.Topology.Sober`, `irreducibleComponents` from
`Mathlib.Topology.Irreducible`, and `AlgebraicGeometry.associatedPoints` from
`Sheaf.AlgebraicGeometry.AssociatedPoints`.  The latter is the dependency
node `def-sc-associated-points`; the other five are the Mathlib matches
recorded by the dependency nodes.  No dependency module or new definition
node was needed.

I checked the edge cases represented by the statement: an empty fibre has no
`y` satisfying the generic-point hypothesis; for `Spec K` the unique point is
associated; for `Spec (K[e]/(e^2))` the nilpotent generic point is still
associated, so reducedness is not assumed; and for `Spec K[u,v]/(uv)` each
minimal component generic point is covered.  The union includes the chosen
fibre at `s = t`; no nonempty-fibre or Noetherian-base hypothesis was added.

Searches made before writing the module:

- `msearch.py Q03 lem-trf-fibre-component-relative-associated leanfinder
  "generic point of an irreducible component of a fibre of a flat morphism is
  associated point of the structure sheaf"`: returned only generic-point,
  fibre-stalk, and flatness declarations; no full match.
- `msearch.py ... loogle "AlgebraicGeometry.Flat, genericPoints.ofComponent"`:
  zero hits.
- `msearch.py ... grep "associated.*point|genericPoints|irreducibleComponents
  Mathlib/AlgebraicGeometry Mathlib/Topology"`: only unrelated topology and
  elliptic-curve occurrences; no full match.
- Repository `rg` for the item id, `relative assassin`, `associatedPoints`,
  and fibre-component generic points found no existing theorem for this item.
- The existing project declaration `associatedPoints` was opened and reused;
  it is the exact stalkwise associated-point notion required by the dependency.

The file was compiled with the required `scompile.py` wrapper.  The first run
identified a private import of `associatedPoints`; changing that import to a
public import fixed the issue, and the clean compile then passed for both the
sandbox and library copies.  No statement correction, disputed statement,
new node, or dependency module is present.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
