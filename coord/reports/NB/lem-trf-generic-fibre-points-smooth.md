## Worker report

The module `lean/Sheaf/TraceFormula/GenericFibrePointsSmooth.lean` states
`AlgebraicGeometry.generic_fibre_points_smooth` with `sorry` proof.  The
statement has the following Lean rendering of the node:

- `Z S : Scheme.{u}` with `[IsNoetherian Z] [IsNoetherian S]` renders the two
  Noetherian scheme hypotheses.
- `(p : Z ⟶ S)` renders the morphism.
- `[Flat p]` renders flatness and `[LocallyOfFinitePresentation p]` renders
  finite presentation (the node's terminology).
- `hred : ∀ s : S, GeometricallyReduced (p.fiberToSpecResidueField s)` renders
  reducedness of every geometric fibre.
- `(s : S)`, `C : Set (p.fiber s)`, and
  `hC : C ∈ irreducibleComponents (p.fiber s)` render a chosen fibre and an
  irreducible component of it.
- `z : p.fiber s` and `hz : IsGenericPoint z C` render its generic point.
- The conclusion `∃ W : Z.Opens, p.fiberι s z ∈ W ∧ Smooth (W.ι ≫ p)` says
  exactly that the image of `z` has an open neighbourhood on which `p` is
  smooth.

The declaration uses the dependency notions as follows: `AlgebraicGeometry.Flat`
from `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`AlgebraicGeometry.LocallyOfFinitePresentation` from
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`IsNoetherianRing` from `Mathlib.RingTheory.Noetherian.Defs` only as the
recorded Noetherian-ring dependency behind the scheme class,
`CategoryTheory.Limits.pullback`/`AlgebraicGeometry.Scheme.Hom.fiber` and
`AlgebraicClosure` from `Mathlib.AlgebraicGeometry.Fiber` for geometric fibres,
`irreducibleComponents` from `Mathlib.Topology.Irreducible`,
`IsGenericPoint` from `Mathlib.Topology.Sober`, and
`AlgebraicGeometry.Smooth` from
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`.

The edge cases checked were an empty fibre (the component hypothesis is then
uninhabited), a one-point field fibre (the unique point is generic and the
conclusion is the expected smooth neighbourhood), a reducible Noetherian fibre
with several components, and a nonreduced fibre such as
`Spec (k[x]/(x^2))`, which is excluded by `hred`.  The finite-component step is
needed because a dense open need not contain generic points in a space with
infinitely many components.

Searches performed:

- `msearch.py NB lem-trf-generic-fibre-points-smooth leanfinder "A flat
  finitely presented morphism with geometrically reduced fibres is smooth at
  generic points of fibres"`: only generic smoothness interfaces; no exact
  match.
- `msearch.py ... loogle "Smooth, GeometricallyReduced"`: no result.
- `msearch.py ... grep "smooth.*generic|GeometricallyReduced" AlgebraicGeometry`:
  reduced/smooth infrastructure only; no exact theorem.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/TraceFormula` for
  generic-fibre smoothness: no declaration of this statement; nearby fibre and
  smoothness declarations are weaker or differently scoped.

No statement correction, new definition node, or dependency-module repair was
needed.  The prior Q85 delivery was a stage-1 split; this delivery supplies the
stage-2 Lean statement and changes only the copied node's `lean` field.

## Second reading by NB

I reread the node statement, its recorded declaration, and the source tags
056V and 01V9. The Lean signature preserves every hypothesis and clause:
`Z` and `S` are schemes in the same universe with their two `IsNoetherian`
instances; `p : Z ⟶ S` has the `Flat` and
`LocallyOfFinitePresentation` instances; `hred` quantifies over every
`s : S` and asserts `GeometricallyReduced` for the geometric fibre; `s`, `C`,
`hC`, `z`, and `hz` select an irreducible-component generic point of the
ordinary fibre. The conclusion is exactly an open `W : Z.Opens` containing
`p.fiberι s z` with `Smooth (W.ι ≫ p)`. No hypothesis, object, or conclusion
was added, removed, specialized, or weakened.

I checked that the imported declarations render the dependency notions used by
the statement: `Scheme.Hom.fiber`, `fiberι`, and
`fiberToSpecResidueField` for fibres, `irreducibleComponents` and
`IsGenericPoint` for the component and generic point, and `Smooth` for the
relative smoothness conclusion. The module has no new definition and its only
proof is `sorry`, as required for stage 2. The earlier packet’s Lean module,
node fields other than `lean`, source attribution, and report discussion are
unchanged; this repair adds only the required second-reading record.
