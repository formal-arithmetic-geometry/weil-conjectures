## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg` states
`AlgebraicGeometry.topologicalKrullDim_closed_irreducible_eq_trdeg`, with proof `sorry`.
It introduces no definitions and changes only the item's `lean` field.

Hypothesis and conclusion correspondence:

- A field K: `{K : Type u} [Field K]`.
- A scheme X over K: `{X : Scheme.{u}} [X.Over (Spec (.of K))]`. The structure morphism
  is `X ↘ Spec (.of K)`, following the standing scheme-over-field convention.
- Finite type over K: `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and
  `[QuasiCompact (X ↘ Spec (.of K))]`, precisely the conjunction in the recorded dependency.
- A closed subset C of the underlying space: `(C : Set X) (hC : IsClosed C)`.
- Nonempty and irreducible: `(hCi : IsIrreducible C)`; Mathlib defines this as
  `C.Nonempty ∧ IsPreirreducible C`. No component/maximality condition is imposed.
- Its generic point η belongs to C: `(η : X) (hηC : η ∈ C)`.
- Genericity as stated in the node: `(hη : closure ({η} : Set X) = C)`.
- Dimension of the subspace: `topologicalKrullDim C` uses the subtype topology.
- The ambient generic residue field: `X.residueField η`, not the function field of X
  (X need not be integral).
- Its prescribed K-structure: `letI := ((X ↘ Spec (.of K)).residueFieldAlgebraMap η).toAlgebra`.
  This uses the source's canonical map; no arbitrary algebra structure is assumed.
- Equality of dimension and transcendence degree: `∃ d : ℕ,
  topologicalKrullDim C = (d : WithBot ℕ∞) ∧ Algebra.trdeg K (X.residueField η) = (d : Cardinal)`.
  A common natural value avoids equating different Lean types. Finiteness here is inherent:
  Stacks 0A21(6) reduces to a finite type domain on a nonempty affine chart and Algebra 00P0;
  the existing dependency `finiteType_domain_ringKrullDim_eq_trdeg` uses this same encoding.
  Thus this does not impose an extra hypothesis or exclude any instance of the node.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (locally ringed space
  with local affine charts) and its scheme morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Topology.Irreducible`: `IsIrreducible` (the subset notion supplied by
  def-weil-irreducible-components; `irreducibleComponents` is its maximal-subset construction).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`;
  `WeilConjectures.ZetaSeries`: `Scheme.Hom.residueFieldAlgebraMap`.

The module additionally imports the stated proof-dependency modules, including
`Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`,
`Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso`,
`Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and the relevant Mathlib
closed-immersion, immersion, properness, integral-scheme, function-field and ring-dimension modules.
The declaration docstring follows all six DAG proof steps. No cyclic proof import was needed.

Source checked: `literature/stacks-project/varieties.tex`,
`lemma-dimension-locally-algebraic`, item `item-dimension-irreducible-trdeg` (0A21/0B1C),
and its proof reducing to the affine reduced case and Algebra 00P0.

Edge cases: the empty C is excluded precisely by `IsIrreducible`, as in the node; consequently
X cannot be empty. C may be a point (common value 0), a proper subvariety, or all of X.
The ambient X may be reducible or nonreduced: no reducedness/integrality assumption is imposed.
K is arbitrary in characteristic and algebraic closure. No separatedness assumption is added.
The universe follows the project's scheme and base-field convention, with all binders explicit.

Searches (2026-10-15):

- `msearch.py ... leanfinder "The dimension of an irreducible closed subset of a scheme of
  finite type over a field equals the transcendence degree of the residue field at its generic
  point"`: eight hits, including Scheme.height_of_isClosed, residue-field and function-field
  declarations; none states the required equality.
- `msearch.py ... loogle '"topologicalKrullDim", "trdeg"'`: zero hits.
- `msearch.py ... leansearch "dimension irreducible closed subset finite type scheme field
  transcendence degree generic point"`: service unavailable (Internal Server Error).
- `msearch.py ... grep '(krullDim|KrullDim).*trdeg|trdeg.*(krullDim|KrullDim)'`: zero hits.
- `rg` of the source `WeilConjectures` and the side `lean/Sheaf` for closed/trdeg combinations
  and the node id: only the related ClosedPointField module, which concerns closed points and
  zero transcendence degree. The upstream FiniteType module supplies dimension invariance
  under nonempty opens and finite-dimension bounds, not this statement.
- Exact proposed declaration name searched in `dag/lean_names_upstream.json`, Mathlib,
  `WeilConjectures`, and `lean/Sheaf`: no collision.

Server verification: `scompile.py NH lem-sc-closed-irreducible-dimension-trdeg <module>` passed
cleanly (1.4 seconds; nice 19, two threads, 60-second limit). No local compiler was invoked.
No statement dispute, new nodes, dependency replacements, or statement corrections.

## Second reading by NH

I reread the node statement, its Stacks source, all six statement dependencies, and the
module signature clause by clause. The field is `{K : Type u} [Field K]`; the scheme is
`{X : Scheme.{u}} [X.Over (Spec (.of K))]`; and finite type is rendered by the two
unbundled assumptions `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and
`[QuasiCompact (X ↘ Spec (.of K))]`, exactly as the dependency node records. The subset,
closedness, nonempty irreducibility, point membership, and generic-point equation are
respectively `(C : Set X)`, `hC : IsClosed C`, `hCi : IsIrreducible C`, `hηC : η ∈ C`,
and `hη : closure ({η} : Set X) = C`. The conclusion uses the subspace dimension
`topologicalKrullDim C` and the ambient residue field `X.residueField η`, with a common
`d : ℕ` giving the two casts exactly as the node's Lean encoding of the dimension/trdeg
equality.

The first reading used a `letI` binder to install the canonical K-algebra on the residue
field. The stage-2 convention disallows let binders in statements, so I changed only this
rendering: the conclusion now supplies the canonical structure explicitly as
`@Algebra.trdeg K (X.residueField η) _ _
((X ↘ Spec (.of K)).residueFieldAlgebraMap η).toAlgebra`. This is definitionally the same
canonical residue-field algebra and adds no hypothesis or choice. The node's `lean.statement`
was updated verbatim to this signature. No other mismatch was found.

Edge cases checked: `IsIrreducible C` excludes the empty subset as required; zero-dimensional
points give `d = 0`; proper closed subsets and `C = Set.univ` are both allowed; `X` may be
reducible or nonreduced; no separatedness, integrality, characteristic, or algebraic-closure
assumption is present; and the universe is shared by `K`, `X`, and the residue field. The
canonical map works for every characteristic and the finite common value is represented by
`d : ℕ` on both target types.

I repeated searches with `msearch.py` LeanFinder/Loogle/grep queries for irreducible closed
subset dimension, `topologicalKrullDim` with `trdeg`, and `krullDim` with transcendence
degree, and searched Mathlib, `WeilConjectures`, and `lean/Sheaf` for the declaration name
and notion. The only hits were the component, residue-field, function-field, and generic
Krull-dimension declarations already recorded as dependencies; no existing theorem states
this result. The module compiled with `scompile.py` on the server after the explicit-algebra
change.
