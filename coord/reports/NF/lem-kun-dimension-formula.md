## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula` states
`AlgebraicGeometry.topologicalKrullDimAt_eq_stalk_dimension_add_residue_trdeg` with
proof `sorry`. It introduces no definitions and makes no statement correction.

Hypotheses and conclusion, clause by clause:
- The field K is `{K : Type u} [Field K]`.
- The K-scheme X is `(X : Scheme.{u}) [X.Over (Spec (.of K))]`, with structure morphism
  `X ↘ Spec (.of K)`. The common universe is that required by Mathlib's scheme category;
  it does not impose a geometric restriction (smaller fields can be lifted).
- Finite type is exactly the recorded dependency's conjunction, given by the two instances
  `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and `[QuasiCompact (X ↘ Spec (.of K))]`.
- The point is `(x : X)`.
- The left side `dim_x X` is the recorded `topologicalKrullDimAt x`.
- The local ring is `X.presheaf.stalk x`, and its dimension is `ringKrullDim` of that ring.
- The residue field is the recorded `X.residueField x`. The explicit final argument of
  `@Algebra.trdeg` is `((X ↘ Spec (.of K)).residueFieldAlgebraMap x).toAlgebra`.
  This is the canonical K-algebra structure, not an arbitrary algebra parameter.
- The conclusion is precisely equality with the sum. `Cardinal.toENat` maps a finite
  cardinal n to n and every infinite cardinal to infinity; coercion into `WithBot ℕ∞`
  puts this nonnegative dimension in the dimension type. Finite type over a field makes
  this transcendence degree finite, as in the existing affine input. No natural-number
  truncation or separate finiteness assertion changes the node's conclusion.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Over`: `AlgebraicGeometry.Scheme.Over` and the structure
  morphism notation; `def-weil-scheme-over-base` has a Mathlib match and needs no module.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`, exactly the
  infimum of dimensions of open neighbourhoods, and proof input
  `IsOpen.topologicalKrullDimAt_eq`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `WeilConjectures.ZetaSeries`: `AlgebraicGeometry.Scheme.Hom.residueFieldAlgebraMap`;
  its full definition composes the base-field algebra map, `Spec.residueFieldIso.inv`,
  and the structure morphism's `residueFieldMap`.
- `Mathlib.SetTheory.Cardinal.ENat`: `Cardinal.toENat` (its definition and finite/infinite
  behavior read in source).
- Proof-only import `Sheaf.RingTheory.DimensionAtPointLocalRingTrdeg` provides the recorded
  `AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_add_trdeg`.
  The remaining recorded proof inputs are in Mathlib's affine-scheme, finite-type and
  scheme modules already available transitively: `locallyOfFiniteType_iff`,
  `IsAffineOpen.fromSpec`, `IsAffineOpen.primeIdealOf`, `IsAffineOpen.fromSpec_primeIdealOf`,
  `IsAffineOpen.fromSpec_app_self`, `IsAffineOpen.isLocalization_stalk`,
  `IsOpenImmersion.instIsIsoCommRingCatStalkMap`, and `Scheme.Hom.germ_stalkMap`.
  Their source signatures and the affine formula's full signature and docstring were read.

Source checked: the complete blueprint node at order 1675 and local Stacks
`morphisms.tex`, `lemma-dimension-fibre-at-a-point` (02FX), whose proof reduces to affine
schemes over a field and Algebra 00P1. No separation, irreducibility, reducedness,
closed-point assumption, or characteristic restriction is present or introduced.

Edge cases checked mathematically: the empty scheme has no x, so the quantified assertion
is vacuous; `Spec K` gives 0 = 0 + 0; at the generic point of affine n-space the stalk
has dimension 0 and the residue transcendence degree is n; at a closed point it is 0
and the stalk dimension gives the local topological dimension. Reducible schemes use
the maximum of the local component dimensions as in the existing affine formula.
Nonreduced schemes have the same prime chains. Arbitrary characteristic is allowed.

Searches (2026-10-15, through `msearch.py NF lem-kun-dimension-formula`):
- LeanFinder: “For a scheme of finite type over a field dimension at a point equals local
  ring dimension plus residue field transcendence degree”: eight hits, including cotangent
  finrank lemmas, standard smooth relative dimension and the residue-field Field instance;
  none is this formula.
- Loogle: `Algebra.trdeg, ringKrullDim`: no hits.
- LeanSearch: “dimension finite type scheme local ring residue field transcendence degree”:
  service unavailable (Internal Server Error); no search verdict asserted.
- Mathlib grep: `trdeg.*[Dd]im|[Dd]im.*trdeg`: no hits.
- `rg` of upstream `WeilConjectures` and project `lean/Sheaf` with the same dimension/trdeg
  pattern plus `lem-kun-dimension-formula`: only affine/domain formulas, their uses, and
  unrelated finrank statements. The existing affine formula was opened; its object is
  `Spec S` at a prime, rather than the arbitrary scheme in this item.
- Searched `dag/lean_names_upstream.json`, Mathlib, upstream, and `lean/Sheaf` for the new
  declaration's prefix `topologicalKrullDimAt_eq_ringKrullDim_add_residue`: no collision.
  The chosen full name is also distinct from the existing affine theorem.

No disputed statement or node fault found. Server-only compilation and delivery dry run
are run with the authorized launcher tools; no local Lean compiler is used.

## Second reading by NF

I read the node statement and source (Stacks Project, Morphisms, Lemma 29.29.1, Tag 02FX)
clause by clause. The introduced objects and their Lean rendering are:

- A field `K` is `{K : Type u} [Field K]`; the universe is shared with the scheme as in
  the project convention and introduces no extra algebraic hypothesis.
- A scheme `X` over `K` is `(X : Scheme.{u}) [X.Over (Spec (.of K))]`, with structure
  morphism `X ↘ Spec (.of K)`.
- “Finite type over `K`” is exactly the two recorded properties
  `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and
  `[QuasiCompact (X ↘ Spec (.of K))]`; no Noetherian, separated, reduced, or finite
  presentation assumption is added.
- A point is `(x : X)`.
- The left side `\kundim_x X` is `topologicalKrullDimAt x`.
- The local term is `ringKrullDim (X.presheaf.stalk x)`.
- The residue term uses the node's `X.residueField x` and its canonical `K`-algebra
  `((X ↘ Spec (.of K)).residueFieldAlgebraMap x).toAlgebra` in `Algebra.trdeg`.
- The conclusion is the stated equality, with `Cardinal.toENat` coerced to `WithBot ℕ∞`
  before addition. Quantifier order and all clauses agree exactly with the node.

Edge cases were checked: an empty scheme has no point and is vacuous; `Spec K` gives zero
on both sides; generic and closed points of affine space give the expected residue and
local contributions; reducible and nonreduced schemes are covered; `n = 0` and arbitrary
characteristic impose no exception. The shared universe does not remove the cases covered
by the project's scheme-over-field convention.

I searched Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` by declaration
name and by `dimension`/`trdeg` concepts using LeanFinder, Loogle, LeanSearch, and `rg`;
the only related result is the affine input theorem, whose object is `Spec R` at a prime
and therefore is not this arbitrary-scheme statement. No duplicate declaration or missing
notion was found. The dependency declarations were opened and match their node signatures.

No mismatch was found, so no source or node change was needed. The module compiled cleanly
with `scompile.py`; the only proof placeholder is the named target theorem's `sorry`.
