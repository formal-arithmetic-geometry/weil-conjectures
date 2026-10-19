## Worker report

The module `Sheaf.AlgebraicGeometry.DimensionExtension` states
`AlgebraicGeometry.topologicalKrullDim_fieldExtension_and_denseOpen` with its entire proof
postponed by `sorry`. No definition, helper theorem, or node correction is introduced.
The declaration docstring gives all nine steps of the DAG proof, including the empty case,
affine-chart argument, Noetherianity and the component/residue-field argument.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- A field K: `{K : Type u} [Field K]`.
- A scheme X over K: `{X : Scheme.{u}} [X.Over (Spec (.of K))]`; its structure map is
  `X ↘ Spec (.of K)`.
- Finite type over K: the two instances `LocallyOfFiniteType (X ↘ Spec (.of K))` and
  `QuasiCompact (X ↘ Spec (.of K))`, exactly the recorded finite-type convention.
- Every field extension L/K: the first conjunct universally quantifies `(L : Type u)`
  with `[Field L] [Algebra K L]`; its specified embedding is `algebraMap K L`.
- X_L: `pullback (X ↘ Spec (.of K))
  (Spec.map (CommRingCat.ofHom (algebraMap K L)))`, explicitly typed as `Scheme.{u}`.
  This is the scheme base-change convention in the dependency record, with its actual
  structure map, rather than an arbitrary scheme or tensor product of global sections.
- Its dimension equals dimension of X: the first conjunct is exactly
  `topologicalKrullDim X_L = topologicalKrullDim X`.
- Every open dense immersion U into X: the second conjunct independently quantifies
  `(U : Scheme.{u}) (j : U ⟶ X) [IsOpenImmersion j]`, with hypothesis `DenseRange j`.
  `DenseRange` is definitionally density of `Set.range j`, the open image of the immersion.
- The second equality is `topologicalKrullDim U = topologicalKrullDim X`.

All universes are explicitly declared. K, L and the schemes are placed in a common
ambient universe, as required to form their pullback in the category of schemes;
there is no independent small universe for test objects. No characteristic,
irreducibility, reducedness, smoothness, separatedness, or nonemptiness hypothesis occurs.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.Topology.KrullDimension`: the recorded `topologicalKrullDimAt`
  was read; the global dimension in this node uses `topologicalKrullDim`, also explicitly
  listed in def-kun-dimension, originally defined in `Mathlib.Topology.KrullDimension`.
  It is `krullDim (IrreducibleCloseds X) : WithBot ℕ∞`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and its `algebraMap`.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: read the recorded module, including
  `AlgebraicGeometry.Scheme.Modules.moduleBaseChange` and its docstring, and followed its
  explicit scheme base-change convention `Limits.pullback f T.hom`. The module-pullback
  declaration is for the separate module clause of that dependency and is not substituted
  for scheme base change. The actual `CategoryTheory.Limits.pullback` signature and
  docstring were also read in Mathlib.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.

Recorded proof dependencies with Lean interfaces are imported without `public` unless
already a statement dependency. These include the matching affine covers, tensor-product
field-extension dimension, closed irreducible dimension/trdeg, and the Mathlib topological,
Noetherian, residue-field and morphism-property interfaces. The existing open-cover bound
comes from the public dimension dependency. Unstated proof-only nodes require no new
statement in order to state this theorem.

Edge cases checked mathematically before writing:

- X empty: the pullback and every source U are empty; all dimensions are bottom, not zero.
- U empty: density forces X empty. An empty open in a nonempty X cannot meet the density
  hypothesis.
- Zero-dimensional X and zero coordinate rings: dimension uses `WithBot ℕ∞`, retaining
  the distinction between empty and nonempty dimension-zero schemes.
- Reducible X, including components of unequal dimensions: a dense open meets every
  component, and the maximum of the component dimensions is unchanged.
- L = K and arbitrary algebraic or transcendental L/K: all are included; no finiteness
  condition is placed on L/K or on the base-change projection.
- Positive characteristic, nonreduced schemes and nonseparated finite type schemes are
  included without extra assumptions. A merely nonempty open need not preserve dimension
  in the reducible case; the necessary density condition is present.

Searches for an existing declaration:

- `msearch.py`, LeanFinder: “Krull dimension of a finite type scheme is invariant under
  field extension and dense open immersion”. Eight hits, including
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, standard-smooth dimension and
  localization bounds; no two-clause scheme theorem.
- `msearch.py`, Loogle: `topologicalKrullDim, DenseRange`; zero hits.
- `msearch.py`, LeanSearch: “Dimension of a finite type scheme over a field is invariant
  under base field extension and dense open restriction”; service unavailable, Internal
  Server Error. The independent search methods above and below were used.
- `msearch.py`, Mathlib grep: `topologicalKrullDim.*(pullback|baseChange|dense)|ringKrullDim.*tensor`;
  one hit in KrullDimension/Polynomial rewriting by a polynomial tensor equivalence,
  not the required result.
- `rg` in the source project and `lean/Sheaf` with the corresponding dimension/pullback,
  baseChange and dense patterns: fibre dimension bounds and specialized curve results.
  Read `BaseChangeDimension.lean`: `baseChange_dim` requires a curve and algebraically
  closed fields. Read `GroupScheme/IdentityLocalDimension.lean`: its field-extension
  helper is private, assumes nonempty X, and has no dense-open clause. Neither can be
  attached as the present statement. The affine tensor theorem is a proof dependency.
- `grep -rn lem-kun-dimension-extension` in the upstream WeilConjectures source: no hit.
  Searches for `dimension_extension`, `dimension_dense` and dimension/Dense variants
  found no usable existing declaration of the whole node.

The blueprint source was read from the launcher's local literature mirror (the shared
checkout omits the literature bodies). Its statement agrees verbatim with the DAG.
The DAG proof has already repaired the blueprint proof's claim that an arbitrary field
extension projection is finite type; the docstring follows that repaired DAG proof.
No statement fault or STATEMENT-DISPUTED finding remains.

Validation: file-only compilation uses the prescribed `scompile.py`; the initial elaboration
needed the explicit `: Scheme.{u}` annotation on the pullback, since dimension expects a type.
The final module compiles cleanly. The required `deliver2.py --no-push` dry run printed
OK: compilation and preflight pass except for the independent second reading, which the
second reader supplies. Nothing was pushed.

## Second reading by NP

I read the node `sec-smooth-purity/lem-kun-dimension-extension.json`, its dependency
records, and the source places before comparing the Lean file line by line. The node
introduces the following objects and clauses:

1. A field `K`, a scheme `X` over `Spec K`, and the finite-type hypothesis on its
   structure map.
2. For every field extension `L/K`, the base change `X_L` and the equality
   `\kundim X_L=\kundim X`.
3. For every open immersion `j : U \hookrightarrow X` with dense range, the equality
   `\kundim U=\kundim X`.

The Lean renders item 1 as `{K : Type u} [Field K]`, `{X : Scheme.{u}}`
`[X.Over (Spec (.of K))]`, `[LocallyOfFiniteType (X ↘ Spec (.of K))]`, and
`[QuasiCompact (X ↘ Spec (.of K))]`. These are exactly the recorded finite-type
convention and introduce no separatedness, Noetherianity, characteristic, smoothness,
reducedness, or nonemptiness assumption.

For item 2, the first conjunct is `∀ (L : Type u) [Field L] [Algebra K L]` followed by
`topologicalKrullDim (pullback (X ↘ Spec (.of K))
(Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}) =
topologicalKrullDim X`. Thus the map is the specified algebra map and the scheme is the
actual categorical pullback from the base-change dependency; it is not an arbitrary
scheme or a tensor product of global sections. The equality uses the same global
`topologicalKrullDim` as `def-kun-dimension`.

For item 3, the second conjunct is `∀ (U : Scheme.{u}) (j : U ⟶ X)
[IsOpenImmersion j], DenseRange j → topologicalKrullDim U = topologicalKrullDim X`.
The open-immersion class is Mathlib's `AlgebraicGeometry.IsOpenImmersion`, and
`DenseRange j` is exactly density of the image. The implication and quantifier order
match the node; no nonempty-open shortcut is used.

The source checks agree: Stacks Tag 00P3 states invariance for an arbitrary field
extension of a finite-type field algebra, and Tag 0A21(8) states the component generic
point dimension formula used for the dense-open argument. Tag 01T0 supplies the finite
type convention. The empty scheme, empty open, zero-dimensional schemes, reducible
schemes, identity/algebraic/transcendental extensions, positive characteristic, and
nonreduced or nonseparated schemes are all covered. Dimensions retain `WithBot ℕ∞`, so
the empty case is bottom rather than being silently identified with zero.

I searched the project and upstream source with `rg`, and ran the prescribed LeanFinder,
Loogle, grep, and LeanSearch queries. LeanFinder returned only general spectrum,
localization, and smooth-dimension results; Loogle and grep returned no matching theorem;
LeanSearch was unavailable (Internal Server Error). No existing declaration states both
clauses, so the module is required. The dependency declarations were opened, including
`topologicalKrullDim`, `Scheme`, `Algebra`, `LocallyOfFiniteType`, `QuasiCompact`,
`IsOpenImmersion`, and the recorded base-change convention; each supplies exactly the
notion used above.

No mismatch was found. In particular, the explicit `Scheme.{u}` annotation on the
pullback is necessary for elaboration but does not alter the mathematical object, and no
extra hypothesis or weakened clause was introduced. I changed no Lean statement or node
field. `scompile.py` compiles the module cleanly, and the delivery dry run passes.
