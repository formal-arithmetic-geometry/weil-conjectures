## Worker report

The delivery states `CategoryTheory.isVersalAtField_finite_residue_extension` in
`Sheaf.AlgebraicGeometry.ArtinPointwiseVersalFieldExtension`. Its proof is `sorry`;
the docstring gives all five accepted DAG proof steps, including the square-zero
iteration, full faithfulness and cancellation of the prescribed isomorphism.
There is no statement correction and no disputed clause.

Hypotheses and clauses of the item, in order:

- The commutative Noetherian base is `(R : Type u) [CommRing R]
  [IsNoetherianRing R]`; its affine spectrum is `Spec (.of R)`.
- Schemes and base maps are Mathlib `Scheme.{u}` and `Over (Spec (.of R))`.
  The explicit universes `u v w` allow arbitrary total-category object and arrow
  sizes; test rings and fields use the same `u` as the schemes. No independent
  smaller test universe or forced equality of total-category universes occurs.
- The fibred groupoid is `F : BasedCategory.{v,w} (Over ...)` with
  `hF : IsFibredInGroupoids F`, using the existing CFG definition. Every arrow is
  strongly cartesian, so its over-map data is exactly a pullback isomorphism.
  Existing cartesian universal properties supply coherent pullbacks without a
  chosen cleavage.
- The Rim--Schlessinger hypothesis is `hRS`. Its four rings `A B C D` denote
  the common overlap, two branches, and pushout vertex. They are arbitrary
  commutative rings, with arbitrary compatible structure maps to Spec R.
  `q : C ⟶ A`, its surjectivity, `(RingHom.ker q.hom)^2 = ⊥`, and
  `j.left = Spec.map q` express precisely the square-zero closed immersion.
  `IsPushout i j k l` identifies the vertex with Spec of the ring pullback.
  Fibres `x₀,y,z` and arrows `a,b` over `i,j` encode the two objects and
  specified overlap isomorphism. The conclusion glues them to `t` with arrows
  `c,d` over `k,l`, and `IsPushout a b c d` glues all compatible arrows uniquely.
  This is the total-category form of the canonical restriction equivalence,
  exactly as in the existing `algebraicModuliStack_rimSchlessinger` interface.
  Full faithfulness gives its pushout universal property for targets over any
  scheme: use the base pushout to get its structural map, pull the target back
  to the vertex, then apply full faithfulness in that fibre. Conversely this
  universal property gives full faithfulness and existence gives essential
  surjectivity. All overlap isomorphisms and automorphisms are retained. There
  are no Artinian, finite-type or nilpotence restrictions on `hRS` beyond the
  item's square-zero condition.
- `U : Over ...` and `[LocallyOfFiniteType U.hom]` express the locally finite
  type family; `x : Functor.Fiber F.p U` is the specified object.
- `u₀ : U.left` is the point, with finite-type residue-point map expressed by
  both `LocallyOfFiniteType` and `QuasiCompact` in `hft`. The field is the
  actual `U.left.residueField u₀`, with its canonical `fromSpecResidueField`.
- `hx : IsVersalAtField F x ...` expands to precisely the stated versality:
  commutative Artinian local `A', A`, a surjection `q`, a surjection
  `r : A → κ(u)`, an R-structure `s'`, an over-map `a` reducing to the point,
  an object `y'` over A', its restriction `y` over A with cartesian arrow `j`,
  and the specified pullback identification `z : y.val ⟶ x.val` over `a`.
  The two surjections give residue identifications because a surjection from
  a local ring onto a field has exactly its maximal ideal as kernel. Using
  `r ∘ q` for A' captures all compatible pairs of residue identifications.
  The existential `b,t` supplies the lifted map and isomorphism, with
  `Spec.map q ≫ b.left = a.left` and `j ≫ t = z` imposing the two exact
  extension conditions. The R-structures and their compatibilities are
  carried by `Over`; no coefficient-field embedding in A or A' is imposed.
- `(L : Type u) [Field L] [Algebra (U.left.residueField u₀) L]
  [Module.Finite ... L]` is any finite field extension. There is no separability
  condition. The concluding `IsVersalAtField` uses the actual composite
  `Spec.map (CommRingCat.ofHom (algebraMap ... L)) ≫ fromSpecResidueField`.
  Expanding that predicate gives every B', B, b, eta, prescribed isomorphism,
  lift b' and extending isomorphism in the conclusion of the item.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (ideals finitely generated).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, with `Module.Finite` for finiteness.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`. Its node is added to stmt_deps because
  the item's CFG notion now uses this existing declaration directly.
- `Sheaf.AlgebraicGeometry.PointwiseVersalLifting`: `CategoryTheory.IsVersalAtField`,
  the new definition node below.
- `def-weil-size-convention` is a metatheoretic convention with no Lean declaration;
  it is represented by explicit universes.
- Proof imports include
  `Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout`, declaration
  `AlgebraicGeometry.isPushout_spec_pullbackCone_of_surjective`, and
  `Mathlib.RingTheory.HopkinsLevitzki`, for
  `instIsNoetherianRingOfIsArtinianRing` and
  `isArtinianRing_iff_isNilpotent_maximalIdeal`.
  `lem-sfb-artinian-finite-residue-restriction` has no recorded Lean or Mathlib
  match in the read repository, so there is no module to import for that proof
  dependency. It remains named in the proof plan, and is not needed for typing.

Edge cases checked before writing: L = κ(u); B = L; B' = B; purely inseparable
finite L/κ(u); the empty U (there is then no point u₀, so no spurious existence);
zero base R (a point over Spec R cannot exist); arbitrary/non-Artinian rings in
hRS, including zero rings; nilpotent thickenings of arbitrary length, handled
in the proof by square-zero iteration. No additional restriction is introduced
in any of these cases. Arbitrary prescribed isomorphisms, including nonidentity
automorphisms, are retained by the arrow equality.

Searches (all through the prescribed msearch wrapper, plus local source reads):

- LeanFinder: `Formal versality at a point of a category fibred in groupoids
  persists after finite residue field extension`: eight residue-field and
  formal-smoothness hits, none concerning general fibred-groupoid versality.
- LeanSearch: `Versality lifting condition for an object of a fibred groupoid
  at a field valued point`: eight hits about localization lifting, cartesian
  lifts and manifold groupoids; none defines the Artinian lifting predicate.
- Loogle: `Pseudofunctor, Groupoid, IsFiberedInGroupoids`: unknown identifier
  Pseudofunctor, zero hits. Follow-up `"versal"`: twelve Ore-localization
  universal-hom hits, none matches.
- Mathlib grep `Schlessinger|\bversal\b|IsFiberedInGroupoids`: three incidental
  comments in cotangent extensions and weak limits, no matching statement.
- Local rg in both `lean/WeilConjectures` and `lean/Sheaf` with
  `\b[Vv]ersal|\b[Vv]ersality|Schlessinger|FibredGroupoid|FiberedGroupoid`,
  followed by reading all pertinent declarations, found only versality of
  proper curve families, versality of complete formal objects, and
  deformation-test pseudofunctors. None defines versality at a field-valued
  point for an arbitrary CFG. The existing CFG and total-category interfaces
  are reused. Direct rg for the new names and the item id upstream gave no
  duplicate. The upstream name index has no matching names.
- DAG searches and `tools/blueprint_refs.py search 'pointwise versality'`
  found no definition node (zero blueprint hits); the broader `versal` search
  included unrelated substring hits and the already read formal-object nodes.
  `lem-sfb-artin-versal-field-lifting` is a different theorem with a global
  versality hypothesis and no recorded Lean; it is not reused as an exact match.
- The current latest blueprint unit and chapter were read; this auxiliary
  statement leaves their statements and proof route unchanged. Stacks artin.tex
  definition-versal and lemma-versal-change-of-field were read directly.

Validation: both modules compiled individually against the published server
library with scompile.py, including sibling-module resolution. There are no
errors or non-sorry warnings. The first elaboration exposed an underdetermined
`Over.homMk`; giving its source and target explicitly fixed it without changing
any statement. No global build or direct repository mutation was performed.

## New nodes

`def-sfb-pointwise-versal-lifting` defines `CategoryTheory.IsVersalAtField` in
`Sheaf.AlgebraicGeometry.PointwiseVersalLifting`. Its source is Stacks 07XF and
the smooth deformation-functor condition used in 07XG. It packages exactly the
item's lifting condition, for a specified field-valued point, so the theorem can
use the same notion for κ(u) and L. It uses the existing `BasedCategory`,
`Functor.Fiber`, `IsHomLift` and fibred-groupoid notion. Its definition has real
data (a quantified Prop), with no proof placeholders. Searches and their actual
results are recorded in its mathlib_searches; the existing proper-curve and
formal-ring versality predicates have different inputs and do not give this
notion. `blueprint_refs.py ancestor` returns null for this imported auxiliary
chain; the new node preserves that null ancestor and prefixes the item to its
existing via chain.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
