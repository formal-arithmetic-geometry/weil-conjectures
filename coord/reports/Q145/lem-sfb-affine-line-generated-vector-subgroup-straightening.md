## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.AffineLineGeneratedVectorSubgroupStraightening`
states `AlgebraicGeometry.affineLineGenerated_vectorSubgroup_straightening`, with the entire
proof `sorry`. Its docstring follows all seven steps of the accepted node proof. The only
helper, `affineLineVectorPower`, is an abbreviation for the existing categorical finite product
of `Grp.mk (StandardGroupSchemes.additive k)`; it introduces no new group law, choice or
independent notion. Its data are the actual product, not postponed data.

I opened Conrad's source https://math.stanford.edu/~conrad/papers/appbnew.pdf and read
Proposition 1.15 and its proof on printed p.9, together with the positive-characteristic
convention on p.3. The theorem is the coordinate-automorphism result stated there, with
axes reordered so that the nonzero coordinates come first. Its direct-factor assertion
is rendered by the explicit retraction conclusion. No correction of the DAG statement
or dependency interface is needed. No STATEMENT-DISPUTED flag.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A field k | `{k : Type u} [Field k]` |
| Characteristic p > 0, p prime | `(p : ℕ) [Fact p.Prime] [CharP k p]`; primality implies positivity |
| Affine group schemes of finite type | `L : Grp (Over (Spec (.of k)))`, `IsAffine L.X.left`, `LocallyOfFiniteType L.X.hom`, `QuasiCompact L.X.hom` |
| Additive group Ga(R) = (R,+), underlying affine line Spec k[x] | Reuse `StandardGroupSchemes.additive` and its recorded `additiveGroup`; its underlying object is `affine k (Polynomial k)` |
| E = Ga^N, N ≥ 0 | `N : ℕ`, ambient `affineLineVectorPower k N`, the product indexed by `Fin N` |
| L is a closed subgroup of E | `i : L ⟶ affineLineVectorPower k N` and `[IsClosedSubgroupScheme i.hom.hom]` |
| L is smooth | `[Smooth L.X.hom]` |
| Fix a separable closure K/k | `(K : Type u) [Field K] [Algebra k K] [IsSepClosure k K]` |
| Scalar extensions L_K, E_K and the inclusion | The actual `Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))`, lifted by `mapGrp` |
| Some set of K-scheme maps A1_K → L_K → E_K | `curves : Set (StandardGroupSchemes.additive K ⟶ ... L ... .X)` and composition with the scalar-extended i; these are scheme maps, not assumed group homomorphisms |
| Pointed means 0 maps to 0 | `hpointed`: precomposing each f with the constant identity-valued endomorphism `1` gives the constant identity-valued morphism `1` into L_K |
| L_K is the smallest closed subgroup containing the curves | `hgenerated`: for every group scheme J and closed subgroup inclusion j into E_K, if each composite curve factors through j, then the inclusion L_K → E_K factors through j |
| A k-group automorphism h of E | `h : affineLineVectorPower k N ≅ affineLineVectorPower k N`; isomorphism in `Grp (Over (Spec k))` |
| An integer 0 ≤ d ≤ N | `d : ℕ` and `d ≤ N` |
| h(L) = Ga^d × {0}^{N-d} as closed subgroup schemes | For every k-test scheme T and x : T → E, x factors through i followed by h exactly when every coordinate with `d ≤ j.val` equals the identity-valued morphism `1`; `Pi.π` is the actual product projection |
| In particular L ≅ Ga^d | `Nonempty (L ≅ affineLineVectorPower k d)` |
| A k-group homomorphism r : E → L restricting to identity | `∃ r : affineLineVectorPower k N ⟶ L, i ≫ r = 𝟙 L` |
| h need not be linear | The ambient isomorphism is in the group-scheme category, with no linearity predicate |

The finite product E is affine and finite type by its construction from the affine line;
there is no arbitrary ambient group or imposed coordinate identification. The factorization
map a in `hgenerated` need not separately be declared a group homomorphism: because j is a
closed subgroup monomorphism and the composite is the group homomorphism i_K, compatibility
with multiplication follows after composing with j. Thus this is exactly subgroup containment.
Quantification over all T, including nonreduced schemes, makes the conclusion equality of
closed subschemes, not only equality of rational-point sets. A set of maps suffices for any
set-indexed generating family: repeated indices have no effect on factorization.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (read full class/docstring).
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `Grp`, `Grp.ofHom`,
  `Mathlib.CategoryTheory.Monoidal.Grp`, and the recorded terminology documentation in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. The statement uses bundled `Grp`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (finite type is their conjunction).
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`; its full signature and docstring
  identify the morphism as a closed immersion and group monomorphism.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-connected-scheme`: `ConnectedSpace`,
  `Mathlib.Topology.Connected.Basic`. Read the definition; this node's statement does not
  assume connectedness, so no such binder was added. That source is already imported
  transitively through the scheme library.
- `def-sc-gm-ga`: `StandardGroupSchemes.additive`, `additiveGroup`, with their explicit
  polynomial algebra and coordinate-law definitions, in
  `Sheaf.AlgebraicGeometry.StandardGroupSchemes`. No second additive group is defined.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`.
- The additional standard interface `IsSepClosure` is read from
  `Mathlib.FieldTheory.IsSepClosed`; it asserts separable closedness and separability.
- Categorical powers and projections reuse the existing `HasLimitsOfShape` instance
  of `Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits`, `Limits.Pi.π`, and `Grp.forget`.

Proof-only imports follow the accepted plan: `IsClosedImmersion` through the group-scheme
module; `MvPolynomial.ringKrullDim_of_isNoetherianRing` in
`Mathlib.RingTheory.KrullDimension.Polynomial`; the recorded first affine dimension-drop
component `PrimeSpectrum.isDomain_of_irreducibleSpace` in
`WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology`;
`algebraicGroup_homomorphism_factorization` in
`Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization`;
the two recorded affine-separated instances in
`Mathlib.AlgebraicGeometry.Morphisms.Separated`;
`affine_normal_quotient_geometry` in
`Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`;
`Scheme.Hom.finiteType_fibre_image_dimension_bounds` in
`Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds`.
The hypersurface-additive-equation and separable-axis-extraction proof dependencies have
no Lean records yet; their mathematical steps remain in the docstring, with no invented imports.

Edge cases checked before drafting:

- N = 0: the empty categorical product is the trivial group; d must be 0, and the
  empty coordinate condition says every T-point belongs to the image, as required.
- d = 0: every coordinate is zero; the image is the trivial closed subgroup.
- d = N: the coordinate condition is empty; the image is all of E.
- Empty generating family: generation forces L_K into the identity subgroup, so L is
  trivial by faithful base change. No `Nonempty curves` hypothesis is present.
- Disconnected smooth subgroups of Ga (for example the constant F_p subgroup) cannot
  satisfy generation by pointed curves; the hypothesis does not silently assert connectedness.
- Infinitesimal kernels such as alpha_p are excluded by smoothness. The conclusion tests
  every scheme, so nonreduced test rings are retained.
- Imperfect fields are allowed, and coordinate graphs such as (t,t^p) require the nonlinear
  group automorphisms which our bundled isomorphism permits.
- The scheme and field universes are explicitly u, with K in the same universe as k:
  separable algebraic closures exist there, and the test category includes the groups
  themselves, so the factorization and equality tests are not vacuous.

Searches for an existing statement (all run with the prescribed msearch.py wrapper;
raw output is retained in sandbox searches.jsonl):

- LeanFinder: "A smooth closed subgroup of a vector group generated by pointed affine
  line maps over a separable closure is carried to a coordinate subgroup by a group
  scheme automorphism". Eight hits, starting with `InfiniteGalois.fixingSubgroup_isClosed`:
  Galois-theory results, no group-scheme straightening theorem.
- Loogle: `"Grp", "AffineSpace"`. Zero hits.
- Mathlib grep: `vector.group|affine.line.generated|straightening`, subdirectory
  `AlgebraicGeometry`. Zero hits.
- LeanSearch: "A smooth subgroup scheme of a power of the additive group generated by
  maps from the affine line is a coordinate direct factor after a group scheme automorphism".
  Eight hits: manifold smoothness, general scheme smoothness, additive subgroup actions
  and abstract `AddAut`; none states the algebraic-group theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `vectorGroup|vector_group|affineLineGenerated|straightening|pointed.*[Cc]urve` found
  unrelated Lie-algebra straightening and pointed-curve geometry. The narrower product
  search found `charZero_commutative_unipotent_vectorGroup`, which has characteristic zero
  and no coordinate-subgroup conclusion; it confirms the existing product encoding only.
- The requested item-id grep in `lean/WeilConjectures` returned no match; exact proposed
  declaration-name searches in both source trees and `dag/lean_names_upstream.json`
  returned no clashes.

Validation: scompile.py compiled this file both under its sandbox module name (6.7 s)
and its final library module name (4.9 s), without errors or warnings. The first draft's
scalar-extended group instance lookup was repaired by using the existing bundled
`mapGrp` interface, rather than imposing new hypotheses or changing group data.

## Second reading by Q145

I reread the node and final signature in a separate pass. This is the dispatcher's single
worker, not a claim of an independent agent review; the maintainer performs the independent
review of this delivery. I checked in particular that curves are ordinary scheme morphisms,
that their origin condition uses constant identity-valued maps rather than the categorical
identity, and that minimality compares against every closed subgroup of E_K. The coordinate
condition uses all test schemes and zero in each remaining coordinate, so it retains the
scheme-theoretic assertion and d = 0/N cases. The isomorphism and retraction are both
explicit clauses and are group-scheme maps. There is no perfectness, connectedness or
linearity binder. No mathematical mismatch was found in this rereading; the only change
after the first compile was the bundled scalar-change expression recorded above.
