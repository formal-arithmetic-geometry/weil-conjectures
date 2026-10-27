## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.AbelianSubgroupEquivariantMultipleMap`
states `AlgebraicGeometry.exists_abelian_subgroup_equivariant_multiple_map`.
Its only proof is `sorry`; it defines no new notions and changes only the item's `lean`.
The source was read directly in `literature/milne-algebraic-groups_iAG2017.pdf`,
PDF pages 164–165 (printed 152–153): Proposition 8.23, Lemma 8.22 and its positive-degree
construction, with the extension assertion 8.18.

Clause-by-clause correspondence:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- k-schemes G and A: `(G A : Over (Spec (.of k)))`.
- Their group-scheme structures: `[GrpObj G] [GrpObj A]`.
- G smooth: `[Smooth G.hom]`.
- G connected, including nonemptiness: `[ConnectedSpace G.left]`.
- G separated, meaning its diagonal is a closed immersion: `[IsSeparated G.hom]`.
- G finite type: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- A an abelian variety, proper smooth and connected: `[IsAbelianVariety A]` together
  with `[GrpObj A]`. No extra commutativity hypothesis is imposed on A or G.
- i a closed subgroup inclusion: `(i : A ⟶ G) [IsClosedSubgroupScheme i]`.
  The recorded upstream class includes the homomorphism condition, injectivity on
  R-points, and closed immersion of the underlying map.
- Centrality on every commutative k-algebra: `hcentral` quantifies over
  `(R : Type u) [CommRing R] [Algebra k R]`, then the two points over
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))`, and asserts
  `Commute (a ≫ i) g`. This matches the node's affine-test centrality exactly.
- A positive integer: `∃ (n : ℕ), 0 < n ∧ ...`.
- A k-scheme morphism: `∃ (φ : G ⟶ A), ...`. There is no `IsMonHom φ` condition
  and no requirement on its value at the identity.
- The formula phi(g i(a)) = phi(g) + [n]a: the left side is
  `lift (fst G A) (snd G A ≫ i) ≫ μ[G] ≫ φ`, and the right side is
  `lift (fst G A ≫ φ) (snd G A ≫ (𝟙 A ^ n)) ≫ μ[A]`.
  These are equal morphisms `G ⊗ A ⟶ A` over Spec k. The cartesian monoidal
  structure on Over is constructed using the chosen scheme pullback:
  `Over.tensorObj_left`, `Over.fst_left`, `Over.snd_left`, `Over.lift_left` in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` identify this product and these
  maps with G ×_k A and its projections. Precomposition with any T-point gives
  precisely the test-scheme formula, including for nonreduced T; conversely take
  T = G ×_k A and its projections. Multiplicative notation here is the existing
  pointwise notation for group objects and represents the addition on A.
- No properness, affineness or commutativity of G is assumed. There is no
  restriction on the characteristic or requirement that n be invertible.

Dependency declarations read and used:

- `Field` (`Mathlib.Algebra.Field.Defs`), and `IsAlgClosed`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`, imported through the recorded
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` module).
- `CategoryTheory.GrpObj` (`Mathlib.CategoryTheory.Monoidal.Grp`), with its
  multiplication `CategoryTheory.MonObj.mul`, pointwise Hom group structure and
  `MonObj.comp_pow`; provided through the upstream group-scheme definitions.
- `AlgebraicGeometry.Smooth` (`Mathlib.AlgebraicGeometry.Morphisms.Smooth`).
- `ConnectedSpace` (`Mathlib.Topology.Connected.Basic`), whose explicit Nonempty
  field agrees with the dependency node's convention.
- `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`
  (`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`).
- `AlgebraicGeometry.IsSeparated` (`Mathlib.AlgebraicGeometry.Morphisms.Separated`),
  the separated part of the proper-morphism terminology node.
- `AlgebraicGeometry.IsSubgroupScheme` and `IsClosedSubgroupScheme`
  (`WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`): full class signatures and
  docstrings read; the latter extends the former and adds IsClosedImmersion.
- `AlgebraicGeometry.IsAbelianVariety`
  (`WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`): full class signature and
  docstring read; it extends IsProper, Smooth and ConnectedSpace without making
  the chosen group structure part of that predicate.
- `AlgebraicGeometry.torsionSubgroupScheme`
  (`WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`): its full definition and
  docstring explicitly identify multiplication by n as `𝟙 A ^ n`. We use that
  existing multiplication map directly; we do not create or assume a new map.
- `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.lift`
  (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`), used by Over's
  existing cartesian monoidal structure rather than a private fibre product.

Plain imports include the already stated proof dependencies: connectedness with a
section; homogeneous quotient; Yoneda full faithfulness; proper/smooth base change
(via the public imports); smooth fpqc descent; smooth source descent; regularity;
flat and surjective base change; commutative torsor positive weight; local spreading;
separated dense-image extensionality (via the public group-scheme import); smooth
composition (via the public abelian-variety import); geometric reducedness; and
geometrically irreducible products. The currently unstated proof nodes
`lem-trf-smooth-connected-fibre-normal-integrality` and
`lem-sfb-weil-extension-to-abelian-variety` have no recorded module to import and are
named in the proof docstring. They provide no data required to type this statement.
The eight-step proof docstring preserves the full node's route, including generic
fibre density and agreement on the entire generic fibre before extension of equality.

Edge cases checked before writing: the trivial abelian subgroup permits n = 1 and
the constant map; if G = A and i is the identity, n = 1 and phi the identity work
(and translations illustrate why identity preservation must not be added). The group
identity and ConnectedSpace exclude empty G and A as intended. Positive characteristic,
including n divisible by the characteristic, is allowed: no etaleness or invertibility
is demanded. There is no properness assumption on G, so the statement covers products
of an abelian variety with a nonproper smooth connected group. The scheme-morphism
equality retains nonreduced tests; it does not reduce to equality on k-points. The
single explicit universe u follows the existing group-scheme and algebra-test API.

Searches (2026-10-24):

- `msearch.py ... leanfinder` query: "A central abelian subgroup of a smooth connected
  algebraic group admits a scheme morphism equivariant for multiplication by a positive
  integer". Eight hits, all concerning abstract group transfer or special linear group
  centres. `MonoidHom.transferCenterPow` needs finite-index centre and is a map of abstract
  groups; none asserts the scheme result.
- `msearch.py ... loogle` query: `"GrpObj", "IsAbelianVariety"`: zero hits.
- `msearch.py ... grep` query: `Rosenlicht|equivariant.*[Aa]belian|[Aa]belian.*[Ss]ubvariety`,
  subdirectory `AlgebraicGeometry`: zero hits.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for the item id, Rosenlicht,
  abelian_subgroup/abelianSubgroup, and equivariant/positive-multiple retractions found
  no exact statement. `grep -rn` of the item id in `lean/WeilConjectures` found none.
- Read `Sheaf.AlgebraicGeometry.AbelianVariety.MultipleRetraction`, declaration
  `AlgebraicGeometry.IsAbelianVariety.exists_multiple_retraction`: its ambient group
  must itself be an abelian variety, and its conclusion is a homomorphism restricting
  to [n], so it is not this statement. The torsor positive-weight theorem is a proof
  ingredient rather than an exact match: its source is a torsor under the target.
- Full upstream subgroup and abelian-variety definitions were read, and the existing
  multiplication map was identified in the recorded multiplication node's module.

No statement correction, new node, unusable dependency interface, or mathematical
statement dispute was found.

## Second reading by Q68

A final worker self-check reread the node alongside the declaration: all the listed
hypotheses have their binders above, affine-test centrality has the exact quantifier,
positivity is explicit, and the conclusion is the two required maps on G ×_k A.
In particular no homomorphism structure or identity normalization was added to phi,
and neither G's properness nor its commutativity was introduced. No mismatch was found.
This is a self-check; the independent delivery review is performed by the maintainer,
as specified in the dispatch brief. No other agent was started.
