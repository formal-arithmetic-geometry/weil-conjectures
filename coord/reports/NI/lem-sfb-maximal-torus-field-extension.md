## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.MaximalTorusFieldExtension` states
`AlgebraicGeometry.maximal_torus_iff_baseChange`, with its proof postponed by `sorry`.
It states both directions of Milne, Algebraic Groups (2017), Theorem 17.82,
printed p.379, for the smooth connected affine finite-type case of the node.
I read that theorem and its centralizer/quotient proof in the local PDF. The
node's statement is unchanged. Its six proof steps are reproduced in the theorem
docstring. No definitions or additional theorems are introduced.

The hypotheses and clauses match as follows:

- The ground field is `{k : Type u} [Field k]`.
- The group schemes T and G are `(T G : Grp (Over (Spec (.of k))))`, and the
  group-scheme homomorphism identifying the subgroup is `(i : T ⟶ G)`.
- Smoothness is `[Smooth G.X.hom]`; connectedness is
  `[ConnectedSpace G.X.left]`, including nonemptiness as in the dependency.
- Affineness is `[IsAffine G.X.left]`. Finite type is the recorded pair
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- The closed subgroup hypothesis is `[IsClosedSubgroupScheme i.hom.hom]`.
- The torus hypothesis is `(hT : MultiplicativeType.IsTorus T)`. This existing
  predicate says that after algebraic closure the group is isomorphic to
  `splitTorus` of some natural-number rank. That construction uses the recorded
  multiplicative group, with the trivial group as its rank-zero case.
- The arbitrary extension is `(L : Type u) [Field L] [Algebra k L]`; the map is
  `algebraMap k L`. No algebraicity, finiteness or separability is required.
- Maximality over k is `ReductiveTorusCentralizer.IsMaximalTorus i`. Its actual
  body requires a closed torus and says that every factorization through a
  closed torus subgroup is an isomorphism; this means no strictly larger torus.
- Scalar extension of the inclusion is
  `((MultiplicativeType.baseChange (K := L)).map i)`. The actual definition is
  `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).mapGrp`, so its
  objects are the chosen fibre products, with their pulled-back group laws.
- The conclusion is the biconditional between maximality of the original
  inclusion and maximality of this scalar-extended inclusion.
- There are no reductivity, splitting, perfectness or characteristic binders.

Dependency declarations used, whose source definitions and docstrings were read:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and its bundled
  `CategoryTheory.Grp`, specialized to the category of schemes over Spec k.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, with its group-homomorphism,
  pointwise-injectivity and closed-immersion components.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `AlgebraicGeometry.StandardGroupSchemes.multiplicative` and its group structure,
  reached through the torus module rather than redefined.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.IsTorus`, `.splitTorus`, `.baseChange`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`; the recorded base-change functor uses this
  chosen fibre product and transports the group law with `mapGrp`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsMaximalTorus`. Its existing node
  `def-sfb-reductive-torus-centralizer-terminology` is added to `stmt_deps` under
  the rule permitting landed definition dependencies. It supplies exactly the
  maximality notion described inline in the original statement.

The stated proof dependencies are imported privately:
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`
(`GeometricallyConnected.of_connectedSpace_of_section`),
`Mathlib.AlgebraicGeometry.Morphisms.Proper` (the recorded base-change interface),
`WeilConjectures.Mathlib.AlgebraicGeometry.Scheme`
(`Scheme.connectedSpace_iff_isIdempotentElem`), and
`Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`
(`affine_normal_quotient_geometry`). Statement dependencies that also occur in
`proof_deps` are already public imports. The other proof nodes have no Lean
record in the current DAG, so there is no recorded module to import for them;
they are all named in the proof docstring. They are not needed to type this
stage-2 statement.

Edge cases checked before writing: rank zero is included by `splitTorus k 0`;
for G trivial its torus is maximal on both sides; for G = G_m the trivial torus
is nonmaximal on both sides; for G = G_a the trivial torus is maximal, including
positive characteristic. Taking T = G for a torus gives maximality on both
sides. L = k is allowed, as are algebraic closures, transcendental extensions,
finite fields and imperfect fields. The empty scheme is excluded already by
the group identity and the stated connectedness convention. The common
universe is the existing scheme/base-change size convention: u is arbitrary,
so fields of different original sizes can be placed in a common universe;
there is no smaller-universe quantifier over test algebras. No geometric
maximality or reductivity is silently built into `IsMaximalTorus`.

Searches performed for an existing statement:

- `msearch.py` LeanFinder, query “A maximal torus of a smooth connected affine
  group remains maximal after any extension of the ground field”: eight hits
  about maximal ideals and Cartan subalgebras, no algebraic-group statement.
- `msearch.py` Loogle, query `"IsMaximalTorus", "baseChange"`: zero hits.
- `msearch.py` grep, query `maximal.?torus|IsTorus|IsMaximalTorus` in
  `AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py` LeanSearch, query “Maximality of a torus in a smooth connected
  affine algebraic group is preserved and reflected by field extension”: eight
  unrelated hits concerning maximal ideals, scalar extension and field theory.
- `rg` in `lean/WeilConjectures` by node id and by maximal-torus/base-change
  keywords: no matching declaration. Searches in `lean/Sheaf` found the existing
  maximality definition and uses, including the characteristic-sequence
  consumer, but no theorem establishing the field-extension biconditional.
- `rg` for the proposed theorem name in Mathlib, both project roots and
  `dag/lean_names_upstream.json`: no existing declaration of that name.

Validation: `scompile.py` compiled the module in sandbox and library modes,
with no errors or non-sorry warnings. `set_option autoImplicit false` ensures
that every variable and universe is explicitly bound. No statement dispute or
source correction was needed. The requested CompactObject example is currently
a withdrawn module with no declarations; the delivered file follows the
current mandatory module/public-import/expose conventions instead.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
