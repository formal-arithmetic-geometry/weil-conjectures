## Worker report

The single module `Sheaf.AlgebraicGeometry.GroupScheme.GeneralCentreZeroDimensionAffine`
states `AlgebraicGeometry.exists_centre_reducedIdentityComponent_dim_and_isAffine`.
Its only theorem has proof `sorry`; there are no new definitions, axioms, instances,
or helper theorems. The mathematical node statement is unchanged.

Hypothesis and clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The general k-group scheme is `G : Grp (Over (Spec (.of k)))`. This is the
  bundled version of the dependency's `GrpObj`; `G.X` has that structure.
- Smooth, connected, separated, and finite type are respectively
  `[Smooth G.X.hom]`, `[ConnectedSpace G.X.left]`, `[IsSeparated G.X.hom]`,
  and `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- The representing group scheme and inclusion are the existential `Z` and `i`.
  `IsClosedSubgroupScheme i.hom.hom` gives the closed immersion, homomorphism,
  and injectivity on algebra-valued points. `IsNormalSubgroupScheme i.hom.hom`
  gives normality, and `IsCommMonObj Z.X` gives commutativity.
- For every commutative k-algebra B, `centralizerPoints (𝟙 G) B` equals the
  range of the inclusion on B-points. Unfolding the existing definition says:
  for every commutative k-algebra B' and every k-algebra map B → B', the
  extended point commutes with every point of G(B'). This is exactly every
  B-algebra extension with its compatible k-algebra structure; it imposes
  no reducedness or nontriviality condition on B or B'. Range equality plus
  injectivity is representability of this subfunctor by the specified inclusion.
  Naturality comes from composition with the scheme morphism i.
- `Z0 : Z.X.left.Opens` and its set equality with
  `connectedComponent (GrpObj.onePoint Z.X)` specify the identity component
  with the open subscheme structure. In particular no reduced or alternative
  scheme structure is chosen for Z0. Existence of this open is part of the
  conclusion, not an added hypothesis about Z.
- A is the explicit Mathlib reduction `Z0.toScheme.nilradical.subscheme`.
  The node introduces A by this formula, so no separate existential A or
  choice is necessary. Its nilradical quotient and closed immersion are the
  dependency's existing constructions.
- The dimension equality is
  `topologicalKrullDim Z0.toScheme.nilradical.subscheme = topologicalKrullDim Z.X.left`.
- The final implication is `topologicalKrullDim Z.X.left = 0 → IsAffine G.X.left`.
- There is no affine or commutative hypothesis on G and no smoothness,
  connectedness, or reducedness hypothesis on Z.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `CategoryTheory.IsCommMonObj`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, `AlgebraicGeometry.IsNormalSubgroupScheme`,
  and their shared `IsSubgroupScheme` interface. This supplies all the recorded
  subgroup terminology without replacing it.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`:
  `AlgebraicGeometry.GrpObj.onePoint`; its existing identity-component declarations
  were also read. Those declarations require finite-type instances on Z before
  they can be applied. Instead of inserting instance-valued hypotheses or extra
  conclusions, the statement specifies the same open component directly by an
  existential open and equality of its underlying set.
- `Mathlib.Algebra.Field.Defs`: `Field`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and morphisms;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: the open subscheme interface;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.nilradical`;
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`:
  `Scheme.IdealSheafData.subscheme` and its canonical `subschemeι`.
- The already landed definition node
  `def-sfb-reductive-torus-centralizer-terminology` is added to `stmt_deps`:
  its module `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`
  defines the general `AlgebraicGeometry.ReductiveTorusCentralizer.centralizerPoints`.
  Despite the namespace, this definition requires neither reductivity nor a torus
  nor affineness. It applies to any group-scheme homomorphism. The source and full
  definition were read; specializing it to `𝟙 G` is the centre functor.
  Its existing `StandardGroupSchemes.affine` and `map` are Spec of an algebra and
  the contravariant Spec map of an algebra homomorphism. These definitions were
  read in `Sheaf.AlgebraicGeometry.StandardGroupSchemes` and reused, not copied.

The six published proof modules are imported privately: component translations,
reduction universal homeomorphism, dimension comparison, dimension-zero affineness,
group-homomorphism factorization, and linear group schemes. The finite-jet action
and exact-property-permanence nodes have no recorded Lean declaration in this
checkout, so no import for them is invented. Their precise uses are retained in
the four-step theorem docstring. They are proof prerequisites, not missing notions
needed to type this statement.

Sources: read Milne Proposition 1.92 and the centre definition on printed pp.33--34,
including the test on all algebra extensions, and the zero-dimensional-centre
case of Theorem 8.26 on printed p.154. The source explicitly warns on printed p.35
that SL_p can have nonreduced centre mu_p. The statement keeps that possibility.

Edge cases checked mathematically before writing: the trivial group has centre
itself of dimension zero and is affine; an elliptic curve is commutative and
equals its centre, so its positive-dimensional centre does not trigger the last
implication; SL_p in characteristic p has centre mu_p, whose reduction of its
identity component and full centre both have dimension zero. The theorem does
not require characteristic zero. The identity section prevents an empty group.
Zero test algebras are included: their points and all maps remain meaningful.
Arbitrary nonreduced test algebras are included throughout. Test rings live in the
same universe u as k and the schemes, not an independent smaller universe.

Searches for an existing statement or notion:

- `msearch.py` LeanFinder, query "The centre of a smooth connected algebraic group
  is a closed normal subgroup scheme and zero dimensional centre implies affine":
  eight abstract-group/Lie-algebra hits; no scheme-theoretic theorem.
- `msearch.py` Loogle, query `"GrpObj", "IsAffine"`: only the Hopf algebra
  instance for a group scheme already assumed affine; no matching theorem.
- `msearch.py` grep, `center|centre|centralizer`, Mathlib `AlgebraicGeometry/Group`:
  zero hits.
- `msearch.py` LeanSearch, query "A smooth connected algebraic group with zero
  dimensional scheme theoretic centre is affine": eight hits on general affine
  schemes, discrete schemes, and finite morphisms; none states this result.
- `rg` in `lean/WeilConjectures` for the item id and centre/affineness combinations
  found no attachment. GroupScheme general-linear results describe reduced centres
  of already affine matrix groups, which cannot replace this statement.
- `rg` in `lean/Sheaf` for centralizer definitions found the general
  `centralizerPoints` above. Its recorded DAG node and full module were read.
  It is reused through its landed node, so no new definition node is needed.
- Checked the proposed theorem name against Mathlib, WeilConjectures, and Sheaf:
  no collision. Inspected `dag/lean_names_upstream.json` for centre names.
- Checked the complete transitive statement/proof dependency reach of the added
  centralizer definition node (129 nodes): it does not reach this item, so the
  new dependency does not close a cycle.

Validation: the single delivered module compiles through the prescribed server
`scompile.py` wrapper, in module mode, with no errors or non-sorry warnings.
The explicit `set_option autoImplicit false` checks that every variable is bound.

No statement correction, disputed statement, dependency module, or new node.
The independent reading is performed by the maintainer after direct delivery,
as required by this worker's brief; no other agent was started.

## Second reading by Q66

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
