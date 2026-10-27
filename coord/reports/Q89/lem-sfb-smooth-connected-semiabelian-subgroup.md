## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothConnectedSemiabelianSubgroup` states
`AlgebraicGeometry.smooth_connected_semiabelian_subgroup`. Its sole proof is `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The copied node changes only its `lean` record.

Source read: Conrad, *Semistable Reduction for Abelian Varieties*, author PDF
https://math.stanford.edu/~conrad/DarmonCM/2011Notes/SemistableReduction.pdf,
printed p.8, Corollary 3.2 and its subgroup application in Corollary 3.3.
The application is precisely the smooth connected subgroup assertion in this node.
The docstring carries all five steps of the accepted DAG proof, including the
closed-immersion pullback argument and the final transport of the kernel square.

Hypotheses and conclusion, clause by clause:

- Algebraically closed ground field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- The given group scheme over k: `G : Grp (Over (Spec (.of k)))`. This bundles
  the structure map and the original group law, with no replacement group structure.
- Commutativity: `[IsCommMonObj G.X]`.
- Smoothness and separatedness of G/k: `[Smooth G.X.hom] [IsSeparated G.X.hom]`.
- Finite type of G/k: `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`,
  the conjunction specified by def-weil-finite-type-morphism.
- Semiabelian geometric fibres: `hG : HasSemiabelianGeometricFibres G`.
- Closed subgroup: `B : Grp (Over (Spec (.of k)))`, `j : B ⟶ G`, and
  `[IsClosedSubgroupScheme j.hom.hom]`. A morphism in `Grp` is a homomorphism;
  the recorded closed-subgroup predicate includes the closed immersion and subgroup
  condition on algebra-valued points.
- Smoothness and connectedness of B: `[Smooth B.X.hom] [ConnectedSpace B.X.left]`.
  No additional separatedness, finite-type or commutativity hypothesis on B is imposed.
- Nonnegative integral rank: existential `r : ℕ`, allowing zero.
- Abelian variety A/k: existential `A : Grp (Over (Spec (.of k)))` and
  `IsAbelianVariety A.X`, which means proper, smooth and connected with the bundled
  group structure supplied by A.
- Homomorphisms from the split torus to B and from B to A: existential
  `i : MultiplicativeType.splitTorus k r ⟶ B` and `q : B ⟶ A`.
- Identification with the entire scheme-theoretic kernel: the `IsPullback` square
  with top arrow `i.hom.hom`, left arrow `toUnit (MultiplicativeType.splitTorus k r).X`,
  bottom arrow `η[A.X]`, and right arrow `q.hom.hom`. This is a square in the
  category of k-schemes, so its universal property gives the actual kernel,
  rather than an equality of geometric points or an arbitrary subkernel.
- Local surjectivity in the big fppf topology:
  `Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
  (yoneda.map q.hom.hom)`. These are exactly the two shared exactness clauses of
  def-sfb-semiabelian-geometric-fibres; exactness as fppf sheaves is their consequence.

Dependency declarations read and reused:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed` (the recorded algebraic-closure
  node explicitly identifies this as its algebraically closed field notion).
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and its category.
- Mathlib.CategoryTheory.Monoidal.Grp / Mon: `CategoryTheory.GrpObj`, `Grp`,
  `IsCommMonObj`; these give group schemes over the base via `Over`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType / QuasiCompact:
  `LocallyOfFiniteType`, `QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.Separated: `IsSeparated`.
- Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres:
  `AlgebraicGeometry.HasSemiabelianGeometricFibres`; its full definition is also
  the model for the conclusion's kernel and fppf clauses.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `AlgebraicGeometry.IsClosedSubgroupScheme` (and its parent `IsSubgroupScheme`).
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`, including nonemptiness.
- WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs: `IsAbelianVariety`.
- Sheaf.AlgebraicGeometry.ToriMultiplicativeType: `MultiplicativeType.splitTorus`.
- Mathlib.AlgebraicGeometry.Sites.Fpqc: `Scheme.fppfTopology`;
  Mathlib.CategoryTheory.Sites.Over: `GrothendieckTopology.over`;
  Mathlib.CategoryTheory.Sites.LocallySurjective: `Presheaf.IsLocallySurjective`.

Proof imports include the recorded Mathlib permanence, finite-type composition,
closed-immersion composition/base-change interfaces and the landed
`Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus` statement.
`lem-sfb-barsotti-chevalley-decomposition` and
`lem-sfb-affine-to-abelian-hom-vanishing` are proof-only dependencies with no recorded
Lean declaration or Mathlib match in the read clone; no module is imported for those
unstated nodes. Neither is needed to type this statement, and both remain explicitly
named in the theorem's proof docstring. There is no import cycle.

Edge cases checked before writing: rank zero uses the existing splitTorus recursion's
unit object; B = 1 allows r = 0 and A = 1. A torus subgroup allows the trivial abelian
quotient, and an abelian subgroup allows rank zero. The empty scheme is excluded by
ConnectedSpace and by the identity section, as in the source. No characteristic
restriction or positive dimension/rank is imposed. All schemes and the field live
in the shared universe u used by the dependency interfaces; the statement is universe
polymorphic. The local-surjectivity predicate ranges over the actual big slice site.

Searches for an existing statement (2026-10-24):

- msearch.py / leanfinder: `A smooth connected closed subgroup of a semiabelian variety
  is an extension of an abelian variety by a split torus`: 8 hits, concerning
  TopologicalAbelianization, Lie groups, and UnitAddTorus; no algebraic-group match.
- msearch.py / loogle: `"semiabelian"`: 0 hits.
- msearch.py / grep: `semi.?abelian|smooth.*connected.*closed.*subgroup`,
  subdirectory AlgebraicGeometry: 0 hits.
- rg in lean/WeilConjectures and lean/Sheaf for `semiabelian|Semiabelian` and the
  exact node id: upstream has no match; Sheaf has the geometric-fibre definition,
  split-quotient, torsion-density, extension and other related statements, but no
  smooth connected closed subgroup result.
- Exact node id and proposed declaration name searched in dag/lean_names_upstream.json
  and lean/WeilConjectures: no match.

No disputed statement or node fault was found. Every binder and universe is explicit;
`set_option autoImplicit false` enforces this. Validation uses scompile.py only.

## Second reading by Q89

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
