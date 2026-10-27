## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RankOneFlagCurve` states
`AlgebraicGeometry.rankOne_flag_quotient_dimension`, with its proof `sorry`.
There are no new definitions, no dependency repairs and no statement correction.
Source read: Milne, Algebraic Groups (2017), Theorem 20.16, printed pp.412--413,
including the algebraically closed base convention immediately preceding it;
Corollary 20.12, printed p.411. The node is the reductive specialization of
(a) implies (c). The declaration docstring carries all four accepted proof steps.

Clause-by-clause rendering:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]` |
| F-group schemes G, T, B and their group homomorphisms | `Grp (Over (Spec (.of F)))` and morphisms in this category |
| G reductive, affine, finite type, smooth and geometrically connected | `hG : ReductiveTorusCentralizer.IsReductive G`; its first component is the previously defined `SolvableGroupStructure.IsAlgebraic G` |
| T is a maximal closed torus subgroup of G | `iT` and `hT : ReductiveTorusCentralizer.IsMaximalTorus iT` |
| R(G) is the largest smooth connected solvable normal closed subgroup, using scheme-theoretic derived series | `hRank : RankOneRoots.HasSemisimpleRankOne G`; its existential witness R and inclusion r have precisely these properties, with maximality expressed by factorization of every other such inclusion |
| The represented fppf quotient G/R(G) is affine of finite type | The witness Q inside `HasSemisimpleRankOne`, `IsAlgebraic Q`, and `SolvableGroupStructure.IsFppfQuotient r.hom.hom q` |
| Every maximal torus of G/R(G) has dimension one | The final universal clause of `HasSemisimpleRankOne`, using the same `IsMaximalTorus` and `topologicalKrullDim` |
| Any Borel B containing T | `iB`, `hB : IsBorelGroupScheme iB.hom.hom`, `t : T ⟶ B`, `ht : t ≫ iB = iT` |
| B is closed, smooth, connected and solvable | The components of the recorded `IsBorelGroupScheme` definition; solvability uses `IsSolvableGroupScheme`, defined by scheme-theoretic derived length |
| All groups are affine of finite type | G is so by hG, T is a torus, and B is a closed subgroup of affine finite-type G. Closed immersions give the inherited affine and finite-type conditions; none is replaced by a rational-points condition |
| Q represents the fppf sheaf quotient of right cosets G/B | `Q`, `q`, `hQ`, `ηq`, `hηq` and `hUniversal`, copied from the quotient presentation in `exists_homogeneous_fppf_quotient` and `exists_orbit_stabilizer_quotient_iso` |
| Krull dimension of that quotient equals one | `topologicalKrullDim Q.left = 1` |
| No characteristic restriction | No characteristic, invertibility, or characteristic-zero binder |

The coequalizer has the two arrows from G times B given by projection and right
multiplication `(g,b) ↦ g iB(b)`. Thus it is the right-coset presheaf. `hQ` says
the represented presheaf is an fppf sheaf. `hηq` identifies the map from G with
the quotient map, and `hUniversal` is its sheafification universal property.
No additional torsor or flatness hypothesis is imposed on the nonnormal quotient.
The homogeneous-quotient dependency already guarantees existence. Quantifying over
any presentation says precisely that the scheme G/B has dimension one and avoids
choosing a representative from a sorried existence theorem.

The item gains the already landed definition node
`def-sfb-rank-one-root-interfaces` in stmt_deps, as permitted for landed notions.
Its recorded `HasSemisimpleRankOne` was read in full. Its radical is specified
by a largest-subgroup property, not selected as definition data. Its quotient
predicate is flat, surjective, locally of finite presentation with the specified
scheme-theoretic kernel. This is the represented fppf quotient, equivalently the
explicit sheafification presentation in `IsFppfGroupQuotient` of the normal-quotient
dependency. The predicate also records existence of a maximal torus in that
quotient; this is automatic for affine algebraic groups over an algebraically
closed field and prevents a vacuous rank condition. It does not restrict the
node's mathematical cases. No private replacement definition is introduced.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the relevant component
  of the algebraic-closure node).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsReductive`, `.IsMaximalTorus`.
- `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`:
  `RankOneRoots.HasSemisimpleRankOne`; its underlying notions are
  `SolvableGroupStructure.IsAlgebraic`, `.IsFppfQuotient` in
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure`, and
  `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`, `IsDerivedGroupScheme`
  in `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`.
- `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`:
  `IsFppfGroupQuotient`, `affine_normal_quotient_geometry`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Borel`: `IsBorelGroupScheme`.
- `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry`:
  `exists_homogeneous_fppf_quotient`, `exists_orbit_stabilizer_quotient_iso`.

The stated proof dependencies are imported privately:
`GeneralBorelFlagVariety.exists_general_borel_flag_variety` (in namespace
`AlgebraicGeometry`), `SmoothGroupOrbitGeometry.exists_smooth_group_orbit_geometry`
(likewise), `Mathlib.AlgebraicGeometry.AlgClosed.Basic` for `residueFieldIsoBase`,
`Mathlib.AlgebraicGeometry.Artinian` and `.Noetherian` for the dimension-zero step,
and `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced` for
`Smooth.geometricallyReduced`. The Jacobson lemma is
`LocallyOfFiniteType.jacobsonSpace` in the already publicly imported finite-type
module. The opposite-Borel intersection and proper homogeneous torus fixed-bound
nodes have no recorded Lean module at the time of writing, so their future imports
are left for the maintainer's dependency-import update. They are not extra
hypotheses or missing notions in this statement.

Edge cases checked before writing:

- A torus, a trivial group, and any semisimple-rank-zero reductive group fail
  the rank-one hypothesis: its radical quotient has a zero-dimensional maximal
  torus, including the trivial torus. There is no empty-index vacuity.
- For SL2, PGL2, and GL2, the quotient by a Borel is the projective line; the
  radical quotient has rank one, even though the original maximal torus of GL2
  has dimension two. The statement does not accidentally require dim(T) = 1.
- Products with central tori remain included, since the rank condition is on
  G/R(G), not G itself.
- Characteristic two and all positive characteristics remain included.
- An empty candidate Q cannot represent this quotient: sheafification preserves
  the image of the identity point of G. Zero-dimensional nonempty quotients are
  excluded by the proof's two distinct fixed points, not by an added assumption.
- Nonreduced test algebras remain among all objects of the fppf site; all subgroup,
  derived-series and quotient conditions retain scheme structure.
- Field, schemes and test site use the same explicit universe u, as in the
  recorded dependencies; no smaller independent test universe is introduced.

Searches performed (no exact existing statement):

- `msearch.py ... leanfinder "The Borel quotient of a reductive algebraic group of
  semisimple rank one has Krull dimension one"`: eight hits about ring dimension,
  including `ringKrullDim_eq_zero_of_field`; none about algebraic-group quotients.
- `msearch.py ... loogle '"Borel"'`: twelve hits concerning Lie-algebra Borel
  submodules and measurable Borel spaces; no group-scheme flag theorem.
- `msearch.py ... grep 'BorelSubgroup|semisimpleRank|rank_one_flag|flagVariety'
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "The Borel quotient of a reductive group of semisimple
  rank one is one dimensional"`: eight measurable-space quotient hits; no match.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and
  `dag/lean_names_upstream.json` for `rankOne_flag`, `rank_one_flag`,
  `flag_quotient_dimension`, `rankOneFlagCurve`: no existing declaration.
- Project `rg` for `Radical|radical|IsSolvable|IsMaximalTorus|rank_one|rankOne`
  found the reusable `RankOneRootInterfaces.HasSemisimpleRankOne` definition.
- Project search for the exact blueprint id found no earlier declaration.
  DAG search for `RankOneRootInterfaces` identified its existing owning node.

Validation: `scompile.py Q04 lem-sfb-rank-one-flag-curve` compiled this file both
as a sandbox module and as `Sheaf.AlgebraicGeometry.GroupScheme.RankOneFlagCurve`
with no errors or warnings. Every variable and universe is explicitly bound;
`autoImplicit` and `relaxedAutoImplicit` are both false. Only the named theorem
has `sorry`. No mathematical dispute or node fault was found.

## Second reading by Q04

A separate clause-checking pass by this worker reopened the node and final file;
no second agent was started, in accordance with the dispatcher brief. The
maintainer's delivery review supplies the independent reading.

Checked the algebraically closed field binders; the actual group schemes and
inclusions; reductivity; maximality of T; the radical's largest-subgroup and
scheme-theoretic solvability clauses inside `HasSemisimpleRankOne`; the rank
condition on the quotient rather than on T; the Borel predicate and explicit
factorization witnessing containment; the right, rather than left, multiplication
in the coset coequalizer; the actual fppf sheafification universal property and
its compatibility with q; and the conclusion on Q.left rather than on rational
points. Compared the coequalizer and universal-property binders directly with
`exists_orbit_stabilizer_quotient_iso`. Checked that no arbitrary quotient map,
normality of B, perfectness assumption, characteristic restriction or rational-point
solvability was substituted. The newly cited node is already landed, and no
new notion or repair is hidden in the module. No mismatch was found and no
statement change was necessary.
