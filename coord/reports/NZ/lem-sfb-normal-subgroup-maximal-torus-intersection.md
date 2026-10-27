## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.NormalSubgroupMaximalTorusIntersection`
states `AlgebraicGeometry.normalSubgroup_maximalTorus_intersection`. Its only theorem
has proof `by sorry`. No definitions, additional nodes, dependency repairs, or statement
corrections were needed. The item node changes only in `lean`.

Source checked directly: Milne, Algebraic Groups (2017), Corollary 17.85, printed
pp.379--380 (PDF pp.391--392), Remark 12.5, p.232 (PDF p.244), and Notation 12.29,
p.241 (PDF p.253). Corollary 17.85 proves maximality of the largest subtorus of the
intersection. The two Chapter 12 passages identify this subtorus with the reduced
identity component. The module docstring contains all seven proof steps of the node.

Hypotheses and clauses:

- The algebraically closed field is `(F : Type u) [Field F] [IsAlgClosed F]`.
- The three F-group schemes are `G M T : Grp (Over (Spec (.of F)))`, using the
  recorded group-object notion; all displayed arrows between them are group morphisms.
- G is affine through `[IsAffine G.X.left]`, smooth through `[Smooth G.X.hom]`, and
  connected through `[ConnectedSpace G.X.left]`.
- Finite type of G is the recorded conjunction of
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- M is smooth and connected through `[Smooth M.X.hom] [ConnectedSpace M.X.left]`.
  Its specified inclusion is `iM : M ⟶ G`, with
  `[IsClosedSubgroupScheme iM.hom.hom] [IsNormalSubgroupScheme iM.hom.hom]`.
  No separate affine or finite-type hypotheses on M are imposed: these follow from
  its closed inclusion in the affine finite-type G.
- The prescribed torus inclusion is `iT : T ⟶ G`, with
  `hT : ReductiveTorusCentralizer.IsMaximalTorus iT`. The definition requires a
  closed torus inclusion and expresses maximality by every containing torus
  factorization being an isomorphism. Its `MultiplicativeType.IsTorus` uses the
  existing finite products of the recorded multiplicative group.
- D is the scheme-theoretic intersection: existential `D`, `pM`, `pT` satisfy
  `IsPullback pM.hom.hom pT.hom.hom iM.hom.hom iT.hom.hom` in F-schemes.
  This is the universal property of the dependency's `pullback`, not an
  intersection of F-points. Forgetting to schemes also gives the scheme pullback.
  Its projections are group morphisms, specifying the induced intersection law.
  Existentially presenting the pullback avoids selecting a new group law on a
  globally chosen pullback object. Pullback uniqueness identifies it with that
  object, compatibly with both projections.
- The actual reduction is `D.X.left.nilradical.subscheme`, with inclusion
  `D.X.left.nilradical.subschemeι`. No abstract reduced replacement is used.
- The open subscheme `U` of that reduction has exactly the preimage of
  `connectedComponent (GrpObj.onePoint D.X)` as its underlying set. Reduction is
  a homeomorphism on underlying spaces, so this is precisely the identity
  component of the reduction; choosing its open subscheme structure is explicit.
- H represents this specified open subscheme through the F-scheme isomorphism
  `e : H.X ≅ Over.mk (U.ι ≫ D.X.left.nilradical.subschemeι ≫ D.X.hom)`.
  Its group inclusion `j : H ⟶ D` satisfies
  `j.hom.hom.left = e.hom.left ≫ U.ι ≫ D.X.left.nilradical.subschemeι`.
  Thus H cannot be a different torus with the same rational points: its whole
  scheme and its inclusion are identified with the reduced identity component.
  The group law is the induced subgroup law, since this inclusion is monic.
- Closed subgroup of D is `IsClosedSubgroupScheme j.hom.hom`.
- Split torus is `∃ n : ℕ, Nonempty (H ≅ MultiplicativeType.splitTorus F n)`;
  this is an isomorphism of group schemes, including n = 0.
- The induced inclusion into M is exactly `j ≫ pM`; its maximality is
  `ReductiveTorusCentralizer.IsMaximalTorus (j ≫ pM)`.
- No reductivity assumption appears. There are no smoothness or reducedness
  assumptions on D, and the construction takes its full nilradical quotient.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic, as specified by the algebraic-closure match.
- `CategoryTheory.Grp`, `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp.
- `AlgebraicGeometry.IsClosedSubgroupScheme` and `IsNormalSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. These test subgroup and
  normality on all commutative F-algebras, including nonreduced algebras.
- `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `ConnectedSpace` and `connectedComponent`, Mathlib.Topology.Connected.Basic.
- `AlgebraicGeometry.ReductiveTorusCentralizer.IsMaximalTorus`,
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology.
- `AlgebraicGeometry.StandardGroupSchemes.multiplicative` and `multiplicativeGroup`,
  Sheaf.AlgebraicGeometry.StandardGroupSchemes; these are used in the existing
  `MultiplicativeType.splitTorus` from Sheaf.AlgebraicGeometry.ToriMultiplicativeType.
  That module also supplies the existing `IsTorus` used by `IsMaximalTorus`.
- `CategoryTheory.Limits.pullback` and its projections,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback; its universal property
  is expressed with `CategoryTheory.IsPullback`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs.
- `AlgebraicGeometry.Scheme.nilradical`, Mathlib.AlgebraicGeometry.IdealSheaf.Basic;
  `Scheme.IdealSheafData.subscheme` and `subschemeι`,
  Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme.
- `AlgebraicGeometry.GrpObj.onePoint`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Basic, is the image of the unique
  point of Spec F under the unit section; it introduces no choice of identity.

All available proof-dependency modules are imported directly, with proof-only
imports non-public: Krull dimension, dimension finiteness, closed immersions,
smooth geometric reducedness, Borel/maximal-torus conjugacy, locally algebraic
group identity components, and multiplicative-type largest subtori.

Edge cases checked before writing: F has arbitrary characteristic; no perfectness
hypothesis is added beyond algebraic closedness. Trivial G, M, or T and rank zero
are allowed. If M is trivial, H is the rank-zero torus. If M = G, the component is
T. A unipotent ambient group is not excluded. Nonreduced intersections and
nontrivial finite disconnected parts of D are handled by the actual nilradical
quotient followed by its identity component. Empty groups cannot arise, because
the group-object structure includes the unit Spec F → G. The universe u is
explicit, and auto-implicit binding is disabled. No independent smaller test
algebra universe is introduced.

Searches made using the prescribed `msearch.py` wrapper:

- LeanFinder: “The reduced identity component of the intersection of a maximal
  torus with a smooth connected closed normal subgroup of an algebraic group is
  a maximal torus of that subgroup”. Eight hits: connectedComponentOfOne,
  Frattini subgroup results, Cartan Lie subalgebra results, and an Engel result.
  None is a group-scheme theorem about maximal tori.
- Loogle: `"maximal", "torus"`: zero hits.
- Mathlib grep in AlgebraicGeometry:
  `maximalTorus|maximal_torus|subtorus|MultiplicativeType`: zero hits.
- `rg` in the prescribed WeilConjectures and Sheaf source directories:
  `normal.*[Tt]orus|[Tt]orus.*normal|lem-sfb-normal-subgroup-maximal-torus-intersection`.
  Sheaf hits concern finite-etale splitting, unipotent quotients, normalizers,
  root parametrizations, and related results; none states this intersection theorem.
  There was no upstream theorem match. A separate search for the proposed full
  declaration name in both project roots, Mathlib and dag/lean_names_upstream.json
  found no name collision.

No STATEMENT-DISPUTED flag or node fault was found. The node's statement is retained
verbatim. The theorem asserts only its listed conclusions, not the additional
“every maximal torus is of this form” assertion in the cited source.

Validation: the prescribed scompile.py compiled the delivered file cleanly in
both sandbox and library-module mode. The sole postponed proof is the named
main theorem. No diagnostic commands or local notation remain.

## Second reading by NZ

The dispatcher assigns a single worker and explicitly prohibits starting other
agents. This section records a second pass by that worker; the independent
mathematical review is the maintainer's review of the delivery.

I reopened the node and final module and compared each clause. The delicate
points are the scheme intersection, the order of reduction and identity
component, and the actual induced inclusion into M. The IsPullback clause
specifies the entire fibre product. The equality defining U is in the space of
the actual reduction and gives it the required open subscheme structure. The
isomorphism e and equality for j identify the inclusion, not merely its image
on points. Consequently `j ≫ pM` is the intended M-inclusion. The split-torus
isomorphism is in Grp, not just schemes. The existing maximal-torus predicate
retains arbitrary containing tori and rank zero. No reductivity, affine/finite-type
hypotheses on M, or smoothness/reducedness hypotheses on D were inadvertently
added. No mismatch or source-based correction was needed. Direct imports of
the recorded terminology and all stated proof dependencies were checked in the
final pass.
