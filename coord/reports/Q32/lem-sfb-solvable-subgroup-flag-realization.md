## Worker report

The delivery states `AlgebraicGeometry.solvableSubgroup_flag_realization` in
`Sheaf.AlgebraicGeometry.GroupScheme.SolvableSubgroupFlagRealization`.
Its sole theorem has proof `sorry`; every definition has actual data. There is
no statement correction and no disputed assertion.

Hypothesis and clause correspondence:

- The algebraically closed base field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- `G H : Over (Spec (.of k))` with `[GrpObj G] [GrpObj H]` are the group schemes.
  `[IsAffine _.left] [LocallyOfFiniteType _.hom] [QuasiCompact _.hom]` express
  the affine finite-type convention for both groups. No characteristic restriction.
- `[Smooth G.hom] [ConnectedSpace G.left]` and their H counterparts express
  precisely the smoothness and connectedness hypotheses, including nonemptiness.
- `i : H ⟶ G` with `[IsClosedSubgroupScheme i]` is the given closed subgroup.
  This class includes the group-homomorphism condition.
- `hsolv : IsSolvableGroupScheme H` is termination of the actual scheme-derived
  series, using the already landed definition from the semisimple-group node.
  It is not abstract solvability of the group of rational points.
- The first existential chooses n, r and L. The vector space is
  `LinearGroupSchemes.Index n → k`, a finite-dimensional coordinate realization
  of V, and `0 < n` says it is nonzero. Every finite-dimensional space admits
  such coordinates; this changes neither the existential representation assertion
  nor the subsequent universal assertion about arbitrary finite-dimensional
  representations. The common-universe ULift indices exclude no finite dimension.
- `IsMonHom r ∧ IsClosedImmersion r.left` makes r a faithful group-scheme
  representation. The GL target is the existing coordinate Hopf-algebra scheme.
- `L : CompleteFlagPoints.Points n k` supplies all terms, endpoints, inclusions
  and dimensions. Over k the finite locally free rank condition is dimension i.
- `CompleteFlagPoints.IsStabilizer i r L` states equality with H on every
  commutative k-algebra A, retaining nonreduced scheme structure.
- The X existential gives an actual scheme representing Fl(V). The equivalences
  `e A` classify its affine-valued points by flags; the equation for every
  `f : A →ₐ[k] B` states precisely naturality under scalar extension.
  A scheme representing this functor on affine test schemes represents the
  full flag functor: the locally direct-summand data glue uniquely on affine
  covers. No universal flag, arbitrary map or comparison is assumed as a premise.
- `IsProjective X.hom` is the recorded projective notion, and
  `LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom` is finite type.
- The universal Z,j clause assumes exactly closed immersion and reducedness,
  and concludes `IsProper Z.hom` and finite type. It includes the empty Z.
- The second conjunct quantifies over every m (including zero), representation s
  and complete flag E. Its two premises require a group homomorphism and closed
  immersion, as in the first representation clause.
- K,j is the scheme-theoretic stabilizer, with `IsClosedSubgroupScheme j` and
  `IsStabilizer j s E`. Existence here makes the implicitly named K explicit.
- U is the open identity component of K, with
  `(U : Set K.left) = connectedComponent (GrpObj.onePoint K)`.
  Its reduction is the actual `U.toScheme.nilradical.subscheme`. The given
  group structure gJ, together with the closed subgroup condition on its
  canonical composite inclusion in K, is the induced subgroup structure.
  Thus this is `(K⁰)_red = (K_red)⁰`, not an arbitrary smooth subgroup.
  Reduction leaves the topology unchanged and commutes with restriction to U.
- `Smooth`, `ConnectedSpace` and `IsSolvableGroupScheme` on that reduction are
  the three asserted properties of the reduced identity subgroup. The last
  equality uses `topologicalKrullDim` on its actual underlying space and on K.

Dependency declarations used:

- `Field`, `IsAlgClosed` and `FiniteDimensional` are the Mathlib notions read in
  Algebra.Field.Defs, FieldTheory.IsAlgClosed.Basic and
  LinearAlgebra.FiniteDimensional.Defs. The coordinate finite-dimensional space
  needs no extra witness or new definition.
- `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp; the same group
  objects are used by the recorded `WeilConjectures...GroupScheme.Defs`.
- `IsClosedSubgroupScheme`, `IsSubgroupScheme`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: closed homomorphic subgroup
  inclusions, retaining the existing pointwise interpretation.
- `Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth; `ConnectedSpace`,
  Mathlib.Topology.Connected.Basic; finite type/closed immersion/properness are
  the Mathlib declarations named by the morphism-conventions dependency.
- `GeneralLinearGroup`, `GeneralLinearGroup.homMulEquiv`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`; imported through
  the recorded `Sheaf.AlgebraicGeometry.LinearGroupSchemes`, whose
  `LinearGroupSchemes.Index` is reused without a second index declaration.
- `Scheme.nilradical`, `Scheme.IdealSheafData.subscheme`, and `.subschemeι`,
  Mathlib.AlgebraicGeometry.IdealSheaf.Basic/Subscheme; reduction is not replaced.
- `topologicalKrullDim`, Mathlib.Topology.KrullDimension.
- `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`, `IsDerivedGroupScheme`,
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`. Its node is added to stmt_deps
  because this existing exact derived-series notion was omitted there originally.
- `IsProjective`, `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, is
  precisely the projective convention referenced by def-pc-morphism-conventions.
- `GrpObj.onePoint`, `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`.
- All `CompleteFlagPoints` declarations in the new node below.

The module privately imports all available nontrivial proof-dependency modules:
HomomorphismFactorization, FreeQuotientGrassmannProjective,
ProjectiveSpace.Product, LocallyAlgebraicGroupIdentityComponent and
GroupNeutralComponentTranslates. Projective-proper and IsProper come through
existing statement imports. The Chevalley, prescribed-kernel, triangular-kernel,
smooth-unipotent-solvable and solvable-fixed-point nodes have no recorded Lean
module in this checkout, so no import can yet be added for them. They are proof
prerequisites, not new statement objects. The docstring supplies all eight
natural-language proof steps, including the faithful direct-sum refinement.

Edge cases checked before writing: G=H=1; H=G solvable; H=1; dimension one;
zero-dimensional arbitrary faithful representations (then G is trivial);
characteristic p and characteristic two; nonreduced test algebras; disconnected
algebras with nonfree projective submodules; the zero algebra (unique flag,
empty prime spectrum); empty closed reduced Z. Complements are not specified as
part of flag data, so two choices of a splitting give the same flag. Nested
subbundles have locally free successive quotients by locally splitting the
surjection of their finite projective ambient quotients.

Searches: msearch LeanFinder query "A solvable algebraic subgroup is the
stabilizer of a complete flag in a faithful representation and the flag scheme
is projective" returned representation-category projectivity and abstract
stabilizer results, no match. Loogle query "AlgebraicGeometry.GeneralLinearGroup,
Flag, IsSolvable" found no identifier for the scheme-level GL in Mathlib. The
Mathlib grep "CompleteFlag|FlagVariety|IsSolvable" in AlgebraicGeometry found
nothing. For the new notion, LeanSearch's complete-direct-summand-flag query
returned basis flags and lattices; Loogle "Flag" returned maximal chains;
Mathlib LinearAlgebra grep found only Basis.Flag. Those do not describe
nonfree projective flags on algebras. Project rg searches of GroupScheme,
Sheaf/AlgebraicGeometry and WeilConjectures found no flag point/stabilizer
notion. Searching the exact item id in WeilConjectures found nothing.
DAG searches and `tools/blueprint_refs.py search complete flag` found the
existing flag-bundle construction, but no node for these points or their scalar
extension. The new node records the full returned search outputs.

Read source: Milne Section 7g, pp.146--147 and Theorem 17.9, p.354, directly
from the local PDF using pdftotext; its flag functor uses direct factors of
constant rank, exactly the definition supplied here. Theorem 17.9 first uses
a Chevalley line, then a complete flag in the quotient by that line.

## New nodes

`def-sfb-complete-flag-points` defines `CompleteFlagPoints.Levels`, `IsComplete`,
`Points`, `extend`, `Preserves` and `IsStabilizer` in its own module
`Sheaf.AlgebraicGeometry.GroupScheme.CompleteFlagPoints`. The source is Milne
7.29--7.30 and 17.9. Data are submodules; completeness is a predicate, and
extension is the actual span of the coordinate image. Matrix preservation uses
`Submodule.map (Matrix.toLin' g.val)`. Rank uses Mathlib `Module.rankAtStalk`;
no free-basis assumption replaces locally free subbundles. The existing
`def-pur-complete-flag-bundle` supplies a recursively constructed universal
scheme with tautological sheaves, and does not define these algebra-valued
points or their base change. Mathlib maximal chains are not the functor on
rings: over a general ring, intermediate submodules need not be subbundles.
The recorded three search kinds and the project/DAG searches found no exact
notion. No dependency interface is repaired or duplicated.

## Second reading by Q32

Author consistency check (not an independent review): reopened both source
modules and both JSON records. Checked all binders and both conjuncts against
the node, including naturality for arbitrary algebra maps, closed immersion
faithfulness, nonreduced tests, zero m, the induced subgroup law on the actual
reduction of the open identity component, and equality of dimensions. The
original index alias was removed in favor of the existing
`LinearGroupSchemes.Index`. Fixed inference of the source of the canonical
reduction inclusion by explicitly specifying its Over object. Independent
review is performed by the maintainer under this dispatcher's delivery model;
no sub-agent was started and no independent reader is claimed here.
