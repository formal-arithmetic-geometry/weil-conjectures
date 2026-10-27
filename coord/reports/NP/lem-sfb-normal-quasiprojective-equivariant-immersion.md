## Worker report

The module `Sheaf.AlgebraicGeometry.NormalQuasiprojectiveEquivariantImmersion` states
`AlgebraicGeometry.exists_normal_quasiprojective_equivariant_immersion`, with its sole
proof `sorry`. No original statement, proof, or proof dependency has changed.

Clause-by-clause correspondence:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Group scheme and its action: `G X : Over (Spec (.of k))`, `[GrpObj G]`, `[ModObj G X]`.
  `GrpObj` includes multiplication, inverse, identity and their laws. `ModObj` includes
  the action morphism, unit and associativity equations in the cartesian category over k.
- Smooth, affine, connected, finite-type G: `[Smooth G.hom]`, `[IsAffine G.left]`,
  `[ConnectedSpace G.left]`, `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- Separated finite-type X: `[IsSeparated X.hom]`, `[LocallyOfFiniteType X.hom]`,
  `[QuasiCompact X.hom]`.
- Normal X: `hnormal` requires `IsDomain` and `IsIntegrallyClosed` on each actual stalk.
  This is normality on every local ring, with no integrality assumption on the scheme.
- Quasi-projectivity: `hquasiprojective` supplies N and a k-morphism into the total-degree
  polynomial Proj in N+1 variables, with `IsImmersion i.left`.
- Nonzero finite-dimensional V: existential n represents the based vector space
  `ULift (Fin (n+1)) → k`. The coordinate basis has finite, positive cardinality n+1.
  Any nonzero finite-dimensional V has a basis of this cardinality, so this is exactly
  the existential assertion of the node, with no restriction on its representations.
- Group-scheme homomorphism: `ρ : G ⟶ GeneralLinearGroup ... k` and `IsMonHom ρ`.
  This is the existing polynomial determinant-localization GL, whose `homMulEquiv`
  identifies every algebra-valued point with an invertible matrix. For the based V,
  these matrices are exactly automorphisms of its scalar extension.
- P(V) is lines: the target is `Proj.projectiveSpaceOverAffineToSpec ... k`, literally
  Proj of the polynomial ring in n+1 variables with total-degree grading.
- Induced projective action: existential `a : ModObj GL P`, with
  `StandardLinearProjectiveAction.IsStandard ... a`. Its universal substitution is
  z_i ↦ sum_j x_ij z_j. Thus it is the action on lines of V, not the dual action.
  The graded lifts have their ENTIRE ring map fixed, including base coefficients;
  the comparison has BOTH projections fixed. No arbitrary comparison or action is assumed.
- Immersion: `IsImmersion j.left`; Mathlib `IsImmersion.isImmersion_iff_exists` gives
  exactly a closed immersion followed by an open immersion.
- Equivariance: `ModObj.smul (M := G) (X := X) ≫ j =
  (ρ ▷ X) ≫ (GL ◁ j) ≫ a.smul`, an equality in `Over (Spec k)`.
  This is precisely j after the G action equals the standard action after (ρ,j).
  Equality of scheme morphisms includes pullback to every algebra, including nilpotents;
  there is no test restricted to geometric points or reduced algebras.
- The final implication says `IsEmpty X.left → n = 0 ∧ ρ = toUnit G ≫ MonObj.one`:
  the empty case uses dimension one and the actual trivial homomorphism.
- X has no smoothness, integrality, projectivity, nonemptiness or faithfulness binder.

Dependency declarations read and reused:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`
  (the algebraically-closed clause of def-weil-algebraic-closure, not a chosen closure).
- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj`; Monoidal.Mon: `IsMonHom`;
  Monoidal.Mod and Monoidal.Cartesian.Mod: `ModObj`, its morphism and action laws.
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` documents these exact specializations.
- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Spec`, `Spec.map`;
  Limits.Shapes.Pullback.HasPullback: `pullback`; cartesian tensor in Over is this fibre product.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`;
  Morphisms.FiniteType: `LocallyOfFiniteType`; Morphisms.QuasiCompact: `QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.Separated: `IsSeparated`, the separated component
  of the proper-morphism conventions; no unintended properness assumption.
- Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: `IsIntegrallyClosed`;
  Algebra.Ring.Defs: `IsDomain`; the node's inline normal-domain convention is retained.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`;
  Morphisms.ClosedImmersion: `IsClosedImmersion`; Morphisms.Immersion: `IsImmersion`.
- Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme: `Proj`;
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace: `Proj.projectiveSpaceOverAffine`,
  `Proj.projectiveSpaceOverAffineToSpec`, whose bodies use `MvPolynomial.homogeneousSubmodule`.
- Mathlib.Algebra.MvPolynomial.Basic: `MvPolynomial`; Eval: `eval₂Hom`;
  Mathlib.LinearAlgebra.FiniteDimensional.Defs: `FiniteDimensional` (finite based-space encoding).
- def-sc-general-linear-group's recorded module `Sheaf.AlgebraicGeometry.LinearGroupSchemes`
  explains that GL is the upstream `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`.
  Its `GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv` and the upstream
  `Matrix.GeneralLinearGroup.CoordinateRing` and `coord` are used directly, with no second GL.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`, requiring nonemptiness as in the node.
- All eight proof dependencies with recorded Lean modules are plain imports, including
  `NormalLineBundlePowerLinearization`, `RelativeAmpleVeryAmple`, `FiniteSubcomodule`,
  `RationalRepresentationComoduleDictionary`, and `ProjectiveBundleQuotientGeometry`.
  The other four proof dependencies have no Lean record and introduce no imports.

Edge cases checked: empty X (explicit one-dimensional trivial conclusion); disconnected
normal X (pointwise stalk normality, no irreducibility); singular normal X; n=0 so P^0
is allowed; trivial G; nonfaithful representations; arbitrary characteristic; nonreduced
test algebras. k and the finite coordinate index live in the same explicit universe u,
using ULift. The predicates quantify scheme maps, avoiding an undersized test-algebra
universe. There are no new hypotheses or statement faults.

Searches: the attached msearch runs used LeanFinder on the complete embedding statement
(returned ordinary Proj/quasi-affine results), Loogle `AlgebraicGeometry.IsImmersion,
"projective"` (zero hits), and Mathlib grep `lineariz|equivariant.*projectiv|Sumihiro`
(zero hits). Searches in `lean/WeilConjectures` and `lean/Sheaf` by item id and projective
linear-action keywords found consumers and the torus-only diagonal action, not this theorem.
The new definition's searches are preserved verbatim in its `mathlib_searches`.

Sources read: Milne Section 7e Definition 7.26, printed p.145, for linear actions;
Brion https://arxiv.org/pdf/1703.09506v3, Introduction and Corollary 2.14, for Sumihiro's
embedding statement. Brion uses integral varieties; the accepted node's finite disjoint
union extension is retained, with no integral/smooth hypothesis on X added.

Verification: both delivered files compiled separately using the required scompile.py
in dependency order. The only elaboration error was fixed by supplying named arguments
`(M := G) (X := X)` to `ModObj.smul`. No diagnostic commands remain.

## New nodes

`def-sfb-standard-linear-projective-action` records the missing standard GL action on
scheme polynomial Proj, with its own module `StandardLinearProjectiveAction`. It defines
the actual universal matrix substitution `coaction` and a Prop `IsStandard` fixing the
action by Proj of this substitution under the canonical two-projection affine-base-change
comparison. Source: Milne Definition 7.26 and the standard matrix realization of its
projectivization; Stacks Constructions 01ND. No construction is selected from a mere
existence theorem, and neither definition uses sorry. The main theorem asserts the
existence of the standard action together with the immersion. This packages its induced
action clause; it is not an additional hypothesis.

LeanSearch and LeanFinder returned abstract `Projectivization` actions over division
rings, which cannot express scheme maps on arbitrary nonreduced algebras. Mathlib grep
found nothing; upstream/project grep found only an unrelated projective-line comment.
`DiagonalProjectiveAction.IsDiagonal` is specifically for a split torus and cannot describe
a full GL action. DAG keyword searches found no identical node. Blueprint searches
`projective action` and `general linear group action on projective space` each returned
zero nodes. `blueprint_refs.py ancestor` explicitly returned `from.node = None`; the new
node preserves that answer and prepends the item to its inherited via chain.

## Second reading by NP

This is an author self-audit: the dispatcher explicitly forbids starting another agent,
and the maintainer performs the independent delivery review. I reopened the final Lean,
the item JSON, and the new definition JSON and checked every binder and conjunct against
the mapping above. The finite based-space encoding has positive rank without excluding
the empty-scheme case. The standard action's coefficient and variable substitutions use
the matrix, not its transpose or inverse. The comparison is pinned by both projections,
so it cannot absorb an arbitrary projective automorphism. The equivariance equation has
the correct source G×X and target P and is scheme-theoretic. The empty-case conjunct was
added explicitly during this check. No original fields other than lean and the authorized
new stmt_dep changed. The new node is a definition, all data are explicit, all public
declarations have source/blueprint docstrings, and the only theorem proof is sorry.
