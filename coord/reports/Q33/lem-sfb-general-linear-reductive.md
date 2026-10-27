## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.GeneralLinearReductive` states
`AlgebraicGeometry.GeneralLinearGroup.isReductive`, with its entire proof `sorry`.
It introduces no definitions. The source was read directly in Milne,
Algebraic Groups (2017), printed pp.401 (19.16--19.19), 52--53 (2.40--2.42),
399--400 (the reductivity convention), and 75 (3.35).
The node's statement and proof are unchanged.

Hypotheses and clauses, read against the actual Lean bodies:

- A field k: `(k : Type u) [Field k]`, with arbitrary universe u and no
  characteristic, perfectness, or algebraic-closedness hypothesis.
- n >= 1: `(n : ℕ) (_hn : 1 ≤ n)`. The underscore suppresses only the unused
  binder warning in this stage-2 sorry statement; the hypothesis is retained.
- G = GL_(n,k): `Grp.mk (AlgebraicGeometry.GeneralLinearGroup
  (LinearGroupSchemes.Index.{u} n) k)`. The recorded GL definition node imports
  the existing upstream GL, the spectrum of
  `Matrix.GeneralLinearGroup.CoordinateRing`, literally the localization of
  the polynomial algebra in matrix entries away from its generic determinant.
  `Index n = ULift (Fin n)` has exactly n elements and respects the upstream
  shared universe of the coordinate index and base ring. `Grp.mk` packages
  that very object with its existing Hopf-algebra group law.
- Smooth over k: the conclusion's `ReductiveTorusCentralizer.IsReductive`
  contains `Smooth G.X.hom`.
- Affine: its `SolvableGroupStructure.IsAlgebraic G` is defined as
  `IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom`.
- Finite type: the last two conjuncts are exactly the finite-type definition
  recorded by def-weil-finite-type-morphism; no finite or proper hypothesis.
- Geometrically connected: the predicate includes
  `ConnectedSpace ((MultiplicativeType.baseChange
  (K := AlgebraicClosure k)).obj G).X.left`. `baseChange` is the actual
  pullback functor along Spec(kbar) -> Spec(k), lifted to group objects.
  `ConnectedSpace` includes nonemptiness.
- Reductive: the predicate universally quantifies over group schemes U and
  group homomorphisms j into that actual base-changed G. It requires
  `IsClosedSubgroupScheme j.hom.hom`, `IsNormalSubgroupScheme j.hom.hom`,
  `ConnectedSpace U.X.left`, and `SolvableGroupStructure.IsUnipotent U`;
  the last predicate includes `Smooth U.X.hom`. It also requires
  `IsAlgebraic U`, automatic for closed subgroups of affine finite-type G.
  It concludes `Nonempty (U ≅ Grp.trivial _)`, an isomorphism of group
  schemes, so infinitesimal subgroup structure is excluded too.
- Faithful finite-dimensional unipotence: `IsUnipotent` uses an existing
  closed faithful matrix representation r and tests every algebraically
  closed extension field F, every F-point x, and the actual matrix
  `GeneralLinearGroup.homMulEquiv ... (x ≫ r)`. Its condition is
  `∃ N : ℕ, 0 < N ∧ (matrix.val - 1)^N = 0`. This is precisely the node's
  geometric-points condition. A faithful representation of an affine
  algebraic group is a closed immersion by Milne 3.35, p.75, so this is
  equivalent to the node's pointwise faithful terminology. The existing
  predicate permits dimension zero, which adds only the trivial group:
  a faithful representation in GL_0 forces U trivial, and the trivial
  group also has the faithful one-dimensional identity representation.

The extra statement dependency
`def-sfb-reductive-torus-centralizer-terminology` is already landed and is
added under the rule allowing landed definition dependencies. Its existing
predicate gives exactly the whole conclusion; using it avoids another
private definition of reductivity. No new nodes or dependency repairs.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs; read its full class
  signature and docstring.
- def-sc-general-linear-group: Sheaf.AlgebraicGeometry.LinearGroupSchemes,
  `AlgebraicGeometry.LinearGroupSchemes.Index`; its module explicitly reuses
  `AlgebraicGeometry.GeneralLinearGroup` in
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear. Read the GL
  definition, group instance, `homMulEquiv`, and its coordinate-ring definition
  in WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup. The recorded
  main declaration `specialLinear` is the SL clause of that multi-clause
  node; the GL portion is the upstream definition, as its lean.note specifies.
- def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth; the same declaration is used
  by the reductivity and unipotence predicates.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`
  and `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms
  .FiniteType and .QuasiCompact; read both class signatures/docstrings.
- def-weil-connected-scheme: `ConnectedSpace`,
  Mathlib.Topology.Connected.Basic; read its nonempty class signature.
- def-sc-group-scheme-subgroup: `AlgebraicGeometry.IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`, in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. Read the full signatures:
  injectivity and normality are tested on every commutative k-algebra.
- Added definition dependency: `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`,
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology; read its entire
  body and docstring, and those of `SolvableGroupStructure.IsAlgebraic`,
  `IsUnipotent`, and `MultiplicativeType.baseChange` in the modules it imports.

Proof imports follow the node's stated plan: affine space and basic opens,
localization, multivariate polynomials, tensor products, affine pullbacks,
spectrum irreducibility and connectedness, smooth affine space,
smooth geometric reducedness, and the affine Nullstellensatz. In particular,
read `AffineSpace.smoothOfRelativeDimension_over`,
`Smooth.geometricallyReduced`, and all three Nullstellensatz declarations
named by the relevant nodes. The fixed-vector proof node has no Lean record
and is not needed to state this result; no import exists for it yet.
The declaration docstring records all six proof steps and their dependencies.

Edge cases checked: n=1 is G_m and the nonzero fixed vector spans directly;
no n>1 assumption slipped in. In positive characteristic the transvection
argument remains valid, with no linear reductivity assumption. The base may
be imperfect. The geometric fibre is not replaced by G(k) or GL_n(kbar) as
an abstract group. Nonreduced subgroup schemes such as mu_p cannot be ruled
out just by their geometric points; the smoothness hypothesis on U and the
scheme isomorphism conclusion retain precisely the source's distinction.
The trivial subgroup is allowed and satisfies the conclusion. An empty
scheme is not connected, and the identity section makes GL nonempty.
The same universe permits every affine algebra needed by this finite-type
construction; no independent smaller test-algebra universe is introduced.

Searches actually run with msearch.py (2026-10-24):

- Lean Finder: “The general linear group scheme over any field is smooth
  affine geometrically connected and reductive”. Eight hits, including
  LinearMap.GeneralLinearGroup, Matrix.GeneralLinearGroup, SpecialLinearGroup
  and Matrix.ProjectiveSpecialLinearGroup: abstract groups, no scheme theorem.
- Loogle: `"GeneralLinearGroup", "reductive"`: zero hits.
- Mathlib grep: `GeneralLinearGroup.*[Rr]educt|[Uu]nipotent[Rr]adical|[Rr]eductive[Gg]roup`:
  zero hits.
- LeanSearch: “The general linear group scheme over a field is reductive”.
  Eight hits on abstract GL definitions, matrix units and SL inclusions;
  no reductive group-scheme assertion.
- Direct rg searches of lean/WeilConjectures and lean/Sheaf for reductivity,
  unipotence, GL names and the exact node id found the definitions reused
  above and their consumers; no theorem asserting reductivity of GL.
  Also searched dag/lean_names_upstream.json for the proposed theorem name.

No statement fault or disputed assertion found. The node's source-place
reference to 2.42 concerns SL; GL connectedness is 2.40. Its proof already
records that distinction, and the module cites 2.40 without changing the node.

Validation: scompile.py compiled this file in both sandbox and library module
modes against the published server build, clean in 8.3 s and 6.9 s respectively.
No warnings. All variables and universes are explicitly bound, module mode is
used, and every line is at most 100 characters. The only postponed proof is
`AlgebraicGeometry.GeneralLinearGroup.isReductive`.

## Second reading by Q33

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
