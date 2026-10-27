## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.UnipotentExtensionArbitrary` states
`AlgebraicGeometry.unipotent_extension_arbitrary`, with its sole proof `sorry`.
It states the existing DAG assertion without changing its statement, dependencies,
proof, or any other non-Lean field. No definitions, helper nodes or dependency repairs
are introduced. There is no statement dispute.

Hypothesis and conclusion correspondence:

- The arbitrary base field is `{k : Type u} [Field k]`.
- `N E Q : Grp (Over (Spec (.of k)))` are the three k-group schemes. The bundled
  arrows `i : N ⟶ E` and `q : E ⟶ Q` are homomorphisms over this same field.
- For each of N, E and Q, `IsAffine G.X.left` is affineness, and
  `LocallyOfFiniteType G.X.hom` together with `QuasiCompact G.X.hom` is finite type.
- `IsClosedSubgroupScheme i.hom.hom` is the specified closed subgroup N in E.
  `IsNormalSubgroupScheme i.hom.hom` is normality over every commutative k-algebra.
- `hq : SolvableGroupStructure.IsFppfQuotient i.hom.hom q` uses precisely the
  dependency's definition of a represented fppf quotient: flat, surjective,
  locally finitely presented, with an isomorphism from the specified N to the
  scheme-theoretic kernel commuting with its inclusion. As the dependency's
  statement and docstring explain, these conditions identify the represented
  sheaf with the fppf sheafification of the cosets: points locally lift along
  the fppf cover, and two lifts differ by a unique kernel point. This does not
  assume global surjectivity on algebra points.
- Each of `hN` and `hQ` quantifies `∃ (n : ℕ), 0 < n ∧ ∃ r : G.X ⟶ GL_n`.
  `IsClosedSubgroupScheme r` makes r a closed group immersion. For every
  `R : Type u` with `[CommRing R] [Algebra k R]` and every R-point x,
  `GeneralLinearGroup.homMulEquiv ... (x ≫ r)` is its image matrix. The first
  equation requires each diagonal entry to be 1; the second requires every
  entry `(a,b)` with `b < a` to be 0, exactly upper unitriangular matrices.
- The conclusion is the identical positive-size closed unitriangular embedding
  condition for E. A closed embedding into GL_n satisfying these equations on
  every algebra is exactly a closed embedding into its closed subgroup U_n:
  evaluate at the coordinate-algebra universal point to see the defining ideal
  vanishes; the coordinate-ring surjection then factors through that quotient
  and remains surjective. Composing an immersion into U_n with U_n into GL_n
  gives the reverse presentation. Thus this is a direct expression of the
  node's embedding condition without introducing or choosing an ambient U_n.
- No smoothness, connectedness, commutativity, centrality, reducedness,
  perfectness or characteristic restriction occurs. In particular the existing
  `SolvableGroupStructure.IsUnipotent` is deliberately not used: it is the
  smooth geometric-point definition, whereas the present node explicitly
  defines unipotence by unitriangular embedding for arbitrary groups.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field` (the dependency's Mathlib match).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, bundled group maps,
  provided through the public dependency imports.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme` (and their inherited
  `IsSubgroupScheme` and `IsMonHom` interfaces).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  inherited by the recorded closed-subgroup class.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` is the recorded GL dependency
  module. As its node and docstring require, GL itself is the existing
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear` construction:
  `GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`. No copy of GL is made.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `SolvableGroupStructure.IsFppfQuotient`.

The already-stated proof dependencies
`Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry` and
`Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary` are plain
proof imports. The remaining four proof-lemma nodes have no Lean records in the
read repository and are named in the complete seven-step proof docstring for
stage 3; they are not needed to type the theorem. The closed-immersion dependency
is already a public import. The withdrawn CompactObject example was read along
with its node and its recorded upstream replacement.

Edge cases checked before writing: n=1 represents the trivial unitriangular
ambient group, so all trivial-group and identity-quotient cases remain covered;
n=0 is excluded exactly by the node's n≥1. Nonreduced algebras and group schemes,
including infinitesimal unipotent groups in positive characteristic, are retained
by the CommRing test-algebra quantifier. Imperfect fields and disconnected
unipotent groups are allowed. No group scheme over a field can be empty because
it has an identity section. The universal coordinate-algebra point is among the
quantified algebras: k, the schemes, and test algebras use the same universe u,
while `ULift.{u} (Fin n)` accommodates the upstream GL indexing convention.
There is no independent smaller test universe and no extra universe equality.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "An extension of arbitrary unipotent affine group
  schemes is unipotent without smoothness"`: eight hits on formally unramified
  morphisms and affine spaces; none states the group-scheme extension theorem.
- `msearch.py ... loogle '"IsUnipotent", "extension"'`: zero hits.
- `msearch.py ... grep 'unipotent.*extension|extension.*unipotent|Unitriangular'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "An affine algebraic group with unipotent normal
  subgroup and unipotent fppf quotient is unipotent"`: nilpotent abstract-group
  quotient lemmas, normality under opposite, and formally unramified lemmas;
  none is an affine group-scheme unipotence result.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the same terms, and
  the node id and proposed declaration name (also in `dag/lean_names_upstream.json`):
  no exact statement. The nearby
  `SolvableGroupStructure.isUnipotent_of_isFppfQuotient` in
  `GroupScheme/SmoothUnipotentExtension.lean` assumes an algebraically closed
  field and smoothness of all three groups, so is not a match. The existing
  `charZero_commutative_unipotent_vectorGroup` expresses the same unitriangular
  equations for its specialized characteristic-zero theorem; it supplies no
  general unipotence predicate to reuse. Its equation style is followed here.

Source checked directly in the local Milne PDF using pdftotext: Theorem 14.5
identifies unipotence with a subgroup of U_n, Corollary 14.7 asserts closure
under extensions, and §6.45 proves it via nonzero invariants and quotient descent.
These statements impose none of the excluded smoothness or perfectness assumptions.
The node's seven-step proof is fully carried into the theorem docstring.

Validation: scompile.py completed successfully for the sole delivered module,
in both sandbox and library modes, with no errors or warnings. The prescribed
deliver2.py dry-run preflight and per-file compilation are the final delivery checks.

## Second reading by Q85

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
