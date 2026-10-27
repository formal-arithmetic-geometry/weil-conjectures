## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.UnitriangularExtension` states
`AlgebraicGeometry.unitriangular_embeddable_of_isFppfQuotient`, with its whole proof
`sorry`. It preserves the node's statement and uses the existing subgroup, matrix group,
and represented quotient interfaces. No definitions, additional nodes, dependency repairs,
or statement corrections are needed.

Hypothesis and conclusion correspondence:

- The arbitrary field is `{k : Type u} [Field k]`. There is no algebraic closure,
  perfectness or characteristic restriction.
- `N E Q : Grp (Over (Spec (.of k)))` are precisely group schemes over k.
  For each of them `[IsAffine _.X.left]`, `[LocallyOfFiniteType _.X.hom]` and
  `[QuasiCompact _.X.hom]` express affine and finite type, including quasi-compactness.
- `i : N ⟶ E` and `q : E ⟶ Q` are group-scheme homomorphisms.
  `[IsClosedSubgroupScheme i.hom.hom]` makes i a closed subgroup immersion;
  `[IsNormalSubgroupScheme i.hom.hom]` expresses normality on all algebra-valued points.
- `hq : SolvableGroupStructure.IsFppfQuotient i.hom.hom q` is the dependency's exact
  quotient convention. It requires q flat, surjective and locally of finite presentation,
  together with an isomorphism from N to its scheme-theoretic kernel respecting i.
  This identifies the represented sheaf with the fppf sheafification of A ↦ E(A)/N(A).
  It does not assert that q is surjective on A-points for each A.
- `hN` and `hQ` render the two unitriangular embedding assumptions separately:
  `∃ (n : ℕ), 0 < n ∧ ∃ r : _.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k, ...`.
  Here `IsClosedSubgroupScheme r` includes the group homomorphism and closed immersion,
  and for every `A : Type u` with `[CommRing A] [Algebra k A]` and point
  `x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ _.X`, the matrix of `x ≫ r` has
  diagonal entries 1 and entry (a,b) equal to 0 when b < a. All three occurrences use
  the recorded `GeneralLinearGroup.homMulEquiv`, not a second functor-of-points map.
- The conclusion is the identical positive-size closed unitriangular embedding condition
  for E. Concretely a closed embedding into GL_n with these equations is exactly a closed
  embedding into U_n: apply the equations at the universal point over k[E], so the
  surjective coordinate map k[GL_n] → k[E] factors through the quotient by the equations
  x_aa - 1 and x_ab for b < a. The resulting map k[U_n] → k[E] is still surjective.
  Conversely composition with the closed inclusion U_n → GL_n gives precisely this
  condition. Thus no explicit independently constructed U_n is required to state the
  same notion. This is also the all-algebra encoding already used in the existing
  `CharZeroCommutativeUnipotentVectorGroup` and `AdjointKernelCentralQuotientUnipotent`
  statements. We introduce no private copy or second named definition of unipotence.
- No smoothness, reducedness, connectedness, commutativity or perfectness hypotheses are
  present. In particular the recorded `SolvableGroupStructure.IsUnipotent`, which starts
  with a Smooth conjunct and uses geometric matrices, would not state this node.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, and group-object morphisms.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, incorporated
  in the closed subgroup predicate.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`, the recorded module for
  def-sc-general-linear-group, publicly imports the unchanged upstream
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`.
  Its `AlgebraicGeometry.GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv` give
  exactly the GL_n scheme and the natural identification of A-points with matrices.
  No SL-specific declaration is used.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `AlgebraicGeometry.SolvableGroupStructure.IsFppfQuotient`. The full definition and
  its quotient-sheaf docstring were read; it supplies the kernel, rather than an
  arbitrary condition on a morphism.

The statement dependencies are public imports. Already recorded proof inputs are plain
imports: `Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`
(`AlgebraicGeometry.RationalRepresentation.dictionary` and its finite-dimensional clause),
`Mathlib.AlgebraicGeometry.Morphisms.Flat` (`AlgebraicGeometry.Flat.SpecMap_iff`), and
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
(`Module.FaithfullyFlat.of_comap_surjective`). The other proof nodes
lem-sfb-unitriangular-subgroup-rational-fixed-vector,
lem-sfb-central-kernel-cyclic-representation-descent, and
lem-sfb-affine-group-faithful-linear-representation have no recorded Lean module at
inspection, so there is nothing to import for them. They are proof inputs only and no
missing notion from them is needed for this statement. The theorem docstring gives
all six proof steps, naming each input.

Source and edge cases:

I read Milne, Algebraic Groups (2017), §6.45 (printed p.135), Theorem 14.5(a),(b)
(printed pp.281–282), and Corollary 14.7 (printed p.282), using `pdftotext -layout` on
the specified local PDF. The source's normal-invariant subspace argument matches all
six node steps; it uses no smoothness or perfectness.

The trivial group is included by n = 1 (U_1 is trivial); n = 0 is excluded exactly as
in the node, without excluding the trivial group. Cases N = 1 and N = E, Q = 1 are
allowed. In characteristic p, alpha_p embeds in U_2 via the upper-right coordinate,
and the constant Z/p also has a positive-size unipotent representation; nonsmooth
and disconnected groups have not been excluded. mu_p is not inadvertently declared
unipotent by testing only reduced or field-valued points: all commutative algebras
occur in each matrix condition. The zero test algebra is allowed and causes no problem
(0 = 1 there). An empty underlying group scheme cannot satisfy the group identity
section over Spec k; no extra nonemptiness premise is needed. Fin n includes all
positive finite sizes; ULift merely places the index in the upstream GL universe.
Test algebras have the same universe as the field and schemes, in accordance with
these recorded APIs; in particular coordinate algebras and universal affine points
are included, so the matrix equations are scheme-theoretic, not a weakened test.

Searches actually run (2026-10-24, wrapper log in the sandbox):

- `msearch.py ... leanfinder` with query "An extension of finite type affine group schemes
  whose kernel and fppf quotient embed in upper unitriangular matrix groups is
  unitriangular embeddable over an arbitrary field": eight results, including
  `Matrix.GeneralLinearGroup.upperRightHom`, its injectivity, matrix SL_2 results, and
  Lie-module triangularizability. None states this group-scheme extension theorem.
- `msearch.py ... loogle` with query "IsUnipotent, IsFppfQuotient,
  IsClosedSubgroupScheme": zero hits, unknown identifier IsUnipotent in the Mathlib
  search service. The project's declaration was inspected separately, as described above.
- `msearch.py ... grep` with regex
  `unitriangular|Unitriangular|unipotent.*extension|Unipotent.*Extension`: zero Mathlib hits.
- `msearch.py ... leansearch` with query "Extensions of affine finite type group schemes
  admitting a closed embedding into an upper unitriangular group are again unitriangular
  embeddable": eight hits on Lie modules, finite groups, closed immersion being affine,
  and unrelated additive/group constructions; no match.
- `rg -n` on `lean/WeilConjectures` and `lean/Sheaf` for unitriangular and extension terms:
  upstream only has an unrelated nonsingular-matrix-inverse comment; project hits include
  the two all-algebra embedding statements above and
  `SolvableGroupStructure.isUnipotent_of_isFppfQuotient` in
  `GroupScheme/SmoothUnipotentExtension.lean`. The latter assumes algebraically closed k
  and smooth N, E and Q, so does not state this node. Its exact full signature was read.
- `rg -n 'lem-sfb-unitriangular-extension' lean/WeilConjectures`: no hits.
- `rg` on `dag/lean_names_upstream.json` for unitriangular, unipotent and the proposed
  theorem name: no matching declaration of this theorem.
- DAG read found `lem-sfb-unipotent-extension-arbitrary`, the pre-existing same-statement
  node noted in this node's stage-1 split report; it has no recorded Lean declaration.
  It is not redefined or edited here; maintainers can attach this theorem to it if desired.

No statement dispute or node fault was found. All variables and the universe u are
explicitly bound; `autoImplicit` is false. Every line is at most 100 characters.

## Second reading by Q87

The delivered section under this heading was the worker re-reading its own work ("This is the
worker's own second check; no other agent was started"). The maintainer's reviewer replaced it
with the independent clause-by-clause reading below (review of c09ca529d097, 2026-10-24).
The Lean module and the node record are unchanged.

Node clauses, the Lean that renders each, and the verdict:

1. "Let k be a field": `{k : Type u} [Field k]`. No perfectness, characteristic or
   algebraic-closure assumption. Correct.
2. "Groups are affine k-group schemes of finite type": `N E Q : Grp (Over (Spec (.of k)))`
   with `[IsAffine _.X.left] [LocallyOfFiniteType _.X.hom] [QuasiCompact _.X.hom]` for each.
   Finite type = locally of finite type + quasi-compact. Correct.
3. "N ↪ E a normal (closed) subgroup": `i : N ⟶ E` with `[IsClosedSubgroupScheme i.hom.hom]`
   and `[IsNormalSubgroupScheme i.hom.hom]` (upstream GroupScheme.Defs: monoid hom,
   injective on all R-points, closed immersion; R-point image normal for all R). Both are
   implied by the kernel clause of the quotient, so they add no assumption. Correct.
4. "q : E → Q represents the fppf quotient, with scheme-theoretic kernel N":
   `hq : SolvableGroupStructure.IsFppfQuotient i.hom.hom q`. The live definition requires q flat,
   surjective and locally of finite presentation, and an iso `e : N.X ≅ GrpObj.ker q` with
   `e.hom ≫ kerι = i`. This is the dependency's exact convention. It does not ask that q be
   surjective on A-points. Correct.
5. "N and Q unipotent: for some n ≥ 1, a group homomorphism into U_{n,k} that is a closed
   immersion": `hN`/`hQ` ask for `0 < n` and `r : _.X ⟶ GeneralLinearGroup (ULift (Fin n)) k`
   with `IsClosedSubgroupScheme r`. For every `A : Type u` with `[CommRing A] [Algebra k A]`
   and every A-point x, the matrix `homMulEquiv … (x ≫ r)` has diagonal entries 1 and entries
   (a,b) with b < a (below the diagonal) equal to 0. Because the condition is tested at the
   universal point `Spec Γ(N) ≅ N` (Γ(N) : Type u), r factors through the closed subscheme of GL_n
   cut out by x_aa − 1 and x_ab (b < a), i.e. through U_n. The factorization is again a closed
   immersion, since k[GL_n] ↠ k[N] factors through k[U_n]. Conversely, a closed embedding into
   U_n composed with U_n ⊆ GL_n satisfies the condition. So this is exactly the node's notion,
   scheme-theoretic and not tested only on geometric points. The recorded
   `SolvableGroupStructure.IsUnipotent` (Smooth conjunct, geometric matrices) would be wrong
   here, and no def node for this nonsmooth notion has landed. The inline encoding is the one
   also used by the delivered CharZeroCommutativeUnipotentVectorGroup and
   AdjointKernelCentralQuotientUnipotent. Correct.
6. Conclusion "E unipotent": the identical condition for E. Correct, not weaker or stronger.
7. "No smoothness, reducedness, connectedness, commutativity or perfectness": none assumed.

Edge cases: n = 0 is excluded as in the node, and the trivial group is covered by n = 1.
N = 1 and N = E (Q = 1) are admitted. α_p (nonreduced, in U_2), constant ℤ/p and imperfect k
are admitted. μ_p is not wrongly unipotent because nonreduced A are tested. The zero algebra
A = 0 is harmless. Universes: k, the schemes and the test algebras all lie in u, as forced by
`Over (Spec (.of k))`. The ULift index is the upstream GL convention, so there is no
silent restriction.

Records and gates: the node differs from live only by `lean`. `lean.statement` occurs verbatim
in the file. The only declaration is a theorem whose proof is `sorry`, and there is no
definition. The module and theorem docstrings carry Milne §6.45, Thm 14.5, Cor 14.7 and
`(blueprint: lem-sfb-unitriangular-extension)`, and the theorem docstring gives the six
proof steps. The stmt_dep modules are public imports, and the proof-only imports are plain.
There is no pro-étale content.
H4: no Mathlib or project declaration states this theorem. The twin node
lem-sfb-unipotent-extension-arbitrary has no landed Lean. A parallel delivery of this same item
by Q143 (effb93da) is textually the same statement and had not landed at review time. Land one
copy only.
