## Worker report

The module `Sheaf.AlgebraicGeometry.SplitSolvableTriangularEmbedding` states
`AlgebraicGeometry.split_solvable_triangular_embedding`, with `sorry` as its entire proof.
The mathematical statement is unchanged. Its new statement dependency is the concrete
upper triangular group construction described below; there is no dependency repair or
statement correction.

Clause-by-clause rendering of the assigned node:

- A field k: `{k : Type u} [Field k]`, with the universe explicitly declared.
- A k-group scheme H: `H : Grp (Over (Spec (.of k)))`. This bundles the scheme over
  Spec(k) and its group-object structure, including multiplication, identity and inverse.
- Smooth: `hsm : Smooth H.X.hom`.
- Connected: `hc : ConnectedSpace H.X.left`.
- Affine: `haff : IsAffine H.X.left`.
- Finite type over k: `hft : LocallyOfFiniteType H.X.hom` together with
  `hqc : QuasiCompact H.X.hom`. These are exactly the local and quasi-compact parts
  of finite type; no separatedness or finite-presentation hypothesis is added.
- Split solvable: `hsplit : IsSplitSolvable H`, using the recorded dependency verbatim.
  Reading `SplitSolvableLength` shows that its positive step is a smooth connected
  closed normal subgroup with a represented fppf quotient isomorphic to G_a or G_m;
  its zero step is the trivial group. Thus none of the specified series conditions
  or quotient structures are replaced by abstract pointwise group solvability.
- Integer n at least 1: `∃ n : ℕ, 0 < n ∧ ...`. Natural positive dimensions give
  exactly the positive integers in this statement.
- B_n is the upper triangular subgroup of GL_n: `UpperTriangularGroup.scheme k n`
  is the actual spectrum of the quotient of the existing GL coordinate ring by
  the below-diagonal coordinates. Its canonical map is `UpperTriangularGroup.inclusion`;
  `UpperTriangularGroup.points` identifies its image with precisely the upper
  triangular invertible matrices over every commutative k-algebra.
- A homomorphism of k-group schemes H to B_n: `b : H.X ⟶ ...` is a morphism over
  Spec(k), and `IsMonHom b` imposes compatibility with multiplication and identity.
  For group objects this also imposes compatibility with inverses.
- A closed immersion: `IsClosedImmersion b.left`, the recorded Mathlib scheme notion.
  In particular faithfulness is scheme-theoretic, rather than injectivity only on
  rational points or on geometric field-valued points.
- Trivial H is allowed: neither H nor the length of its split series is required
  to be nontrivial. No perfection, algebraic closure, infinitude or characteristic
  assumption occurs anywhere in the signature or in the new construction.

Dependency declarations and sources read:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, and group-object morphisms;
  the specialization to `Over (Spec (.of k))` is documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` (def-sc-group-scheme).
- `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`: `IsSplitSolvable` and
  `SplitSolvableLength` (def-sfb-split-solvable-right-torsors). Also read
  `SolvableGroupStructure.IsFppfQuotient` in
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure` and the standard G_a/G_m interfaces.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`: the recorded general-linear node's
  module, using `LinearGroupSchemes.Index` (ULift (Fin n)). The module explicitly
  reuses the upstream GL construction. Read its `specialLinear` signature and its
  documentation, rather than mistaking that primary declaration for GL itself.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`: `GeneralLinearGroup`
  and `GeneralLinearGroup.homMulEquiv` (def-sc-general-linear-group).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, whose
  data are a closed embedding and surjectivity on stalks (def-weil-closed-immersion).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup`:
  `GeneralLinearGroup.subgroupScheme` and `GeneralLinearGroup.subgroupSchemeι`;
  read their canonical quotient definitions, group and closed-immersion instances.
- `WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup`: `CoordinateRing`,
  `coord`, and the actual GL Hopf structure. The quotient Hopf interface is
  Mathlib's `Ideal.IsHopfIdeal` and `HopfAlgebra.Quotient`.

All modules with usable records among the proof dependencies were checked: the four
lemma proof dependencies currently have no Lean records, so they have no import to
add. The already stated general-linear definition is imported through the new module.
The main theorem docstring contains every step of the supplied proof plan and names
all four lemma dependencies. Every helper theorem has a source and a complete proof
plan in its own docstring.

Edge cases checked before writing:

- H = 1: the length-zero series is allowed and the theorem can take n = 1.
- n = 1: the generating set of the ideal is empty, so B_1 is GL_1 = G_m;
  the below-diagonal equations are vacuous, as required.
- n = 0: the construction extends canonically to GL_0, but the assigned theorem
  explicitly requires `0 < n`, so it does not use an empty representation.
- Arbitrary fields: nothing requires perfection, characteristic zero or algebraic
  closure. The quotient Hopf construction works in every characteristic.
- Nonreduced and zero test algebras: `points` quantifies over `[CommRing A] [Algebra k A]`
  without domain or nontriviality assumptions. Its equations describe the entire
  represented subgroup, including infinitesimal points.
- Size: the field, schemes, and test algebras use the same explicitly bound universe u,
  matching the recorded scheme/GL interfaces. Matrix indices are ULift (Fin n),
  so the GL interface imposes no spurious restriction on the field universe.

Searches for the main statement:

- msearch.py leanfinder: “A smooth connected split solvable affine group scheme over
  a field has a faithful representation into upper triangular invertible matrices”.
  Eight hits were Lie algebra faithfulness/triangularizability and topological matrix
  embeddings, not this theorem.
- msearch.py loogle: `"IsSolvable", "Matrix"`: zero hits.
- msearch.py grep: `triangular|Triangular|trigonal` in Mathlib/AlgebraicGeometry:
  zero hits.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for upper triangular,
  triangular group, trigonalizable, split solvable and the assigned node id:
  matrix/Lie results and the split torsor definitions, no matching theorem or B_n.
- rg of the prospective declaration names and `dag/lean_names_upstream.json`:
  no conflicts. The existing closed-subgroup quotient machinery is reused.

There is no STATEMENT-DISPUTED issue. The local Milne PDF was read at printed
pp.324--325 and p.343: Proposition 16.52 gives the forward implication over any
field; perfection is needed only for its converse. No converse is asserted here.

Validation: both delivered modules compiled separately, in dependency order,
through the prescribed scompile.py wrapper against the live published server
library. The server reported 53.7 seconds for the upper triangular construction
and 7.2 seconds for the main theorem, with no errors or unexpected warnings.
The prescribed deliver2.py --no-push dry run passed: commit 4c8268d1e00
passes the preflight and compiles; nothing pushed. Final delivery runs the same
server compilation and preflight again before pushing.

## New nodes

`def-sfb-upper-triangular-group-scheme` supplies the missing concrete B_n.
Its source is Milne Section 16a, printed p.324, and Proposition 16.2, pp.324--325.
`UpperTriangularGroup.ideal` is the real ideal span of below-diagonal GL coordinates;
`ideal_isHopfIdeal` postpones only the proof that this specified ideal is a Hopf
ideal. `scheme` and `inclusion` directly reuse the upstream spectrum-of-quotient
construction and its quotient-map inclusion. There is no chosen arbitrary group,
unspecified representation, or data-valued sorry. The inherited instances make the
inclusion a group homomorphism and closed immersion. `points` states exactly the
universal-algebra image characterization. Both helper theorems' assertions occur
explicitly in the new node's statement, and their natural-language proofs are in
their docstrings.

Searches: msearch.py leansearch on “The upper triangular invertible matrix group
scheme is the closed subgroup of GL cut out by below diagonal coordinates” returned
eight ordinary matrix hits; loogle on `"IsUpperTriangular"` returned the matrix
predicate and eight matrix consequences; grep for triangular schemes/Hopf ideals
returned no hits. Project rg and the upstream name table had no definition of this
ideal or scheme. DAG searches found B_n used within theorem statements, but no
owning definition node. `blueprint_refs.py search 'upper triangular'` returned only
two unrelated Engel nodes; `blueprint_refs.py ancestor` returned None, preserved
as null in the new node's provenance, with the assigned item's full via chain.
The new node's mathlib_searches retain the search tool records verbatim as JSON.

## Second reading by Q30

A separate second pass reread the assigned node, the new node and both final module
texts clause by clause. It checked the group-scheme target is the actual quotient
B_n, that `IsMonHom b` is present (an arbitrary scheme morphism would be insufficient),
that closed immersion is on the underlying scheme morphism, and that finite type
includes quasi-compactness. It checked the strict inequality is j < i for the
vanishing coordinates, that all test algebras rather than just fields occur in
`points`, and that no perfection hypothesis was imported into the theorem.
No mismatch was found. This was a second pass by the dispatched worker, not a claim
that another agent reviewed it: the dispatch explicitly forbids starting agents,
and the maintainer's independent review reads the completed delivery.
