## Worker report

The module `Sheaf.AlgebraicGeometry.RationalRepresentationUnipotentPoint` states
`AlgebraicGeometry.rationalRepresentation_unipotent_point`, with its sole proof `sorry`.
The item is unchanged outside `lean`. No new notion, dependency repair, or statement
correction is needed.

I read the item, every statement dependency and its recorded declaration, and the proof
dependency records. I read Milne, Algebraic Groups (2017), printed pp.170–171, Theorem
9.18 and remarks 9.19–9.23, from `literature/milne-algebraic-groups_iAG2017.pdf` using
`pdftotext`. In particular, 9.19 says detection by one faithful representation gives
unipotence in all representations; 9.23 explicitly permits nonsmooth groups. The four
proof steps in the module docstring are the node's Jordan compatibility, Tannaka
reconstruction, faithful detection at K, and transfer of the positive nilpotence exponent.

Hypotheses and clauses, matched individually:

- The algebraically closed field K is `{K : Type u} [Field K] [IsAlgClosed K]`.
  Mathlib's `IsAlgClosed` defines splitting of every polynomial and documents its
  equivalence with the existence of roots for every nonconstant polynomial.
- The K-group scheme is `(G : Over (Spec (.of K))) [GrpObj G]`. The base is part of
  the bundled object, so all morphisms below are over K. `GrpObj` supplies precisely
  multiplication, identity and inverse with their group diagrams.
- Affineness is `[IsAffine G.left]`. Finite type is the recorded pair
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- The integers m,d >= 1 are `(m d : ℕ) (hm : 0 < m) (hd : 0 < d)`. These include
  exactly the stated dimensions. `LinearGroupSchemes.Index.{u} n` is `ULift (Fin n)`,
  with exactly n indices and the universe required by the existing GL construction.
- The maps i and r are morphisms from G to `GeneralLinearGroup (Index n) K`, with
  `[IsMonHom i]` and `[IsMonHom r]` supplying the homomorphism property.
- Faithfulness is the explicit hypothesis `hi`: for every `(R : Type u)` with
  `[CommRing R] [Algebra K R]`, composition `x ↦ x ≫ i` is injective on the morphisms
  `(Spec (.of R)).asOver (Spec (.of K)) ⟶ G`. These are precisely G(R). The target
  is GL(R) under the existing bijection `GeneralLinearGroup.homMulEquiv`; injectivity
  is equivalent before and after this bijection. No closed immersion assumption is added.
- A single point is the argument `g : (Spec (.of K)).asOver (Spec (.of K)) ⟶ G`.
  There is no hypothesis on other points.
- The nilpotence premise is `hg : ∃ N : ℕ, 0 < N ∧ (...) ^ N = 0`, with the
  parenthesized matrix equal to
  `(GeneralLinearGroup.homMulEquiv (Index m) K K (g ≫ i)).val - 1`.
- The conclusion is `∃ M : ℕ, 0 < M ∧ (...) ^ M = 0`, using the corresponding
  d-by-d matrix from `g ≫ r`. Matrix `1` is the identity matrix; `.val` forgets
  invertibility without changing the entries. Thus both displayed powers are matrix powers.
- There is no smoothness, connectedness, or whole-group unipotence assumption.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field` (line 180); exposed through the field import.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` (line 43), and
  `Mathlib.CategoryTheory.Monoidal.Mon`: `CategoryTheory.IsMonHom` (line 213).
  I also read the group-scheme conventions in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (line 43); its imported QuasiCompact module:
  `AlgebraicGeometry.QuasiCompact` (line 43).
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`: `AlgebraicGeometry.LinearGroupSchemes.Index`;
  its public upstream import `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`:
  `AlgebraicGeometry.GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`.
  I read the construction and full signatures of these declarations. Only the general
  linear portion of the dependency is needed here; the special linear declarations are
  not duplicated.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` (line 471), exposed by
  the imports. `Scheme.asOver` supplies the canonical spectrum over the base field.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` and its root characterization
  (lines 58–80).

The proof dependencies `lem-sfb-multiplicative-jordan-linear-compatibility` and
`lem-sfb-tannaka-rational-point-reconstruction` have no recorded Lean module in the
read clone. They are cited in the proof docstring. Neither is needed to type this statement.

Edge cases checked: m=d=1 gives scalar unipotence equal to 1; identity points allow N=M=1;
the trivial group is allowed. Dimensions zero are excluded exactly as in the node, while
the proof plan still allows the zero representation in its Tannaka family. Both positive
and zero characteristic are permitted. Nonreduced group schemes and nonreduced or zero
test algebras are permitted: there is no reducedness, domain, or nonzero-ring assumption
on R. No restriction on connected components is imposed. All test algebras use the base
universe u, which also contains K and the coordinate algebras, so the quantifier includes
R=K and the universal affine test algebras; it is not a smaller, potentially vacuous universe.

Searches actually run through `msearch.py Q133 lem-sfb-rational-representation-unipotent-point`:

- `leanfinder`: “If a faithful rational representation sends a point of an affine algebraic
  group to a unipotent matrix then every rational representation does”. Eight hits,
  including LieModule faithfulness, SL scalar extension injectivity and finite-group
  Tannaka results; none states the result for affine algebraic groups.
- `loogle`: `"IsNilpotent", "Representation"`. Zero hits.
- `leansearch`: “rational representations of algebraic groups preserve unipotent elements”.
  Eight hits, concerning rational casts, abstract representations and finite-group Tannaka;
  no exact match.
- `grep`: `unipotent|jordan.*decomp|decomp.*jordan` in Mathlib/AlgebraicGeometry.
  Zero hits (run twice, both zero).

Direct searches: `rg -n 'unipotent|Unipotent|rationalRepresentation'` on both
`lean/WeilConjectures` and `lean/Sheaf` found geometric-unipotence definitions and later
consumer proof plans, but no preservation theorem. A subsequent search for
`rationalRepresentation_unipotent_point|rationalRepresentation.*unipotent|faithful.*unipotent`
in Mathlib and both project source directories found no existing declaration.
Searching the exact node id in `lean/WeilConjectures` and `dag/lean_names_upstream.json`
found no match. The Sheaf hit in `CharZeroCommutativeUnipotentVectorGroup.lean` is a
proof-plan citation, not a declaration of this statement. `blueprint_refs.py search
'rational representation unipotent point'` returned zero matching blueprint nodes.

Validation: the prescribed `scompile.py` compiled the initial module in both sandbox
and library modes cleanly (2.3 seconds each). The final module also sets
`autoImplicit false`, and all variables and its single universe are explicitly bound.
No node fault or statement dispute was found.

## Second reading by Q133

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
