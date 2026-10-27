## Worker report

The module `Sheaf.AlgebraicGeometry.ChevalleyCharacterCancellation` states
`AlgebraicGeometry.chevalley_character_cancellation`, with exactly one postponed theorem
and no new definitions. The node copy changes only `lean`. No statement correction,
new node, or dependency repair is needed.

I read Milne, Algebraic Groups (2017), Theorem 4.27, Lemma 4.28, Corollary 4.29
and Remark 4.30 (printed pp.94--96), including the erratum on the ambient tensor
representation. The statement is Corollary 4.29 with the all-algebras meaning of
stabilizer specified by Remark 4.30. Its proof docstring includes all three DAG
proof steps, including the coordinate contraction over nonreduced algebras.

Hypotheses and clauses, matched individually:

- A field k: `{k : Type u} [Field k]`.
- G and H are k-group schemes: `G H : Over (Spec (.of k))`, with `[GrpObj G]`
  and `[GrpObj H]`. Group laws and morphisms use the recorded group-object API.
- G affine: `[IsAffine G.left]`.
- G finite type over k: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, the
  conjunction specified by the finite-type dependency record.
- H a closed subgroup: `(i : H ⟶ G) [IsClosedSubgroupScheme i]`. This includes
  compatibility with multiplication and injectivity on every algebra's points.
- A finite-dimensional rational representation: a natural number `n` and
  `ρ : GeneralLinearGroup.RationalHom G (ULift.{u} (Fin n))`, with `IsMonHom ρ`.
  A choice of basis writes V as `ULift (Fin n) → k`; this represents every
  finite-dimensional vector space up to linear isomorphism. No positive-dimension
  assumption is imposed on representations in the character hypothesis.
- GL(V)(A) as A-linear automorphisms: `GeneralLinearGroup.homMulEquiv` supplies
  the existing natural invertible-matrix identification. `Matrix.toLin'` acts on
  the scalar extension `ULift (Fin n) → A` by that matrix.
- For each subspace U (and later L), its scalar extension is explicitly
  `Submodule.span A ((fun w ↦ fun j ↦ algebraMap k A (w j)) '' (U : Set ...))`.
  This is the image of U tensor A in V tensor A under the chosen basis.
  Over a field, the inclusion splits, so its base extension is injective for every A.
- Character: `χ : H ⟶ StandardGroupSchemes.multiplicative k`, with `IsMonHom χ`.
  Its scalar value is the coordinate ring map `(Spec.preimage (h ≫ χ).left).hom`
  evaluated at `LaurentPolynomial.T 1`. Because χ is an over-morphism, this map
  fixes k; because the target is the Laurent group, that value is a unit.
- Character occurrence: the antecedent of `hc` existentially quantifies n, ρ,
  its homomorphism proof, and `U : Submodule k (...)`, requires `U ≠ ⊥`, and
  states the scalar-action equation for every A, h in H(A), and v in U_A.
- Cancellation: for each occurring χ, the consequent of `hc` gives `m : ℕ`
  with `0 < m`, and another representation and nonzero U. The action scalar is
  the same character coordinate map evaluated at `T (-(m : ℤ))`. Laurent
  multiplicativity makes this precisely χ_A(h)^(-m). Quantifying positive
  naturals is equivalent to the node's quantification over positive integers.
- Conclusion representation: the outer existential gives n, ρ and `IsMonHom ρ`.
- Conclusion line: `L : Submodule k (...)` and `Module.finrank k L = 1`.
- Scheme-theoretic stabilizer: for every A and g in G(A), the equivalence
  `(∃ h : points H A, h ≫ i = g) ↔ Submodule.map ... L_A = L_A`
  says exactly that the subgroup image is the setwise stabilizer of L_A.
  It uses equality of submodules, not just forward stability or rational points.
- Pointwise fixed: the second conjunct for every A, h and v in L_A states
  `Matrix.toLin' (...) v = v`.
- Naturality: all points maps are composition of actual k-scheme morphisms,
  and `homMulEquiv` is the existing natural matrix identification; there is
  no independently chosen action on points.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (a commutative ring and division ring).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`;
  group homomorphisms use `CategoryTheory.IsMonHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, extending `IsSubgroupScheme`,
  which extends `IsMonHom` and supplies injectivity on all algebra-valued points.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`: the recorded general-linear
  dependency module, which reuses upstream `AlgebraicGeometry.GeneralLinearGroup`.
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear` defines that
  scheme and `GeneralLinearGroup.homMulEquiv`; the module
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie` defines
  `GeneralLinearGroup.RationalHom`. I read their full signatures and docstrings.
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional` is
  `Module.Finite`; coordinate spaces have finite dimension, and `Module.finrank`
  is used for the dimension-one conclusion.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.multiplicative` and `multiplicativeGroup`, the actual
  Laurent Hopf group scheme. `Spec.preimage` evaluates its actual coordinate maps.

The proof dependency `lem-sfb-chevalley-scheme-line-stabilizer` currently has no
Lean record or closed upstream audit; it is only a proof prerequisite and adds
no notion needed to state this item. No module can be imported for it yet.
The other proof dependency is `def-sc-gm-ga`, whose module is publicly imported
because its multiplicative group also appears in the statement.

Edge cases checked before writing: n = 0 is allowed in the hypothesis's search
for representations (then its nonzero U condition is false). The conclusion's
rank-one condition forces nonzero V. The zero algebra A is included without a
Nontrivial assumption: its vector modules are zero and all group-of-points sets
are singletons. Nonreduced algebras are included. H = G, trivial H, trivial χ,
m = 1, and characteristic dividing m introduce no extra hypotheses or divisions.
The zero-space GL is the existing empty-matrix group scheme. No smoothness,
reducedness, algebraic closure, or characteristic-zero hypothesis is added.
All scheme, field and test-algebra sizes use one explicit arbitrary universe u,
matching the recorded subgroup and general-linear interfaces; larger mathematical
objects can be considered by choosing a larger u and lifting the base field.

Searches (2026-10-24):

- `msearch.py ... leanfinder` query: “A closed subgroup scheme is the stabilizer
  of a pointwise fixed line if every occurring character has an occurring negative
  power”. Eight hits concern abstract fixing subgroups, invariants and inertia;
  none gives the rational group-scheme representation in this statement.
- `msearch.py ... loogle` query: `"stabilizer", "Submodule"`. Four hits:
  `Submodule.stabilizer_coe`, `Submodule.mem_stabilizer_submodule_iff_map_eq`,
  `LinearEquiv.mem_stabilizer_fixedSubmodule`, and
  `LinearEquiv.mem_stabilizer_submodule_of_le_fixedSubmodule`. These express
  abstract-action stabilizers and do not give this theorem.
- `msearch.py ... leansearch` query: “rational representation affine group scheme
  occurring character negative power stabilizer line”. Eight unrelated hits
  (norm-num negative powers, affine schemes, abstract stabilizers and rational
  functions); no match.
- `msearch.py ... grep` query: `Chevalley|stabilizer.*line|character.*occur`
  in Mathlib/AlgebraicGeometry. Four hits concern constructibility of images.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for `Chevalley|chevalley|
  RationalRepresentation|rationalRepresentation|CharacterOccurs|characterOccurs|
  scalarAction`, and focused `RationalHom|occurs` searches: existing rational
  representation/comodule and matrix group APIs found; no character-cancellation
  theorem. The comodule dictionary's NaturalRepresentation would be an alternative
  encoding, but is unnecessary since the node defines finite representations
  directly by group-scheme homomorphisms.
- `grep -rn 'lem-sfb-chevalley-character-cancellation' lean/WeilConjectures`:
  no hit. A full-name search for `chevalley_character_cancellation` in Mathlib,
  WeilConjectures, Sheaf and `dag/lean_names_upstream.json` also found no declaration.

Validation: prescribed `scompile.py Q16 lem-sfb-chevalley-character-cancellation`
compiled both sandbox and actual module identity cleanly. The signature is copied
verbatim into the node's lean.statement, all universes and binders are explicit,
and all source lines are at most 100 characters. No STATEMENT-DISPUTED issue found.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
