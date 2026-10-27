## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusRationalFixedPoint` states
`AlgebraicGeometry.exists_rational_fixedPoint_of_splitTorus`, with its whole proof `sorry`.
No definition or auxiliary theorem is introduced. The source is Milne, Algebraic Groups
(2017), Theorem 16.51, printed p.343, read directly from the PDF (PDF page 355).
It states the fixed-point theorem for split solvable groups on complete algebraic schemes
with a rational point; our node is its split-torus specialization. Its multiplicative-group
limit argument and finite-coordinate induction are given in the theorem docstring, following
all six accepted DAG proof steps, including both dense-open morphism comparisons.

Hypotheses and conclusion, clause by clause:

- Any field k: `{k : Type u} [Field k]`. There is no assumption on characteristic,
  perfectness, cardinality, or algebraic closedness.
- A k-group scheme T: `(T : Grp (Over (Spec (.of k))))`. This uses the recorded
  `CategoryTheory.GrpObj` interface through the bundled `Grp`, which stores the group
  structure on `T.X`.
- Isomorphic as a group scheme to G_m^r for r at least zero: `(r : ℕ)` and
  `hsplit : Nonempty (T ≅ MultiplicativeType.splitTorus k r)`. The isomorphism is in
  the category of group objects, not merely of underlying schemes. The recorded
  `splitTorus` is the finite product of the existing canonical Laurent Hopf group
  `StandardGroupSchemes.multiplicative k`, with the trivial group at r = 0.
- Proper finite-type k-scheme: `(X : Over (Spec (.of k))) [IsProper X.hom]`.
  `IsProper` extends `LocallyOfFiniteType` and `UniversallyClosed`; the latter implies
  `QuasiCompact`. Thus both parts of finite type are present without adding redundant
  hypotheses. X need not be reduced, smooth, irreducible, or connected.
- A k-scheme action with both morphism identities: `[ModObj T.X X]`. Its `smul` is a
  morphism in `Over (Spec (.of k))` from the relative product to X. The fields
  `one_smul` and `mul_smul` are exactly the unit and associativity diagrams. The
  monoidal action on this category is tensor product, hence the scheme fibre product.
- X(k) nonempty: `hx : Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ X)`. The tensor unit is
  Spec k over itself, so these morphisms are precisely rational points.
- A rational point x: `∃ x : 𝟙_ (Over (Spec (.of k))) ⟶ X`.
- Every commutative k-algebra A: `∀ (A : Type u) [CommRing A] [Algebra k A]`.
- Every t in T(A): `(t : StandardGroupSchemes.affine k A ⟶ T.X)`. The domain is
  the recorded Spec A over Spec k; morphisms in `Over` enforce k-linearity.
- Scalar extension x_A: `toUnit (StandardGroupSchemes.affine k A) ≫ x`, the composite
  Spec A → Spec k → X. The equation `t • (...) = ...` uses Mathlib's internal
  Hom action, defined as pairing t and x_A followed by the action morphism. Thus
  the conclusion is the stated scheme-theoretic fixedness, not just fixedness by T(k).

All universes and variables are explicitly bound; autoImplicit is disabled. Test algebras
are in the same arbitrary universe u as the field and schemes, following the upstream
group-scheme convention. This is a full affine test for equality of the orbit morphism
T → X with the constant morphism: the affine split torus itself is a permitted test algebra.
Consequently it also determines fixedness on algebras in larger universes by scalar
extension; no restriction on geometric field extensions or infinitesimal test rings is
being imposed.

Dependency declarations used and read in source:

- `Mathlib.Algebra.Field.Defs`: `Field`, the recorded field definition.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, and group-object morphisms,
  the recorded group-scheme interface.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`, with
  `IsSeparated`, `UniversallyClosed`, and `LocallyOfFiniteType` as its parent classes.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact`, precisely the finite-type components.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.splitTorus`, whose existing DAG node
  `def-sfb-tori-multiplicative-type` is added to stmt_deps. Its existing module is
  imported, with no copied definition and no change to that dependency node.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.affine`, `.multiplicative`, and `.multiplicativeGroup`, used
  through the torus dependency. Their actual coordinate algebra and canonical Hopf
  group law were inspected. The latter sends the coordinate to t⊗t, 1, and t⁻¹.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `ModObj`, its `smul`, `one_smul`, and
  `mul_smul`; `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`: the Hom action,
  `CategoryTheory.Hom.smul_def`. These existing definitions express the action without
  introducing an additional notion.

Proof imports are plain imports: `Mathlib.Algebra.MvPolynomial.Basic` (the
polynomial-domain leaf), `Mathlib.AlgebraicGeometry.Noetherian` (the finite-type
Noetherian leaf), `Sheaf.AlgebraicGeometry.RationalMapExtensionValuationPoint`
(`AlgebraicGeometry.exists_extension_at_valuation_stalk`, recorded proof dependency),
and `Mathlib.AlgebraicGeometry.Morphisms.Separated`
(`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`, recorded proof dependency).
The affine-spectrum and properness dependencies are public through the statement imports.

Edge cases checked mathematically before writing: r = 0 keeps the given rational point;
empty X is excluded by the essential hx assumption; finite and imperfect fields are
allowed; a trivial action on a nonreduced proper X is covered; a scaling action on P¹
has rational fixed points; translation on G_m shows why properness must remain.
Nonreduced A, including dual numbers, are quantified, and the zero algebra is allowed.
No density of k-rational torus points is used.

Searches for an existing theorem:

- `msearch.py`, LeanFinder: “A split torus acting on a proper scheme over a field with a
  rational point has a rational scheme theoretic fixed point”. Eight hits concerned
  global sections of proper schemes, affine space, fixed fields, and Galois categories;
  none states this theorem.
- `msearch.py`, Loogle: `"fixedPoints", "Scheme"`. No hits.
- `msearch.py`, grep in Mathlib/AlgebraicGeometry:
  `split.*[Tt]orus.*fixed|[Bb]orel.*fixed`. No hits.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the node id, split-torus fixed points, and Borel
  fixed points: no exact statement. Existing flag-variety modules only cite the
  algebraically closed solvable-group result in proof plans.
- Direct rg for `splitTorus` located the existing ToriMultiplicativeType module.
  Direct source inspection of the Cartesian Mod and ModObj interfaces found the
  existing action and its algebra-point action. The existing schemeActionFixedIdeal
  is for an abstract group of automorphisms, so it is not used here.

Validation: `scompile.py Q101 lem-sfb-split-torus-rational-fixed-point` on the delivered
module succeeded in module mode, with no errors or unexpected warnings. The module
contains one theorem and one postponed proof. No statement correction, disputed statement,
new node, or dependency repair was needed.

## Second reading by Q101

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
