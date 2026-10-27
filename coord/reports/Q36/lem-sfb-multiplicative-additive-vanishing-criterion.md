## Worker report

The module `Sheaf.AlgebraicGeometry.MultiplicativeAdditiveVanishingCriterion` states
`AlgebraicGeometry.diagonalizable_iff_commutative_and_additive_hom_zero` with one
`sorry` proof. It introduces no definition and proves nothing. I read Milne,
Algebraic Groups (2017), printed pp.233–234 (Definition 12.7 and Theorems 12.8–12.9)
and pp.237–238 (Theorem 12.18 and its complete proof). The theorem is precisely
12.18(b) iff 12.18(d) over an algebraically closed field, with the finite-generation
convention of 12.9(a). The declaration docstring records all eight DAG proof steps.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- An algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
  There is no characteristic assumption.
- An F-group scheme G is `(G : Over (Spec (.of F))) [GrpObj G]`. This is exactly
  the interface recorded on `def-sc-group-scheme`, including its existing group law.
- Affineness is `[IsAffine G.left]`.
- Finite type is `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, exactly
  the conjunction recorded on `def-weil-finite-type-morphism`.
- The additive group is `StandardGroupSchemes.additive F`, with its recorded
  instance `StandardGroupSchemes.additiveGroup`. Its coordinates are F[y], its
  coproduct is y ⊗ 1 + 1 ⊗ y, and its counit is evaluation at zero.
- “Diagonalizable” is the left side of the equivalence:
  `∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
  Nonempty (Grp.mk G ≅ diagonalizableGroup F M)`.
  `AddGroup.FG` means finite generation as a group, allowing torsion. The isomorphism
  is in `Grp (Over (Spec (.of F)))`, hence preserves the group law and the base.
  The existing `diagonalizableGroup F M` is the spectrum of `AddMonoidAlgebra F M`
  with the canonical Hopf structure e_m ↦ e_m ⊗ e_m, not just an isomorphic scheme
  or a group with unspecified operations.
- “If and only if” is `↔`.
- Commutativity is `IsCommMonObj G` as a conjunct on the right, not a hypothesis
  that would incorrectly restrict the forward implication.
- “Every homomorphism G → G_a” is
  `∀ (f : G ⟶ StandardGroupSchemes.additive F), IsMonHom f → ...`.
  The ambient morphisms are F-scheme morphisms; `IsMonHom` imposes preservation
  of multiplication and identity, and group inverses are then preserved.
- The zero conclusion is
  `f = toUnit G ≫ MonObj.one (X := StandardGroupSchemes.additive F)`.
  `toUnit` goes to the terminal F-scheme and `MonObj.one` is the identity section
  of this group object, which is the additive coordinate zero. This is equality of
  scheme morphisms, so it detects behavior on nonreduced test algebras as required.
- No smoothness, reducedness, connectedness, finiteness of the group scheme,
  or finite-dimensionality of its coordinate algebra is imposed.

Dependency interfaces read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, lines 169–180.
- `def-weil-algebraic-closure`: its recorded `IsAlgClosed` component,
  Mathlib.FieldTheory.IsAlgClosed.Basic, lines 59–64; the statement requires an
  algebraically closed base, not a chosen algebraic closure of some further field.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and `Grp`,
  Mathlib.CategoryTheory.Monoidal.Grp, lines 42–46 and 85–94;
  `CategoryTheory.IsMonHom` and `IsCommMonObj`, Mathlib.CategoryTheory.Monoidal.Mon,
  lines 211–215 and 1220–1223. I also read the group's explicit scheme specialization
  in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, lines 38–47, and
  `AlgebraicGeometry.QuasiCompact`, Morphisms.QuasiCompact, lines 38–46.
- `def-sc-gm-ga`: `AlgebraicGeometry.StandardGroupSchemes.additive`,
  `additiveComul`, `additiveCounit`, `additiveAntipode`, and `additiveGroup`,
  Sheaf.AlgebraicGeometry.StandardGroupSchemes, lines 96–112 and 154–157.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme, lines 469–480, used through the spectrum-based
  group constructions.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  Mathlib.LinearAlgebra.TensorProduct.Defs, lines 77–83, used by the existing
  group-algebra Hopf structure; no replacement tensor notion is introduced.
- The already landed `def-sfb-diagonalizable-group` supplies
  `AlgebraicGeometry.diagonalizableGroup`, Sheaf.AlgebraicGeometry.DiagonalizableGroup,
  lines 22–28. I read its complete definition and docstring. The item's stmt_deps
  gains this landed node under brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES).
  The informal statement and proof are unchanged.
- Finite generation uses `AddGroup.FG`, Mathlib.GroupTheory.Finiteness, lines 398–401.
  The zero map uses `CartesianMonoidalCategory.toUnit` and `MonObj.one`; the formula
  is the same one documented by `MonObj.Hom.one_def`,
  Mathlib.CategoryTheory.Monoidal.Cartesian.Mon, line 237.

Statement modules are public imports. Stated proof dependencies are available through
Mathlib.AlgebraicGeometry.Group.Affine (via the public group constructions), and plain
imports Mathlib.LinearAlgebra.Basis.VectorSpace, Mathlib.LinearAlgebra.FreeModule.Basic,
Mathlib.RingTheory.Coalgebra.GroupLike, Mathlib.RingTheory.TensorProduct.Maps, and
Mathlib.RingTheory.FiniteType. The affine locally-finite-type dictionary is already
public through Morphisms.FiniteType. The proof dependencies
`lem-sfb-comodule-finite-subrepresentation` and
`lem-sfb-finite-algebra-split-or-dual-quotient` have neither a Lean record nor a
Mathlib match in the read repository; no import for either exists. They are proof
inputs only and are recorded by name in the proof docstring, without supplying
unrequested statements for those nodes.

Edge cases checked before writing:

- The trivial group is D_F(0), with zero character group allowed; every map is zero.
  The character group is a genuine group and therefore never an empty type.
- In characteristic p, μ_p is D_F(Z/p) and is included although it is nonreduced.
  Its primitives vanish by the coefficient comparison; finite-generation imposes
  no torsion-free or prime-to-characteristic restriction.
- G_a and α_p have their nonzero identity/inclusion map to G_a, so the vanishing
  conjunct fails; testing just geometric points would miss α_p, but the statement
  uses actual scheme morphisms.
- The constant group Z/p in characteristic p has a nonzero map to G_a; a constant
  finite group of order prime to the characteristic over F is diagonalizable.
- Noncommutative groups are rejected by the explicit commutativity conjunct even
  if their additive homomorphisms all vanish.
- No zero coordinate algebra or empty scheme can accidentally be an F-group scheme:
  the group identity is a section from the nonempty Spec F.
- All universes are explicit, and `autoImplicit` is false. G is an arbitrary scheme
  in the same universe as its base. A finitely generated abelian character group
  admits a model in Type u (a quotient of a finite power of integers, lifted to u),
  so its existential universe loses no diagonalizable presentation. This is the
  existing diagonalizableGroup API and the same convention as its landed consumers.
- The forward primitive calculation c_0 = 2c_0 implies c_0 = 0 even in
  characteristic 2; no division by 2 is used.

Searches actually run:

- `msearch.py ... leanfinder` with query
  “A commutative affine algebraic group over an algebraically closed field is
  diagonalizable if and only if every homomorphism to the additive group is zero”:
  eight hits, including HasAffineProperty.diagonal_iff and other scheme-diagonal
  properties, LieModule.instIsTriangularizableOfIsAlgClosed, Rep.diagonalHomEquiv_apply,
  and RootPairing.GeckConstruction.instHasTrivialRadical; no criterion match.
- `msearch.py ... loogle` query `"GrpObj", "IsCommMonObj", "IsMonHom"`:
  successful search, zero hits.
- `msearch.py ... grep` query `diagonaliz|diagonalis|multiplicative.?type|primitive`
  restricted to AlgebraicGeometry/Group: successful search, zero hits.
- `msearch.py ... leansearch` with query
  “An affine finite type group scheme over an algebraically closed field is
  diagonalizable if and only if it is commutative and every group scheme
  homomorphism to the additive group is zero”: eight affine-scheme/finite-morphism
  results, no criterion match.
- `rg` for diagonalizability and the item id in lean/Sheaf and lean/WeilConjectures
  found the existing DiagonalizableGroup construction and landed consumers,
  especially CommutativeMultiplicativeTypeExtension, but no statement of this criterion.
  `grep -rn` for the exact item id in lean/WeilConjectures returned no hit.
- `rg` for the chosen full declaration name in Mathlib/AlgebraicGeometry,
  lean/Sheaf, lean/WeilConjectures and dag/lean_names_upstream.json found no duplicate.
- The existing DAG node `def-sfb-diagonalizable-group` and its complete record were
  read before adding it to stmt_deps. No new notion or node is needed.

Validation: scompile.py compiled both the sandbox module and the actual library module
against the published server build, in 1.6 s and 2.1 s respectively, with no errors or
unexpected warnings. No statement fault, source correction, or disputed statement was found.

## Second reading by Q36

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
