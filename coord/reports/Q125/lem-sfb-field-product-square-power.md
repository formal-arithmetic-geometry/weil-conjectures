## Worker report

The module `Sheaf.AlgebraicGeometry.FieldProductSquarePower` states
`AlgebraicGeometry.Scheme.Modules.exists_fieldProductSquare_tensorPower`.
Its only theorem has proof `sorry`. No new definition, auxiliary theorem,
dependency repair, or statement correction is needed. The products, coordinate
maps and square difference are explicit local let expressions in the signature.
There is no choice of an unspecified map or module.

The source was opened online at
https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf :
Guo, March 31, 2026 version, Section 5.1 (square-difference definition),
Proposition 5.2(ii), Claim 5.2.1 and the norm descent paragraph, printed pp.11–12.
The node is its stated smooth separated finite-presentation field specialization.
The declaration docstring reproduces the node's three proof steps.

Hypotheses and clauses, matched individually:

- A field `k`: `(k : Type u) [Field k]`. The base is exactly
  `Spec (CommRingCat.of k)`.
- Each scheme and its morphism to the base: `X₁ X₂ X₃ : Over (Spec ...)`;
  `.left` is the scheme and `.hom` is its structure morphism. These are
  arbitrary objects of the over category, with no extra chosen section.
- Smoothness: `[Smooth X₁.hom]`, `[Smooth X₂.hom]`, `[Smooth X₃.hom]`.
- Separatedness (closed-immersion diagonal): `[IsSeparated X₁.hom]`,
  `[IsSeparated X₂.hom]`, `[IsSeparated X₃.hom]`.
- Finite presentation: the three `LocallyOfFinitePresentation` instances and
  the three `QuasiCompact` instances. Quasi-separatedness, the remaining
  finite-presentation condition in the dependency's statement, follows from
  each `IsSeparated` instance; it is not silently omitted or replaced by
  mere local finite presentation.
- Integral after every field extension: the three
  `[GeometricallyIntegral Xᵢ.hom]` instances, using the recorded Mathlib notion.
- `C = X₁ ×_k X₂ ×_k X₃`: `let C := (X₁ ⨯ X₂) ⨯ X₃` in the over category.
- `P = X₁ ×_k X₁ ×_k X₂ ×_k X₂`:
  `let P := (X₁ ⨯ X₁) ⨯ (X₂ ⨯ X₂)`.
- The domain `P ×_k X₃`: `let Q := P ⨯ X₃`. The projection `pi` is
  `(prod.fst : Q ⟶ P).left`.
- The coordinate maps `r_ab`: `x false`, `x true` select the first and
  second `X₁` coordinates; `y false`, `y true` do the same for `X₂`.
  The nested `prod.lift` in `r a b` pairs these with the unchanged final
  `prod.snd : Q ⟶ X₃`. Thus `false/true` represent `0/1`, respectively.
- The square difference `D(M)` has exactly the ordered factors
  `r00^* M`, `r11^* M`, `dual (r01^* M)`, `dual (r10^* M)`.
  Every inverse image is `Scheme.Modules.tensorPullback`, every tensor is
  the existing monoidal sheaf tensor, and `dual` is internal Hom into `O_Q`.
- Every invertible module `A` on `C`:
  `∀ (A : C.left.Modules), A.IsInvertible → ...`.
- There is an integer `n ≥ 1`: `∃ (n : ℕ), 1 ≤ n ∧ ...` is precisely a
  positive integer, since there are no negative integers satisfying this
  bound. Tensor powers use the recorded `A.tensorPow n`.
- An invertible `N` on `P`: `∃ (N : P.left.Modules), N.IsInvertible ∧ ...`.
- The asserted isomorphism: `Nonempty (D (A.tensorPow n) ≅
  (tensorPullback (prod.fst : Q ⟶ P).left).obj N)` in `Q.left.Modules`.
  This asserts an actual module isomorphism, not only a cohomological
  identity or a numerical equality of invariants.

Dependency declarations read and used (including full signatures and docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, used throughout (reexported by the geometric imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`; together with
  `AlgebraicGeometry.QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`:
  `AlgebraicGeometry.IsSeparated`; its `QuasiSeparated` instance supplies
  the third finite-presentation condition.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`:
  `AlgebraicGeometry.GeometricallyIntegral`, which quantifies over field
  extensions through the geometric-fibre predicate.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
  These occur through the existing over-category product construction:
  `Mathlib.CategoryTheory.Limits.Constructions.Over.Products` identifies
  `(Y ⨯ Z).left` with `pullback Y.hom Z.hom` via
  `CategoryTheory.Over.prodLeftIsoPullback`, compatibly with projections.
  The imported `Over.Basic` gives the over-category finite-limit instance;
  `Mathlib.AlgebraicGeometry.Limits` gives finite limits of schemes.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` and `tensorPow`.
  Imported publicly through `WeilConjectures.AlgebraicGeometry.Modules.Dual`,
  whose `AlgebraicGeometry.Scheme.Modules.dual` is the recorded dual notion.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  its publicly imported `AlgebraicGeometry.Scheme.Modules.tensorPullback`
  from `WeilConjectures.AlgebraicGeometry.TensorPullback`. Its explicit
  sectionwise inverse-image/change-of-rings construction was read.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the recorded tensor dependency,
  imported with the existing sheaf tensor construction it reexports.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, used internally in the existing
  geometric-integrality notion of field extension. No extension is selected
  or added as a hypothesis of this field-case conclusion.

Neither proof dependency has a Lean record in the read repository:
`lem-sfb-field-square-after-finite-extension` and
`lem-sfb-finite-field-picard-norm-base-change`. They are named in the proof
plan but have no module to import. They are not needed to type this statement.

Edge cases checked before writing:

- `n = 0` must be excluded; the explicit bound `1 ≤ n` does so. `n = 1`
  remains available, with no divisibility or characteristic restriction.
- If `X₃ = Spec k`, `pi` is an isomorphism; the conclusion permits the
  square difference itself as the descended module.
- If `X₁` or `X₂` is the point, the opposite-sign coordinate factors cancel;
  the formula gives a trivial square difference as expected.
- If `A = O_C`, all four factors and their duals give `O_Q`.
- An empty scheme is not geometrically integral, hence excluded by the
  node itself, not by an extra nonemptiness or surjectivity assumption.
- No properness, rational points, algebraic closedness, perfectness,
  separability or characteristic hypothesis is imposed. The norm argument
  is valid for inseparable extensions as well.
- All universes and binders are explicit, with auto-implicit binding
  disabled. Arbitrary field and scheme size is represented by universe `u`.

Searches (2026-10-24):

1. `msearch.py ... leanfinder` with query “On three smooth geometrically
   integral schemes over a field a positive tensor power of a line bundle
   has square difference pulled back from the parameter base”: eight
   `Scheme.Pullback.Triplet` hits about tensor products of residue fields;
   none is a line-bundle square theorem.
2. `msearch.py ... loogle '"IsInvertible", "pullback"'`: two vector-field
   pullback hits, neither about invertible module sheaves.
3. `msearch.py ... grep 'squareDifference|square_difference|theorem.of.the.square'
   AlgebraicGeometry`: zero Mathlib hits.
4. `msearch.py ... leansearch` with query “A line bundle on three smooth
   geometrically integral varieties has a positive tensor power with square
   difference pulled back from the first two doubled factors”: eight tensor
   algebra and pullback-carrier hits, none the claimed geometric theorem.
5. `rg` for `squareDifference|square_difference|field_product_square|productSquare|
   squarePower|SquareDifference` in the project's `lean/WeilConjectures` and
   `lean/Sheaf`: only unrelated Cartesian-square constructions in
   `ProductOpenTensorProjection` and `EtaleGraphProductInterchange`.
6. `rg 'lem-sfb-field-product-square-power' lean/WeilConjectures`: zero hits.
   `rg` for the chosen theorem name in `dag/lean_names_upstream.json`,
   `lean/WeilConjectures`, `lean/Sheaf`: zero hits.

No statement fault or STATEMENT-DISPUTED issue was found. Only the `lean`
field of the copied item node changes, preserving indent 1 and final newline.

Validation: prescribed `scompile.py Q125 lem-sfb-field-product-square-power`
compiled both the sandbox module (8.8 seconds) and the final library module
(9.0 seconds), with no errors or unexpected warnings. The prescribed
`deliver2.py --no-push` then printed OK: preflight and compilation pass.

## Second reading by Q125

I reopened the node and the completed module for a separate second pass.
This was a self-review because the dispatch brief forbids starting agents;
I do not claim an independent worker performed it. The maintainer performs
an independent review of the delivery.

I checked each of the three smooth, separated, finite-presentation and
geometric-integrality assumptions, the field base, all three product
parenthesizations, all four coordinate selections, the ordered signs,
and the quantifiers over `A`, positive `n`, and invertible `N`. The over
category products are the same fibre-product notion, up to the existing
canonical projection-compatible isomorphism, so the different grouping of
`P` changes no scheme-theoretic data. In particular `r false true` selects
`x₀,y₁,z`, and `r true false` selects `x₁,y₀,z`, and precisely these two
pullbacks are dualized. `D` is evaluated at `A.tensorPow n`, as required,
rather than only asserting a formula for a different tensor-power object.
The final arrow is the first projection from `Q` and the pullback is the
prescribed tensor pullback. No mismatch or code change was found in this pass.
