## Worker report

The module `Sheaf.AlgebraicGeometry.SpecialLinearPicardZero` states
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_specialLinear`, with its sole
proof `sorry`. It states the sheaf formulation of Picard vanishing, exactly the
first conclusion of the node. No definitions or axioms are introduced.

Hypothesis and conclusion correspondence:

- A field k: `(k : Type u) [Field k]`, using Mathlib's field class; it includes
  nontriviality. No algebraic closure or characteristic hypothesis occurs.
- An integer n >= 1: `(n : ℕ) (hn : 1 ≤ n)`. The theorem includes n = 1.
- The polynomial quotient A = k[x_ij]/(det(x_ij)-1) and X = Spec A:
  `(LinearGroupSchemes.specialLinear k n).left`. Reading the actual definitions,
  `specialLinear` is `StandardGroupSchemes.affine k (SpecialAlgebra k n)`;
  `SpecialAlgebra` is the quotient of `MvPolynomial (Index n × Index n) k` by
  `specialIdeal k n`, which is `Ideal.span {genericMatrix.det - 1}`.
  `Index n = ULift (Fin n)`, a bijective relabeling of the n row and column
  indices. The underlying `affine` scheme is the ordinary affine spectrum.
  This uses the landed notion directly, without a second quotient definition.
- Every invertible O_X-module: the arbitrary binder
  `(L : (LinearGroupSchemes.specialLinear k n).left.Modules) [L.IsInvertible]`.
  The recorded upstream `IsInvertible` says that every point has a Zariski-open
  neighborhood on which the pullback of L is isomorphic to the unit module.
- It is isomorphic to O_X:
  `Nonempty (L ≅ Scheme.Modules.unit (LinearGroupSchemes.specialLinear k n).left)`.
  This is an O_X-linear sheaf isomorphism, not just a stalk or global-section map.
  `Scheme.Modules.unit` is precisely `SheafOfModules.unit X.ringCatSheaf`.
- The equivalent Pic(X) = 0 sentence is expressed by this very assertion:
  every isomorphism class equals the class of O_X, the tensor unit. It does not
  replace sheaf Picard vanishing with the abstract matrix group's triviality or
  with the ring Picard group without a comparison.

Statement dependency declarations read and used:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-weil-pbc-matrix-determinant`: `Matrix.det` in
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`; `det_apply` is its Leibniz formula.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible` in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`, `MvPolynomial.algHom_ext` in
  `Mathlib.Algebra.MvPolynomial.Basic`, and `MvPolynomial.aeval` in `.Eval`.
- `def-weil-pbc-algebra-hom-quotient`: `AlgHom` in `Mathlib.Algebra.Algebra.Hom`,
  `Ideal.Quotient.algebra` and `Ideal.Quotient.mkₐ` in
  `Mathlib.RingTheory.Ideal.Quotient.Operations`.
- Added landed dependency `def-sc-general-linear-group`: `LinearGroupSchemes.specialLinear`,
  `SpecialAlgebra`, `specialIdeal`, `Index` in `Sheaf.AlgebraicGeometry.LinearGroupSchemes`.
  This dependency addition records reuse of the exact existing scheme. The statement,
  proof, and proof dependencies are unchanged; this is not a statement correction.

Proof dependencies are imported privately: `Mathlib.AlgebraicGeometry.AffineScheme`
and `.ResidueField` for the basic-open localization statements;
`Mathlib.GroupTheory.MonoidLocalization.Away` and
`Mathlib.RingTheory.Localization.Defs` for localization and its universal property;
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` for the recorded tensor
pullback interface; and `Sheaf.AlgebraicGeometry.AffineSpaceOpenInvertibleTrivial`
for `nonempty_iso_unit_of_open_mvPolynomial_field`. The declaration docstring gives
all four node proof steps, including the actual coordinate retraction and the
local tensor trivializations.

Source and edge cases:

Read Milne, Algebraic Groups (2017), PDF pp.429-430 (printed pp.417-418),
Proposition 20.30, and PDF p.65 (printed p.53), 2.42. Proposition 20.30 asserts
Pic(SL_n) = Pic(GL_n) = 0, and uses the scheme decomposition in 2.42. Also read
the latest blueprint's `sec-smooth-purity/sk-prop-an/def-sc-general-linear-group.md`.
For n = 1 the quotient is k[x]/(x-1), so X is Spec k and every line bundle is
trivial. For n = 2, including characteristic 2, the determinant equation and
first-column division use no prohibited denominator: only det is inverted on G.
No restriction excludes finite fields or imperfect fields. The positivity binder
excludes n = 0 exactly as the node does. The field universe is arbitrary and
ULift of the finite index set does not restrict k or the rank.

Searches for an existing statement (all prescribed searches run before writing):

- `msearch.py leanfinder`, query "Every invertible sheaf on the special linear
  determinant one matrix scheme over a field is trivial": 8 hits, including
  `CommRing.Pic.mk_eq_one`, `CommRing.Pic.subsingleton_iff`, and abstract
  `SpecialLinearGroup` facts. None states this scheme/sheaf theorem.
- `msearch.py loogle`, query "Matrix.det, MvPolynomial, Ideal.Quotient": 0 hits;
  the service reports unknown identifier `Ideal.Quotient`. This search is
  inconclusive; the direct quotient source was read instead.
- `msearch.py grep`, query `Pic.*SpecialLinear|SpecialLinear.*Pic|iso_unit.*specialLinear`:
  0 hits.
- `msearch.py leansearch`, query "Every line bundle on the special linear
  algebraic group scheme over a field is trivial": 8 hits about abstract
  matrix/special-linear groups, not sheaf Picard vanishing.
- `rg` over the project's `lean/WeilConjectures` and `lean/Sheaf` for special-linear
  and Picard names, plus the exact node id in `lean/WeilConjectures`: no existing
  theorem. The search located `LinearGroupSchemes.lean`, whose exact coordinate
  scheme is reused here, and `AffineSpaceOpenInvertibleTrivial.lean`, whose
  recorded theorem is a proof dependency.
- `rg` of `dag/lean_names_upstream.json` for the corresponding Picard/special-linear
  patterns found no existing statement. The new declaration name has no match.

No statement dispute, dependency repair, or new node is needed.

## Second reading by Q51

Reread the node, source, dependency declarations, and finished module after writing.
This is the dispatcher's single worker's second pass, not a claim of another
independent agent's review; the maintainer supplies the independent review.
The field and positivity binders exactly match the hypotheses. Unfolding the
existing specialLinear/affine/SpecialAlgebra/specialIdeal definitions gives the
specified determinant-one quotient spectrum. The arbitrary sheaf binder and
IsInvertible instance quantify over all line bundles, and the conclusion is an
actual sheaf isomorphism to its structure module. The equivalent Picard sentence
adds no independent condition. All four natural-language proof steps appear in
the docstring. No mismatches were found and no statement correction was made.
