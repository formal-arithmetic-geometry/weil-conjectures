## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.PurelyInseparableFrobenius` states
`AlgebraicGeometry.existsUnique_purelyInseparable_curve_frobenius`, with `sorry`.
The node's mathematical statement and all other fields are unchanged; only `lean`
is attached. There are no new definitions, helper theorems, or dependency repairs.

Source read: Stacks Project `curves.tex`, Lemma `lemma-purely-inseparable-smooth`
(Tag 0CCZ), and `varieties.tex`, Remark `remark-n-fold-relative-frobenius`
(Tag 0CCG). The former gives unique exponent and unique isomorphism; the latter
specifies exactly the pullback and its two projections. Restricting to the node's
algebraically closed base and smooth target is already part of the node.

### Hypotheses and conclusions, clause by clause

- An algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- Characteristic p greater than zero is `(p : ℕ) (hp : p.Prime)
  (hk : (p : k) = 0)`. For a field this is equivalent to characteristic p,
  because a prime p vanishing in a field must be its characteristic. Primality
  is consequently no added restriction, and implies p is at least two.
- X and Y are `(X Y : Scheme.{u})` with structure maps `sX`, `sY` to
  `Spec (.of k)`. `[IsCurve sX] [IsCurve sY]` are the dependency's exact
  separated finite-type curves with dimension at most one. Smoothness is
  `[Smooth sX] [Smooth sY]`, properness `[IsProper sX] [IsProper sY]`, and
  integrality `[IsIntegral X] [IsIntegral Y]`.
- Dimension exactly one is `hXdim : topologicalKrullDim X = 1` and the
  corresponding `hYdim`. No geometric integrality assumption is added.
- The k-morphism is `(f : X ⟶ Y) (hf : f ≫ sY = sX)`.
- The node's explicit meaning of nonconstant is `hf_nonconstant`: there is
  no `y : Spec (.of k) ⟶ Y` with `y ≫ sY = 𝟙 _` and `sX ≫ y = f`.
  Thus constant morphisms through rational points are precisely excluded.
- The finite purely inseparable induced extension is `hfield`. Its witness
  `i : Y.functionField →+* X.functionField` must satisfy
  `Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk (genericPoint Y) =
  X.fromSpecStalk (genericPoint X) ≫ f`. This is the defining generic-point
  diagram for f's induced embedding, not an independently chosen extension.
  Ring homomorphisms between these fields are injective automatically. Both
  `Module.Finite` and `IsPurelyInseparable` are evaluated at exactly
  `i.toAlgebra` (including the explicit module structure). This is equivalent
  to the node's finite purely inseparable extension by the image f^*k(Y).
  The diagram also ensures k-linearity from `hf`; no arbitrary field map can
  substitute for the induced one. This interface is the same generic-point
  formulation used by the landed Frobenius/separable factorization consumer.
- The twist for each n is the actual
  `pullback sX (Spec.map (CommRingCat.ofHom
    (iterateFrobeniusOfPrime k hp hk n)))`.
  The imported ring map `iterateFrobeniusOfPrime` is exactly a ↦ a^(p^n).
- Unique exponent and unique isomorphism together are `∃! nh : Σ n : ℕ,
  (pullback ... ≅ Y), ...`. Equality of these dependent pairs entails equality
  of exponents and, after that equality, equality of the isomorphisms.
  This avoids a nested unique-existence statement that might fail to exclude
  exponents admitting several factorizations.
- The isomorphism is over k because `nh.2.hom ≫ sY = pullback.snd ...`;
  this also fixes the twist's structure morphism to the second projection.
- The relative Frobenius witness F satisfies BOTH
  `F ≫ pullback.fst ... = X.iterateFrobenius hp hX nh.1` and
  `F ≫ pullback.snd ... = sX`. The pullback universal property determines
  F uniquely from these equations, so this is the canonical relative
  Frobenius, not an arbitrary map. The existential `hX` records the derived
  fact p vanishes in global sections: pull p=0 back along sX. It is in the
  conclusion, not an additional assumption or new data construction.
- The last clause `F ≫ nh.2.hom = f` is f = h composed with relative
  Frobenius. Composition in Lean is written in diagrammatic order.
- At n=0 the imported ring power map and `Scheme.iterateFrobenius` both
  take first powers. The twist is the pullback along the identity of Spec k;
  its canonical identification with X takes F to the identity. This follows
  from the displayed projection equations, including at n=0, without a
  separate choice of identification or a positivity restriction on n.
- The imported absolute Frobenius is identity on points and sends every local
  section to its p^n-th power, as required by the final descriptive clause.

### Dependencies and declaration reading

Read every node in `stmt_deps`, including its `lean` record or `mathlib_match`,
and opened its indicated interface and docstrings. Used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed`, in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`. This node explicitly records that
  predicate for the algebraically closed-field clause; an algebraic closure
  object `AlgebraicClosure k` is not needed here.
- `def-pc-field-characteristic`: Mathlib `CharP` / `ringChar`, in
  `Mathlib.Algebra.CharP.Defs`; the equivalent prime-and-vanishing presentation
  feeds the existing absolute power Frobenius directly.
- `def-sc-curves`: `AlgebraicGeometry.IsCurve`, module
  `WeilConjectures.AlgebraicGeometry.Curve`, including its full inherited
  separatedness, locally finite type, quasi-compactness, and dimension bound.
- `def-pc-integral-scheme`: Mathlib `AlgebraicGeometry.IsIntegral`, module
  `Mathlib.AlgebraicGeometry.Properties`, with its nonempty/domain conditions.
- `def-sc-function-field`: `WeilConjectures.AlgebraicGeometry.FunctionField`,
  whose node record explicitly reuses Mathlib `Scheme.functionField` for an
  integral scheme, its stalk at `genericPoint`, and the field instance. The
  product `Scheme.functionFieldOfComponents` applies to nonintegral curves;
  taking it again here would obscure the exact integral-scheme clause.
- `def-pc-field-extension`: Mathlib `Algebra`, module
  `Mathlib.Algebra.Algebra.Defs`; `i.toAlgebra` supplies the induced extension.
- `def-pc-field-tower`: module `Sheaf.FieldTheory.FieldTower`, whose docstring
  records the pre-existing Mathlib `Module.Finite` and `IsPurelyInseparable`
  for finiteness and pure inseparability. `FieldExtension.degree` is not
  needed, since the item does not assert a numerical degree.
- `def-pc-base-change`: module
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, whose docstring
  specifies `pullback`, `pullback.fst` and `pullback.snd` as the base-change
  scheme and its projections. Its module-sheaf base-change functor is not the
  scheme-level object and is not substituted for it.
- `def-weil-absolute-frobenius-scheme`: `Scheme.iterateFrobenius`, module
  `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`; opened its data
  construction and `iterateFrobenius_apply` / `iterateFrobenius_app_apply`.

Proof imports are `WeilConjectures.FieldTheory.PurelyInseparablePthRootTower`
(`IsPurelyInseparable.exists_pth_root_tower`, signature and docstring read), and
`Mathlib.LinearAlgebra.Dimension.Free` (`Module.finrank_mul_finrank`).
Other proof dependencies share the public definition imports, or have no
recorded Lean declaration in the read DAG: proper-curve-function-field-morphisms,
algclosed-curve-model, and smooth-curve-relative-frobenius-degree. They remain
named in the full six-step proof docstring for subsequent proof work. They are
not hypotheses of the statement and require no new statement interface here.

### Edge cases

Checked n=0, f an isomorphism, degree one / empty root tower, positive iterates
of Frobenius on the projective line, and possible automorphisms of Y. An
isomorphism is represented by n=0; the projection formulas impose no n>0
restriction. For a nontrivial iterate the function-field degree is p^n, so two
exponents cannot qualify. Once the exponent is fixed, surjectivity of the
relative Frobenius (or injectivity on function fields) excludes distinct
postcomposed automorphisms. Empty and dimension-zero schemes are excluded
exactly by the node's integrality and dimension-one hypotheses, not by any
new constraint. No genus restriction is present. All universes and binders are
explicit, with `autoImplicit false`; k and both schemes use the same standard
scheme universe, as in the existing curve interface.

### Searches

- `msearch.py ... leanfinder`: “A purely inseparable nonconstant morphism of
  smooth proper integral curves over an algebraically closed field is uniquely
  an iterated relative Frobenius followed by an isomorphism.” Eight hits on
  field Frobenius/exponents and uniqueness of algebra embeddings, no curve theorem.
- `msearch.py ... loogle`: `"frobenius", "Scheme"`: zero hits.
- `msearch.py ... grep`: `purely.?inseparable.*curve|curve.*purely.?inseparable|
  frobenius.*twist|twist.*frobenius`, in Mathlib `AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch`: “Unique relative Frobenius factorization of a
  purely inseparable morphism between smooth proper curves.” Eight hits on
  separable polynomials and purely inseparable fields, no curve theorem.
- `rg` of the node ID in `lean/WeilConjectures` and `lean/Sheaf`: only the
  proof-plan citation in `Curve/FrobeniusSeparableFactorization.lean`.
- `rg` of purely inseparable curve / curve purely inseparable patterns in both
  libraries: generic-model preparation results, not this classification.
- Broader Frobenius/twist search in both libraries found finite-field geometric
  fibers and coefficient twists; neither has this arbitrary-base-field twist
  classification or unique exponent and unique isomorphism.
- The new declaration's full name was searched in Mathlib, both project source
  roots, and `dag/lean_names_upstream.json`: no existing declaration.

No statement dispute or mathematical correction was found. The preceding
worker's rejection concerned an already stage-1-split node; that metadata is
preserved verbatim in this stage-2 Lean attachment.

### Validation

`scompile.py NR lem-sfb-purely-inseparable-curve-frobenius` compiled the module
on the live server as both sandbox and library module, with no errors or warnings
(7.2 s and 3.2 s respectively). No local or global build was run.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
