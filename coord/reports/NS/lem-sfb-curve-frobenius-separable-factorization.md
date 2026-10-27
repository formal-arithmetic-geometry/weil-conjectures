## Worker report

States `AlgebraicGeometry.exists_curve_frobenius_separable_factorization` in
`Sheaf.AlgebraicGeometry.Curve.FrobeniusSeparableFactorization`. There is exactly one
named theorem, with proof `sorry`, and no definitions or additional postponed lemmas.
The theorem's docstring contains all six accepted proof steps, naming their dependencies.
The natural-language statement and accepted proof split are unchanged.

The earlier worker confused NF's independently accepted stage-1 split with a stage-2
statement. The accepted node still had `lean: null`; NF's ledger entry reports two new
proof nodes, not a Lean attachment. This delivery supplies the missing statement and
preserves NF's split and review. The example CompactObject module is now withdrawn;
I read its node's current attachment and the actual upstream CompactObject module for
module/public-section/docstring conventions.

Hypotheses, matched individually:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The two schemes are `(C D : Scheme.{u})`; their displayed k-structures are
  `(sC : C ⟶ Spec (.of k))` and `(sD : D ⟶ Spec (.of k))`.
- `[IsCurve sC] [IsCurve sD]` uses the recorded curve notion: separated, finite type,
  dimension at most one. Smoothness is `[Smooth sC] [Smooth sD]`; properness is
  `[IsProper sC] [IsProper sD]`.
- Geometric integrality is `[GeometricallyIntegral sC] [GeometricallyIntegral sD]`.
  The explicit `[IsIntegral C] [IsIntegral D]` witnesses expose the integral-scheme
  function fields. They impose no additional mathematical condition:
  `GeometricallyIntegral.isIntegral_of_subsingleton sC`, respectively `sD`, gives
  these from geometric integrality over the field spectrum. The witness is a proposition
  and proof irrelevance prevents a choice of witness from altering the function field.
- Dimension exactly one is `hCdim : topologicalKrullDim C = 1` and the analogous
  `hDdim`. Thus the curve convention does not admit unwanted zero-dimensional curves.
- The map is `(u : C ⟶ D)` and its being over k is `hu : u ≫ sD = sC`.
- Nonconstant is exactly `hu_nonconstant`: there is no `y : Spec k ⟶ D` with both
  `y ≫ sD = 𝟙 _` and `sC ≫ y = u`. In particular this does not replace the source's
  definition by an assumed dominant map or a separately chosen field embedding.

Conclusions, matched individually:

- The existentially quantified `C'`, `s'`, `F`, and `v` are the intermediate scheme,
  its k-structure, and the two actual scheme morphisms. `IsCurve s'`, `Smooth s'`,
  `IsProper s'`, `GeometricallyIntegral s'` and `topologicalKrullDim C' = 1`
  give every requested property of the intermediate curve. The existential
  `IsIntegral C'` exposes its function field, with the same redundancy as on the inputs.
- `F ≫ s' = sC` and `v ≫ sD = s'` say both morphisms are over k. `F ≫ v = u`
  is precisely `u = v composed with F` in Lean's left-to-right composition notation.
- The second negated rational-point factorization says exactly that `v` is nonconstant.
- The ring homomorphism `i : D.functionField →+* C'.functionField` is required to
  satisfy
  `Spec.map i ≫ D.fromSpecStalk (genericPoint D) =
   C'.fromSpecStalk (genericPoint C') ≫ v`.
  These are the canonical generic-point morphisms from the spectra of the generic
  stalks, so this diagram specifies the embedding induced by `v`, not an unrelated
  homomorphism. A field homomorphism is injective; the generic-point morphism for an
  integral scheme is a monomorphism, so this is also the unique induced homomorphism.
  The over-k equations make this embedding compatible with k. `Module.Finite` uses
  the module associated to exactly `i.toAlgebra`; `Algebra.IsSeparable` uses exactly
  that algebra too. Thus it is the induced finite separable function-field extension.
- `CharZero k → C' = C ∧ HEq s' sC ∧ HEq F (𝟙 C) ∧ HEq v u` gives the literal
  characteristic-zero choice, not merely an isomorphic intermediate curve. `HEq`
  handles the dependent domains/codomains after `C' = C`; it is equality of those
  very maps, not an extra equivalence or a chosen abstract isomorphism.
- For every prime `p` vanishing in k (equivalently, characteristic p for a field),
  the final clause supplies `n : ℕ`, hence `n ≥ 0`. The ring map is the existing
  `iterateFrobeniusOfPrime k hp hk n`, whose actual value at a is `a ^ (p ^ n)`.
  The equality `e` makes `C'` the actual chosen pullback along `Spec` of this map.
  `s' = eqToHom e ≫ pullback.snd ...` is exactly the second-projection k-structure.
- The last equality identifies the first projection of `F` with the existing
  `C.iterateFrobenius hp hC n`. Together with `F ≫ s' = sC` and the second-projection
  equality, this characterizes the n-fold relative Frobenius by both its projections.
  This is the Stacks definition, including the affine formula: on an affine chart,
  the first projection sends a to `a^(p^n)` and the second sends b to b, so the
  tensor-product universal property forces `a tensor b` to `a^(p^n)b`. No arbitrary
  map is substituted for relative Frobenius. `hC` is merely the proof that p vanishes
  in global sections, which already follows by applying `sC.appTop` to `hk`.

Dependency interfaces read and reused:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: the recorded Mathlib match includes `IsAlgClosed`,
  in `Mathlib.FieldTheory.IsAlgClosed.Basic`; no chosen closure is needed here.
- `def-sc-curves`: `AlgebraicGeometry.IsCurve`, in
  `WeilConjectures.AlgebraicGeometry.Curve`.
- `def-pc-integral-scheme`: Mathlib `AlgebraicGeometry.IsIntegral`, in
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-pc-geometrically-irreducible`: the recorded Mathlib
  `AlgebraicGeometry.GeometricallyIntegral`, in
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` (also read its imported reduced
  and irreducible class signatures).
- `def-sc-function-field`: public import of the recorded
  `WeilConjectures.AlgebraicGeometry.FunctionField`. Its docstring explicitly assigns
  the integral-scheme specialization to Mathlib `Scheme.functionField`, the generic
  stalk, and this is what is used. The component-product definition is not copied.
  Mathlib `Scheme.fromSpecStalk` supplies the canonical maps without a new helper.
- `def-pc-field-extension`: Mathlib `Algebra`, `RingHom.toAlgebra` and its module.
- `def-pc-field-tower`: public import of the recorded
  `Sheaf.FieldTheory.FieldTower`. Its docstring assigns finite separability to
  `Module.Finite ∧ Algebra.IsSeparable`; the degree definition itself is unnecessary.
- `def-pc-base-change`: public import of the recorded
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; its note and docstring
  explicitly assign scheme base change and projections to `Limits.pullback`,
  `pullback.fst`, and `pullback.snd`. The module-base-change functor is not misused
  as a definition of a scheme pullback.
- `def-pc-field-characteristic`: the Mathlib `CharP`, `ringChar` match. Over a field,
  `CharZero` is characteristic zero, and a prime vanishing in the field is its
  characteristic (`CharP.charP_iff_prime_eq_zero`).
- Added the already recorded `def-weil-absolute-frobenius-scheme` and
  `def-weil-ring-frobenius` to `stmt_deps`. The former's existing declaration is
  `AlgebraicGeometry.Scheme.iterateFrobenius` in
  `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`; the latter's is
  `iterateFrobeniusOfPrime` in `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`.
  Both are real constructions, and both include the zero-th iterate.
- Proof-only import `Mathlib.FieldTheory.PurelyInseparable.Basic` supplies the recorded
  Mathlib match for `lem-weil-pbc-separable-first-purely-inseparable`, including
  `separableClosure.isPurelyInseparable` and the imported
  `separableClosure.isSeparable`. The other three theorem proof dependencies have
  no Lean attachments in the read node files, so there are no recorded modules of
  theirs to import. They are all named in the proof docstring. No statement interface
  required to write this item is missing.

Edge cases checked against the source before writing:

- Characteristic zero: choose literally C, sC, its identity and u; the positive-p
  implication is vacuous and the induced finite extension is separable by 030K.
- Positive characteristic with u already separable: n=0 is allowed. The power ring
  endomorphism is the identity; the pullback is canonically C and relative Frobenius
  is that canonical identity-base-change map. No `1 ≤ n` hypothesis is introduced.
- A pure Frobenius map has v an isomorphism and hence a finite separable extension
  of degree one; the identity and arbitrary isomorphisms are covered as n=0 cases.
- On the projective line, t to `t^(p^r)` has exponent r; a composition with a separable
  map has the corresponding separable second factor. No genus assumption is imposed.
- The empty scheme and dimension-zero schemes are excluded by the stated integrality
  and dimension-one hypotheses, as required. There is no extra nonemptiness assumption.
- The algebraically closed field may be transcendental over its prime field. There is
  no finite-field datum, finite-field descent, fixed closure, or bounded Frobenius power.
- The source, target, field and all test scheme constructions live in the explicit
  common universe u; no independent smaller test-algebra universe makes a clause vacuous.
- Although the positive-characteristic clause quantifies over prime p and a vanishing
  proof, characteristic uniqueness makes this exactly the one characteristic of k;
  proof irrelevance makes the power maps independent of the chosen proofs.

Searches for an existing theorem (read all returned hits):

- `msearch.py`, leanfinder, query: "Every nonconstant morphism of smooth proper curves
  over an algebraically closed field factors through iterated relative Frobenius with
  finite separable function field extension". Eight hits: Weierstrass point maps,
  `Algebra.FormallySmooth.of_perfectField`, field-level
  `IsPurelyInseparable.iterateFrobenius`, number-theoretic `functionField_iff`,
  `Scheme.RationalMap.fromFunctionField_ofFunctionField`, and properness/global-section
  lemmas. None states this curve factorization.
- `msearch.py`, loogle, initial query `frobenius, Scheme`: no hits, with unknown
  identifier Scheme. Repeated as a quoted-name search `"frobenius"`: twelve hits, all the ring-level
  Frobenius, its iterates and their formulas, or Frobenius-semilinear linear maps;
  none is a scheme/curve factorization theorem.
- `msearch.py`, grep, query `(frobenius|inseparable).*(factor|curve)|curve.*separable`:
  five categorical Frobenius-factorization hits in RegularCategory/Basic, unrelated
  to schemes or smooth proper curves.
- `rg` in project `WeilConjectures/` and `Sheaf/` for the item id, curve/separable
  factorization phrases, `relativeFrobenius`, `frobeniusTwist`, function-field maps
  and finite separability. There is no exact theorem. The finite-field framework's
  relative maps require finite-field model data, absent here. The general
  `Scheme.relativeFrobenius_finite` is a finiteness result for n≥1 and does not
  supply the curve/separable factorization or its n=0 case. Its projection
  characterization agrees with the one used here.
- `rg` for `exists_curve_frobenius_separable_factorization` across Mathlib,
  `WeilConjectures/`, `Sheaf/` and the upstream name index: no collision.
- Read Stacks `curves.tex`, Proposition unwind-morphism-smooth (0CD2), and
  `varieties.tex`, Definition relative-frobenius and Remark n-fold-relative-frobenius.
  Their pullback and relative-Frobenius conventions agree with the accepted node.

No STATEMENT-DISPUTED flag and no statement correction. There are no new nodes or
dependency repairs: only the item's Lean record and its two added, landed definition
statement dependencies change.

Validation: the prescribed `scompile.py` compiled the sandbox module and its library
path on the server, separately, in 2.4 s and 3.0 s. No errors or unexpected warnings.

Delivery dry run: `deliver2.py NS lem-sfb-curve-frobenius-separable-factorization --no-push`
returned OK: preflight and per-file compilation pass. Exactly the item node, its module,
and this report were staged. No independent second reading was performed by this worker;
the maintainer's independent review is the authorized next review.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
