## Worker report

The delivery states `DerivedCategory.perfect_algebra_coinduction_tensor` in
`Sheaf.Algebra.Homology.PerfectAlgebraCoinductionTensor`. Its only postponed proof is
this named theorem, with the seven-step DAG proof in its docstring. The two small API
helpers have real data: `ModuleCat.coinductionComplex` abbreviates termwise application
of the existing `ModuleCat.coextendScalars`; `ModuleCat.coextendScalars_additive` installs
the existing generic theorem that a zero-preserving, binary-product-preserving functor
is additive. No mathematical statement, dependency, or proof plan was changed.

Hypotheses and conclusions, clause by clause:

- Commutative rings and the homomorphism are `{R B : Type u} [CommRing R] [CommRing B]`
  and `(f : R →+* B)`. A common universe contains any pair of coefficient rings;
  localization universes `wR` and `wB` remain independent and explicit.
- The ordinary unbounded categories are `DerivedCategory (ModuleCat.{u} R)` and
  `DerivedCategory (ModuleCat.{u} B)`, with their `HasDerivedCategory` binders.
- Perfectness of the underlying R-module B placed in degree zero is precisely `hB`,
  using the recorded `DerivedCategory.IsPerfectRingComplex`, applied to
  `(singleFunctor (ModuleCat R) 0).obj ((restrictScalars f).obj (ModuleCat.of B B))`.
  The recorded definition says bounded finite projective representative, with no
  Noetherian or flatness hypothesis.
- Coinduction is the existing `(ModuleCat.coextendScalars f).rightDerivedFunctor`.
  `ModuleCat.coextendScalars` has carrier `B →ₗ[R] M` and the exact action
  `(b • h)(b') = h (b' * b)`, read in ChangeOfRings.lean:520–555. Its termwise
  application is `coinductionComplex f J`. Thus it is Hom from B[0], not a
  different internal Hom or a chosen B-action.
- The auxiliary parameters `J [J.IsKInjective]` and `η : R[0] ⟶ J [QuasiIso η]`
  select any computing resolution of R[0]. They impose no extra mathematical
  assumption: K-injective resolutions exist for ModuleCat by the upstream
  Grothendieck/K-injective-resolution instances. The statement works for every
  such resolution, rather than choosing data from an unproved existence theorem.
  The cochain tensor unit in the type of η is R[0].
- `V = coinductionComplex f J` represents the exact object D_B = C_B(R[0]): apply
  coinduction to Qη and then `Functor.rightDerivedFunctorObjQIso J`. This API is
  read in upstream RightDerivedFunctor/KInjective.lean:47. No arbitrary object of
  D(B) is supplied instead of D_B.
- Tensor with the B-complex V is the existential `L` together with `ε`, its
  `IsLeftDerivedFunctor` universal property for the existing total mixed tensor,
  and the clause `IsIso (ε.app F)` for every K-flat F. This is exactly the interface
  of `exists_derivedTensor_second_factor_functor`; its totalization order is (F,V)
  and its B-action comes from V. L is not an unconstrained functor parameter.
- `∃ θ : L ≅ (ModuleCat.coextendScalars f).rightDerivedFunctor` is the required
  natural isomorphism in D(B), for every object of the whole unbounded D(R).
- The canonical evaluation comparison is specified by the final two clauses,
  for every K-flat complex F. The isomorphism s is fixed by
  `s.hom = Q.map (ρ_ F).inv ≫ Q.map (F ◁ η)`. K-flatness makes this map invertible.
  The chain map e is fixed on every coproduct generator by
  `e(ι(h ⊗ (b ⊗ x))) = ι(x ⊗ h(b))`. At b=1 this is tensoring with evaluation at
  one. The extra b handles the actual `V ⊗_B (B ⊗_R F)` presentation of the mixed
  module tensor and ensures the formula determines the map, including balancing.
- The last equation says that the scalar restriction of θ followed by the actual
  upstream adjunction counit equals `U(ε_F)` followed by the canonical restriction
  factorization, Qe, and s inverse. It therefore says precisely that θ is the
  adjunct of tensoring K with the evaluation counit D_B → R[0]. Naturality is
  part of θ itself. Since the adjunct is fixed on all K-flat representatives,
  the morphism is uniquely normalized, rather than just an arbitrary natural
  isomorphism of the two functors.
- The final scalar-restriction clause of the node is rendered by the same
  evaluation-generator formula and adjunct equation: the adjunction curries
  `x ⊗ h(1)` to `b ↦ x ⊗ h(b)`. Forgetting B-linearity is exactly ordinary
  perfect-complex evaluation. No separate unnormalized RHom isomorphism is assumed.
- There is no boundedness predicate on F or on the inputs of L, no flatness
  predicate on B/R, and no Noetherian hypothesis.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and `singleFunctor` (the node
  def-weil-abstract-derived-category).
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex` (def-pc-perfect-ring-complex).
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`:
  `DerivedCategory.exists_derivedTensor_second_factor_functor` and its imported
  `ModuleCat.mixedTensor` (lem-pc-derived-tensor-second-factor-functor).
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` and its K-injective model are
  imported as the recorded ringed-site RHom interface. The node expressly permits
  ordinary ModuleCat as an alternative to the one-object-site encoding. Here the
  ordinary Hom from B[0] is implemented directly by the already existing right
  derived coextension, so no second general derived internal Hom is constructed.
- Upstream `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`:
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`, applied to the exact
  ordinary `ModuleCat.restrictCoextendScalarsAdj f`. This supplies an actual
  derived adjunction, not a Nonempty or a new postponed theorem. Although the
  proof dependency lem-trf-derived-coinduction-adjunction has no Lean record,
  the needed construction already exists through this usable upstream API;
  the main statement can therefore use it directly without adding a duplicate
  dependency module or asking to wait for a record.
- Upstream `RightDerivedFunctor.KInjective`: `Functor.rightDerivedFunctorObjQIso`;
  `GrothendieckAbelian.KInjectiveResolution` and ModuleCat.AB supply unbounded
  resolutions. `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact` supplies
  exactness of restriction. `Functor.mapDerivedCategoryFactors` identifies its
  value on complexes in the normalization equation.

All available recorded proof modules are imported without `public`: K-flat
resolutions, signed perfect tensor-dual degrees and differential, projective Hom
evaluation model, and quasi-isomorphism invariance of Hom. The two Mathlib proof
leaves are imported through DerivedCategory.KProjective and HomologySequence.
The unstated coinduction lemma is not imported as a nonexistent module; its actual
upstream adjunction construction is used in the statement as explained above.

Edge cases checked: identity ring map (ordinary evaluation/unit comparison);
zero ring B (both B-valued functors are zero); arbitrary characteristic; perfect
but nonflat quotient, for example Z → Z/2 (allowed); zero F; and complexes F
unbounded in either direction. In each total degree the formula specifies every
(p,q) summand with p+q=n. It uses direct-sum inclusions, not a finite-support or
boundedness condition on F. Arbitrary choices of J and η are retained. There is
no discarded identity-map case or localization-universe equality.

Searches actually run:

- msearch.py leanfinder, query `Perfect algebra derived coinduction is tensor with
  its derived dual`: 8 cotangent/Kaehler-related hits, no derived-coinduction formula.
- msearch.py loogle, query `ModuleCat.restrictCoextendScalarsAdj`: one ordinary
  adjunction hit. Read the full definition and counit in ChangeOfRings.lean:520–680;
  it is the building block used here, not the perfect derived tensor theorem.
- msearch.py grep, query `coinduction|coextendScalars`, subdirectory
  Algebra/Category/ModuleCat: 7 hits in EnoughInjectives and ChangeOfRings, all ordinary.
- msearch.py leansearch, query `For perfect R algebra B derived coinduction RHom B K
  is tensor with RHom B R`: 8 hits on representation coinduction, smooth tensor
  products, coalgebra unit maps, dual base change, and Kaehler modules; none match.
- rg/grep in upstream WeilConjectures for the item id and coinduction terminology:
  no existing theorem with this statement. A targeted source search for
  `rightDerivedFunctor` and `mapDerivedCategoryRightDerivedAdjunction` located the
  general unbounded constructions, whose full signatures and docstrings were read.
- rg in lean/Sheaf for coinduction, second-factor tensor, and perfect ring complexes:
  existing sheaf coinduction is on ringed spaces, not this ordinary derived tensor
  comparison. AlgebraicShriekCalculus refers to the item in proof prose only.
- Exact-name searches for `perfect_algebra_coinduction_tensor`,
  `coextendScalars_additive`, and `coinductionComplex` in Mathlib, upstream,
  dag/lean_names_upstream.json and lean/Sheaf found no collision.

The local Stacks source was opened at dualizing.tex, section-trivial,
lemma-right-adjoint, lemma-RHom-ext and lemma-RHom-is-tensor-special. It gives the
same ring map, unbounded functors, B-action via Hom, and perfectness hypothesis.
No statement dispute or source correction was necessary.

Validation: compile via the required scompile.py wrapper, with each file checked
separately. The initial diagnostic passes found the missing additive-instance
registration and an inverse needing explicit K-flat evidence; these were repaired
using the existing generic additive theorem and the uniquely characterized
isomorphism s. A final style warning was repaired by shortening the counit line.

## Second reading by N0

This is an in-thread second pass with both the unchanged JSON statement and final
Lean source open. No other agent was started, as the dispatcher explicitly forbids
it; the maintainer's independent delivery review remains the independent reading.

Checked hB against the recorded perfect-complex definition: its object is B with
restricted R-action in degree zero, not B as a B-module. Checked J/η against R[0],
and the coextension action against `CoextendScalars.smul_apply`. Checked that θ is
an isomorphism of D(B)-valued functors with source the entire D(R). Checked the
orientation of ε against the second-factor dependency and the orientation of
`mapDerivedCategoryFactors.hom` against ExactFunctor.lean:41. The counit equation
then has source U(L(QF)) and target QF on both sides. Checked that s inverse removes
F ⊗ J using precisely η and the right unitor, and that the pure-generator formula
uses h(b), reducing to h(1) on the canonical b=1 generator. The adjunction therefore
fixes the same canonical evaluation arrow as the node, including the scalar
restriction assertion. All coefficient and localization universes are explicitly
bound. There is one theorem with sorry and no sorry in data. No mathematical
mismatch or statement change was found; the compile-driven repairs above only
changed the way the same canonical constructions are elaborated.
