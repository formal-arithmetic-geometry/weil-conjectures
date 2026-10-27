## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.RelativeFrobeniusFunctionFieldImage`
states `AlgebraicGeometry.relative_frobenius_function_field_image`, with one
named theorem and its entire proof postponed by `sorry`. No definition, new node,
dependency repair, or statement correction is needed. All existing node fields
are preserved except `lean`.

Hypothesis and clause correspondence:

- The algebraically closed base field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- Positive characteristic is `(p : ℕ) (hp : p.Prime) (hk : (p : k) = 0)`.
  For a field this is equivalent to characteristic p > 0, rather than an extra
  assumption: positive field characteristic is prime, and prime p vanishing in
  a nonzero field implies `CharP k p`.
- The k-scheme is `(C : Scheme.{u}) (a : C ⟶ Spec (.of k))`.
  `[IsCurve a]` includes separatedness, finite type and dimension at most one;
  `[Smooth a] [IsProper a] [IsIntegral C]` give the three asserted properties.
  `(hCdim : topologicalKrullDim C = 1)` specifies dimension exactly one.
- `(n : ℕ)` permits every nonnegative integer, including zero.
- T is literally `pullback a (Spec.map (CommRingCat.ofHom
  (iterateFrobeniusOfPrime k hp hk n)))`. The existing ring homomorphism
  `iterateFrobeniusOfPrime` has value x^(p^n); no substitute twist is introduced.
  Its structure morphism is `pullback.snd`, as witnessed by the second
  projection equation `F ≫ pullback.snd ... = a`.
- `∃ (_ : IsIntegral T), ...` exposes the property of this actual twist needed
  by the existing function-field map, rather than assuming it. Similarly
  `∃ hC : (p : Γ(C, ⊤)) = 0, ...` supplies the proof argument of the existing
  absolute Frobenius. This vanishing follows from hk via pullback of constants.
- `∃! F : C ⟶ T, ...` and its first two conjuncts give exactly the morphism
  with projections `C.iterateFrobenius hp hC n` and a. Pullback uniqueness
  ensures this specifies the canonical pair morphism, not an arbitrary map.
- The zero clause is `n = 0 → IsIso (pullback.fst ...) ∧
  F ≫ pullback.fst ... = 𝟙 C`. At n=0 the base-field power map is the identity,
  so this first projection is the canonical identity-base-change isomorphism.
  It identifies F with the identity exactly as requested.
- `∃ hη : F (genericPoint C) = genericPoint T, ...` supplies the equality
  needed by the canonical generic-stalk pullback `(F.functionFieldMap hη).hom`.
  `Function.Injective` states that this actual homomorphism is an embedding.
  Field extensions use the unital homomorphism formulation of
  `def-pc-field-extension`; no arbitrary algebra structure or k-linearity is
  imposed on the first projection.
- The final equation is `Set.range (F.functionFieldMap hη).hom =
  Set.range (fun x : C.functionField ↦ x ^ (p ^ n))`. This is precisely equality
  of the two subsets inside k(C), with the right side consisting of actual
  powers, not their span, generated field, or perfect closure.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed`, documented in the
  dependency's `mathlib_match`, in `Mathlib.FieldTheory.IsAlgClosed.Basic`;
  imported through `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
- `def-pc-field-characteristic`: Mathlib `CharP`/`ringChar`, in
  `Mathlib.Algebra.CharP.Defs`; the equivalent prime-and-vanishing formulation
  also supplies the parameters of the recorded absolute Frobenius.
- `def-sc-curves`: `AlgebraicGeometry.IsCurve`, in
  `WeilConjectures.AlgebraicGeometry.Curve`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`, in
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-pc-base-change`: the recorded module
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` expressly says
  scheme base change is `Limits.pullback`, with `pullback.fst` and
  `pullback.snd`. Its `moduleBaseChange` concerns modules only and is not
  misused as a scheme construction.
- `def-weil-absolute-frobenius-scheme`:
  `AlgebraicGeometry.Scheme.iterateFrobenius`, in
  `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`, with exactly its
  primality, global-section vanishing and n arguments.
- `def-sc-function-field`: the recorded module
  `WeilConjectures.AlgebraicGeometry.FunctionField` explicitly reuses Mathlib
  `AlgebraicGeometry.Scheme.functionField` for the integral-scheme clause.
  The existing `AlgebraicGeometry.Scheme.Hom.functionFieldMap`, in
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`, is the generic
  stalk map for a generic-point-preserving morphism.
- `def-pc-field-extension`: Mathlib `Algebra`/`RingHom.toAlgebra`, in
  `Mathlib.Algebra.Algebra.Defs`. The dependency allows the equivalent
  field-plus-unital-ring-homomorphism formulation, used here.
- Proof dependency `def-weil-ring-frobenius`: `iterateFrobeniusOfPrime`, in
  `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`, publicly imported by the
  absolute Frobenius module and used for the base-field twist map.
- Proof dependency `lem-sfb-automorphism-twist-curve-lift`:
  `AlgebraicGeometry.automorphism_twist_curve_lift`, in
  `Sheaf.AlgebraicGeometry.Curve.AutomorphismTwistCurveLift`, imported as a
  proof dependency. Its full signature and proof docstring were read. It
  identifies the first projection's stalk map with a field isomorphism and
  supplies the compatible lift and the composition identity used in the plan.

The existing smoothness and properness classes are imported from
`Mathlib.AlgebraicGeometry.Morphisms.Smooth` and `.Proper`. Every universe and
variable is explicitly bound; `autoImplicit` is disabled. There are no local
notations, hidden lets, additional axioms, or definitions with postponed data.

Edge cases checked before writing:

- n=0 gives exponent 1, full image k(C), identity power map on k, and the
  explicit canonical-identification clause above; it is not omitted.
- n=1 specializes to ordinary relative Frobenius.
- p=0, p=1 and characteristic zero are excluded exactly by positive field
  characteristic, encoded by hp and hk. No assumption of positive characteristic
  of every ring of sections is substituted: the recorded Frobenius handles
  the zero ring on the empty open.
- Empty schemes, disconnected reducible curves and zero-dimensional curves
  are excluded by the node itself (integrality and dimension one).
- No false perfection assertion is made about k(C). For example the
  projective line over an algebraically closed field has the proper subfield
  k(t^(p^n)) at positive n, exactly the right-hand range here.
- The twist is not assumed identified with C as a k-scheme for positive n.
  The first projection's field map need not be k-linear.

Searches for an existing statement (all msearch calls used group N9 and this item):

1. `leanfinder`, query: "The function field embedding of iterated relative
   Frobenius on a smooth integral curve over an algebraically closed field has
   image exactly the p^n power subfield". Eight hits: abstract
   `IsPurelyInseparable.iterateFrobenius` and its algebra-map formulas, and a
   Witt-vector Frobenius result. None identifies the geometric generic-stalk
   image of this twist.
2. `loogle`, query `"frobenius", "functionField"`: zero hits.
3. `grep`, query `(frobenius|Frobenius).*(functionField|function.field)|functionField.*(frobenius|Frobenius)`:
   zero Mathlib hits. Direct rg of Mathlib AlgebraicGeometry for Frobenius
   returned no hits either.
4. `leansearch`, query: "Image of the generic stalk homomorphism of iterated
   relative Frobenius equals p^n powers in the function field of an integral
   curve". Eight hits: abstract field iterateFrobenius formulas, semilinear
   iterateFrobenius, and iteration identities; no geometric range statement.
5. Direct rg of `lean/WeilConjectures` and `lean/Sheaf` with the expression
   in (3) found an unrelated boundary Frobenius lift and the previously
   stated relative Frobenius degree theorem. The latter's signature states
   the degree, not this range equality. Its proof docstring mentions the
   range as a step, which is not an existing Lean theorem.
6. Direct grep of the exact item id in `lean/WeilConjectures`: no hits.
   Direct rg of the proposed declaration/module name in both project roots
   and `dag/lean_names_upstream.json`: no hits.

The source passages in Stacks Varieties Tag 0CCG and Curves Tag 0CCY were
opened and read. No node fault or STATEMENT-DISPUTED issue was found.

Validation: the prescribed scompile wrapper compiled this file separately
both in sandbox mode (2.3 s) and at its library module path (2.5 s), with no
errors or unexpected warnings. The delivery dry run is performed next.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
