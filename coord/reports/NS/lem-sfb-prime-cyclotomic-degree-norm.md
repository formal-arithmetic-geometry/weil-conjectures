## Worker report

The module `Sheaf.NumberTheory.PrimeCyclotomicDegreeNorm` states
`IsPrimitiveRoot.prime_adjoin_finrank_norm_sub_one`, with its entire proof `sorry`.
It introduces no definitions. The node's mathematical statement is unchanged.

Source read: Milne, Abelian Varieties, Chapter I, Lemma 14.5, printed p.63,
PDF p.69, extracted directly from `literature/milne-abelian-varieties_AV.pdf`.
The proof explicitly gives the shifted minimal polynomial and signed prime norm.
The declaration docstring reproduces all four DAG proof steps and their dependencies.

Hypothesis and clause correspondence:

- A characteristic-zero field: `{K : Type u} [Field K] [CharZero K]`, with `universe u`
  explicitly declared. No finiteness or algebraicity restriction is placed on ambient `K`.
- A prime integer: `{p : ℕ} (hp : p.Prime)`. Primes here are positive integer primes,
  as in the source's primitive pth root and exponent `p - 1`; `Nat.Prime` includes 2.
- An element of exact order p: `{η : K} (hη : IsPrimitiveRoot η p)`. The existing
  definition asserts `η ^ p = 1` and that p divides any exponent giving one.
  For positive p this is equivalent to the node's absence of smaller positive
  exponents: divide an exponent by p and use the remainder, which is less than p.
- The prime subfield uses `DivisionRing.toRatAlgebra` from
  `Mathlib.Algebra.Algebra.Rat`; this is the canonical rational embedding supplied
  by the characteristic-zero field, with no additional algebra hypothesis.
- The smallest subfield containing ℚ and η is exactly
  `IntermediateField.adjoin ℚ {η}`. Its definition is the subfield closure of the
  union of the rational image and the singleton. It is a subfield of this same `K`.
- Finiteness of E/ℚ is the first conjunct
  `FiniteDimensional ℚ (IntermediateField.adjoin ℚ {η})`, an abbreviation for
  `Module.Finite` over the field. Finiteness is concluded, never assumed.
- The degree equality is the second conjunct
  `Module.finrank ℚ (IntermediateField.adjoin ℚ {η}) = p - 1`.
- The element η inside E is the existing `IntermediateField.AdjoinSimple.gen ℚ η`,
  defined as the subtype pair of η with its canonical adjoining-field membership.
  Thus the norm argument `IntermediateField.AdjoinSimple.gen ℚ η - 1` is exactly η-1
  in E, with no arbitrary choice of lift.
- The norm equation is the last conjunct, with rational right-hand side
  `(-1 : ℚ) ^ (p - 1) * (p : ℚ)`.
  `Algebra.norm` is definitionally the determinant of left multiplication:
  `Algebra.norm_apply` states `norm ℚ x = LinearMap.det (Algebra.lmul ℚ E x)`.
  Hence it renders the node's specified determinant norm exactly.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, used by the
  canonical rational algebra and the intermediate field's inherited field/algebra
  structures; the signature and docstring of the recorded class were read.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  `Mathlib.LinearAlgebra.Dimension.Finrank`; its docstring specifies the finite
  dimensional interpretation and the infinite-rank convention. Finiteness is a
  separate conclusion here.
- `def-weil-endomorphism-determinant`: `LinearMap.det`,
  `Mathlib.LinearAlgebra.Determinant`, publicly imported through
  `Mathlib.RingTheory.Norm.Defs`; `Algebra.norm` and `Algebra.norm_apply` use precisely
  this declaration. Both determinant and norm definitions were read.

The proof dependencies currently have Mathlib matches; they are imported privately:
`minpoly.sub_algebraMap` from `Mathlib.FieldTheory.Minpoly.Field`,
`Polynomial.cyclotomic_eq_minpoly_rat` and `Polynomial.cyclotomic_prime` through
`Mathlib.RingTheory.Polynomial.Cyclotomic.Roots`,
`IntermediateField.adjoinRootEquivAdjoin` from
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`,
`AdjoinRoot.powerBasis'` from `Mathlib.RingTheory.AdjoinRoot`, and
`Algebra.norm_eq_norm_adjoin` and `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`
through `Mathlib.RingTheory.Norm.Transitivity`. The polynomial-ring definition and
norm basic module are also supplied by these public import chains. The relevant
signatures and docstrings were read locally; no dependency interface needed repair.

Edge cases checked before writing:

- For p=2, η=-1, E=ℚ, degree is 1, and norm(η-1)=-2. The displayed sign gives -2.
- For odd prime p, p-1 is even and the signed expression is p, agreeing with
  Mathlib's odd-prime norm formula.
- p=0 and p=1 are excluded by primality, so natural subtraction p-1 is the usual
  positive degree. η=1 is excluded by primitive order for p≥2.
- K can be transcendental or infinite dimensional over ℚ: only its generated
  intermediate field is asserted finite. There is no cyclotomic-extension
  hypothesis on ambient K, nor a separability or algebraic-closure hypothesis.
- The universe u is unrestricted; the subtype E has K's universe, and Mathlib's
  rational scalar action and finrank allow the base field in its own universe.

Searches for an existing statement (all through the prescribed msearch wrapper):

- LeanFinder: “The subfield generated over the rationals by a primitive prime p
  root of unity has degree p minus one and norm of the root minus one equal to
  (-1)^(p-1) p”. Eight hits, including
  `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two'` and number-field integer-norm
  analogues. None states the combined conclusion for the generated subfield.
- Loogle: `IsPrimitiveRoot, Algebra.norm`. Twelve hits, including odd-prime norm
  formulas, general primitive-root norms, and `norm_sub_one_two` for orders
  2^k with k≥2; none combines adjoining-field degree and the signed formula at p=2.
- Mathlib grep: `norm_sub_one|finrank.*totient|intermediateField_adjoin_isCyclotomicExtension`
  in `NumberTheory/Cyclotomic`. Six hits: cyclotomic degree equals totient,
  odd-prime norm formulas, and the adjoining-field cyclotomic extension theorem.
  Their source signatures were inspected. They are related ingredients, not an
  existing declaration of this whole statement.
- LeanSearch: “A rational subfield generated by a primitive pth root of unity has
  degree p minus one and the norm of the root minus one is signed p”. Eight hits;
  again primitive-root norms and odd-prime specializations, without this conjunction.
- Local rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `cyclotomic.*degree.*norm|norm_sub_one|prime_cyclotomic|primeCyclotomic` found only
  unrelated p-adic analytic norms and a docstring citation of this node in
  `Sheaf.NumberTheory.AlgebraicIntegerRootUnityCongruence`.
- The required recursive search for the node id in `lean/WeilConjectures` found no
  declaration. A name search for `prime_adjoin_finrank_norm_sub_one` in both roots,
  Mathlib, and `dag/lean_names_upstream.json` found no collision.

Compilation uses the prescribed server wrapper. An initial elaboration diagnosed
that the rational algebra instance was only available through private proof
imports; adding the public `Mathlib.Algebra.Algebra.Rat` import supplies the
canonical instance without adding a hypothesis. The final compiler and preflight
results are recorded by the delivery wrapper.

No new nodes, dependency repairs, statement corrections, or disputed statements.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
