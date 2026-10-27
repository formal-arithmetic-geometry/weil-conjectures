## Worker report

The module `Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis` states
`AlgebraicGeometry.GmRepresentation.weightDecomposition_and_basis`, with `sorry`
as its only theorem proof. The two real-data helpers `weightSpace` and
`pointValue` spell out the subspace and evaluation already introduced in the item.
No independent new notion, dependency repair, or statement correction is needed.

I read the unchanged node, every statement dependency and its Lean record or
Mathlib match, and the seven proof steps. I read Milne, Algebraic Groups (2017),
Definition 12.11, Theorem 12.12 and Remark 12.13 on printed pp.234--235, and
Remark 4.1 and equations (24)--(25) on printed p.84, from the local PDF.
The latter expressly identifies a rational representation with a counital,
coassociative coordinate coaction and describes evaluation on every algebra.

Hypothesis and clause correspondence:

- Any field k: `{k : Type u} [Field k]`; no characteristic or closure restriction.
- A k-vector space V: `{V : Type v} [AddCommGroup V] [Module k V]`.
  Its universe is independent of the field universe.
- Finite dimension: `[FiniteDimensional k V]`, Mathlib's finite-module predicate.
- The representation: the node expressly permits its equivalent specification by
  `c : V →ₗ[k] V ⊗[k] LaurentPolynomial k`. This is the formulation used here.
  `hcoassoc : HopfAction.Coassociative k (LaurentPolynomial k) V c`
  is `(c tensor 1)c = (1 tensor Delta)c`, with the associator made explicit.
  `hcounit : HopfAction.Counital k (LaurentPolynomial k) V c` is
  `(1 tensor epsilon)c = id`, using the right tensor unitor. These are the
  existing right-coaction predicates, not locally redefined predicates.
- G_m and its specific coalgebra: `StandardGroupSchemes.multiplicative k` is
  Spec of `LaurentPolynomial k`. Its canonical Laurent Hopf structure, also used
  here, has Delta(t^a) = t^a tensor t^a and epsilon(t^a) = 1. See the defining
  instance and the `comul_C_mul_T_self` and `counit_C_mul_T` lemmas in
  `Mathlib.RingTheory.Coalgebra.MonoidAlgebra`.
- V_a = {v : c(v) = v tensor t^a}: `weightSpace c a` is exactly the equalizer
  `LinearMap.eqLocus c ((TensorProduct.mk k V (LaurentPolynomial k)).flip
  (LaurentPolynomial.T a))`, so its carrier has precisely that equation.
- V = the internal direct sum of the V_a:
  `DirectSum.IsInternal (weightSpace c)`. Its definition is bijectivity of the
  canonical summation homomorphism from the direct sum into V, including
  both existence and uniqueness of finite decompositions.
- Only finitely many nonzero summands: `{a : ℤ | weightSpace c a ≠ ⊥}.Finite`.
- Ordered basis e_1,...,e_s: `∃ (s : ℕ) (e : Module.Basis (Fin s) k V)`.
  Fin s is the usual zero-based version of this finite ordered indexing.
- Integer weights a_i: `a : Fin s → ℤ` and
  `∀ i, c (e i) = e i ⊗ₜ[k] LaurentPolynomial.T (a i)`.
- The claimed action over every commutative k-algebra and unit:
  `∀ (R : Type (max u w)) [CommRing R] [Algebra k R] (z : Rˣ) (i : Fin s),
  pointValue c R z (e i) = e i ⊗ₜ[k] ((z ^ a i : Rˣ) : R)`.
  Here `pointValue c R z = (LaurentPolynomial.leval k z).lTensor V ∘ₗ c`
  is exactly `(1 tensor ev_z)c`, hence rho_R(z) on v tensor 1 by Milne 4.1.
  LaurentPolynomial.leval evaluates the finite Laurent sum by scalar
  multiplication; with an algebra structure this is ordinary substitution
  using the algebra map. This is canonical evaluation, not an arbitrary map
  standing in for an action. The right side equals z^(a_i) times e_i tensor 1.
  The test-algebra universe `max u w` is at least that of k and is arbitrarily
  large; it cannot make the assertion vacuous by being smaller than the field.
- Every characteristic and dimension zero: there are no characteristic,
  nonzero-vector-space, nonempty-index or nontrivial-test-algebra hypotheses.

Dependency declarations and source signatures read:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, a commutative ring
  with the division ring structure, including nontriviality.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  `Mathlib.CategoryTheory.Monoidal.Grp`; its explicit specialization to
  `Over (Spec (.of k))` and `IsMonHom` is documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, which I read.
  The equivalent coaction formulation needs no extra group-scheme binder.
- `def-sc-gm-ga`: `AlgebraicGeometry.StandardGroupSchemes.multiplicative`
  and `multiplicativeGroup`, `Sheaf.AlgebraicGeometry.StandardGroupSchemes`.
  These define exactly Spec of the Laurent algebra and its canonical Hopf law.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, abbreviation for Module.Finite.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and `TensorProduct.mk`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; `TensorProduct.lift` and `ext'`,
  `Mathlib.LinearAlgebra.TensorProduct.Basic`; `LinearMap.lTensor` and
  `rTensor`, `Mathlib.LinearAlgebra.TensorProduct.Map`.
- `def-weil-laurent-polynomial-ring`: `LaurentPolynomial`, `LaurentPolynomial.T`
  and `LaurentPolynomial.leval`, `Mathlib.Algebra.Polynomial.Laurent`.
  Only its abstract Laurent ring, unique coefficients and evaluation are used;
  no second realization inside the rational-function field is introduced.
- `def-weil-pbc-free-module`: `Module.Free`,
  `Mathlib.LinearAlgebra.FreeModule.Basic`, and its constituent `Module.Basis`,
  `Mathlib.LinearAlgebra.Basis.Defs`. A Basis is the linear coordinate
  equivalence with finitely supported coefficient families, exactly the node.
- Added landed statement dependency `def-sfb-hopf-action-module-data`:
  `HopfAction.Coassociative` and `HopfAction.Counital`,
  `Sheaf.RingTheory.HopfActionModuleData`, read with the full linear-map
  formulas and docstrings. This is an additive stmt_deps update authorized by
  brief-stage2 §5, not a new definition or a correction of the statement.
- Stated proof dependency `lem-sfb-hopf-coaction-linearization`:
  `HopfAction.hopfCoactionLinearization`,
  `Sheaf.AlgebraicGeometry.HopfCoactionLinearization`, imported non-publicly.
  I read its full signature and docstring: it relates the actual affine
  linearization and module coaction by evaluating the linearization on
  module generators. Its other three statements cover morphisms, unit and tensor.

Edge cases checked mathematically before writing:

- V = 0: every weight space is bottom, the direct-sum map is the unique
  bijection between zero modules, the nonzero-weight set is empty, and s = 0
  gives the empty basis. No positivity assumption on s occurs in Lean.
- Trivial representation: the only nonzero possible weight is zero, and
  evaluation of T 0 at any unit is 1.
- Negative weights, for example -3: the equation uses T (-3), while the
  action uses the integer power of the unit z, so no inverse of a nonunit
  or natural-number truncation appears.
- Finite field F_2 and positive characteristic: the coaction distinguishes
  integer weights even if all rational units act trivially. No Lie-algebra
  or k-point weight space is substituted for the stated group-scheme one.
- Repeated weights: multiple independent basis vectors may carry the same
  integer weight; neither the basis weights nor the weight spaces are
  required to be distinct or one-dimensional.
- R = 0: CommRing allows the zero algebra; tensor and unit power evaluation
  are defined there, and the formula still holds. No nontriviality is assumed.

Searches actually run (all through msearch.py, Q103 / this item):

1. `leanfinder`: `Every finite dimensional rational representation of the
   multiplicative group scheme has an integer weight decomposition and a basis
   of weight vectors`. Eight Lie-module results, including
   `LieModule.Weight.instFinite` and `LieModule.iSup_genWeightSpace_eq_top`;
   none states rational G_m weight decomposition in arbitrary characteristic.
2. `loogle`: `"LaurentPolynomial", "Coalgebra"`. One hit:
   `LaurentPolynomial.instCoalgebra`, used via the existing canonical Hopf
   algebra. This supplies the coalgebra, not this theorem.
3. `grep`: `Comodule|[Rr]epresentation.*[Ww]eight|LaurentPolynomial.*(weight|decompo)`.
   One result in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, a comment
   about the Weyl-group representation; not this statement.
4. `leansearch`: `A finite dimensional comodule over the Laurent polynomial
   Hopf algebra is the direct sum of integer weight subspaces and has a weight
   basis`. Eight hits: root-pairing bases, Laurent cocommutativity, Lie-module
   weight spaces, weighted homogeneous polynomials. No exact match.
5. Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf`, Mathlib representation
   and coalgebra directories, and `dag/lean_names_upstream.json`, for
   `Comodule|comodule|GmRepresentation|weightSpace|weight.*[Bb]asis|[Rr]ational[Rr]epresentation`
   and the proposed names. The project has a tangent-space character-weight
   definition and Lie weights, and upstream GeneralLinear rational homomorphisms
   on coordinate spaces, but no exact Laurent coaction weight theorem or the
   proposed fully qualified declarations. The upstream LinearAlgebraicGroup
   Weights module concerns represented degree data and determinant weights,
   with algebraic-closure/characteristic-zero assumptions in its later results.
   Searching the item id in `lean/WeilConjectures` gave no attachment.

Validation: scompile.py compiled the file twice, with its sandbox module name
and its actual library name, successfully (14.4 s and 4.6 s). No errors or
unexpected warnings. The final dry-run result is recorded below after checking.
No STATEMENT-DISPUTED flag or statement fault was found.

Final validation: deliver2.py --no-push printed `OK (dry run)` for commit
2e84117d344, confirming both the maintainer's preflight and per-file compilation.
The delivery consists of exactly the module, node record and worker report.

## Second reading by Q103

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
