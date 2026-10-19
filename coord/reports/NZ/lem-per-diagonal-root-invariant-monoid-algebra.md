## Worker report

Retained and repaired the saved packet. The single module
`Sheaf.AlgebraicGeometry.DiagonalRootInvariantMonoidAlgebra` defines the canonical
polynomial ideal `AlgebraicGeometry.diagonalRootIdeal`, its quotient
`AlgebraicGeometry.diagonalRootAlgebra`, and the quotient variables
`AlgebraicGeometry.diagonalRootGenerator`, all with real data. Its sole theorem,
`AlgebraicGeometry.diagonal_root_invariant_monoid_algebra`, has proof `by sorry`.
There are no new nodes, dependency replacements, or natural-language statement
changes. The node copy is refreshed from the current shared node and only `lean`
is changed. Explicit `autoImplicit false` and `relaxedAutoImplicit false` apply.

Hypotheses and objects, clause by clause:

- `(A : Type u) [CommRing A]` covers every commutative coefficient ring, including
  the zero ring. `(n : ℕ) (hn : 1 ≤ n)` and `hnA : IsUnit (n : A)` give precisely
  the positive integer invertible in A. `ζ : Aˣ`, `hζ`, and `hζsep` give the stated
  root of unity, its nth power, and all unit separations for `1 ≤ a < n`.
- `r : ℕ` permits zero variables and `t : Fin r → A` gives their parameters.
  `H : AddSubgroup (Fin r → ZMod n)` is the actual diagonal subgroup.
- The ideal is `Ideal.span (Set.range (fun i ↦ X i ^ n - C (t i)))`, the algebra
  is its actual polynomial quotient, and the generators are `Ideal.Quotient.mk`
  of the variables. Thus B is the node's B, not an arbitrary presented ring.
- `L : AddSubgroup (Fin r → ℚ)` with `hL` specifies exactly the rational vectors
  `a/n` whose numerator has zero pairing modulo n with every h in H. `P` with
  `hP` is exactly the nonnegative integral vectors. `Q` with `hQ` is the intersection
  of L with the nonnegative orthant; since L lies in `(1/n)ℤ^r`, this is precisely
  `L ∩ (1/n)ℕ^r`. These characterizations uniquely determine the subobjects.
- `K : AddSubgroup L` with `hK` is exactly the integral vectors inside L; its
  quotient is therefore `L/ℤ^r`. `exp : Q → Fin r → ℕ` with `hexp` gives the
  uniquely specified integer `n*q_i`, without choosing or assuming extra roots.
- The two `Algebra` instances are constrained by `hbase` and `hinclusion`.
  For every p with natural coordinate vector a, `hbase` requires its monomial
  to map to `∏ i, t i ^ a i`. This is the specified map `z^(e_i) ↦ t_i` on all
  monomials. `hinclusion` requires every integral monomial to map to that same
  monomial in `ℤ[Q]`. Because both maps are ring maps and the integral monomials
  form additive bases, these are exactly the canonical algebra structures,
  not arbitrary structure maps or extra mathematical restrictions.
- `MulSemiringAction (Multiplicative H) B` is the action by ring automorphisms;
  `SMulCommClass (Multiplicative H) A B` says it fixes A (apply to 1, which is
  fixed by every semiring action). `hgen` gives exactly `x_i ↦ ζ^(h_i) x_i`.
  These conditions uniquely determine the specified diagonal action on B.

Conclusions, clause by clause:

- `IsFineSaturatedMonoid (Multiplicative Q)` uses the recorded dependency's
  definition: finite generation, injectivity into its canonical Grothendieck
  group, and saturation in that group.
- `∀ q : Q, IsUnit (Multiplicative.ofAdd q) → q = 0` explicitly gives sharpness.
- The existential additive equivalence from the Grothendieck group to L is
  required to send each canonical generator to its actual rational vector.
  This is the canonical identification `Q^gp = L`, with the inclusion respected.
- `Finite (L ⧸ K)` and `∀ b : L, n • QuotientAddGroup.mk' K b = 0` give exactly
  the finite, n-annihilated group cokernel.
- An additive homomorphism `ι : P →+ Q`, `Function.Injective ι`, and the coordinate
  equation `(ι p).1 = p.1` state the actual injective inclusion. The following
  `∀ q : Q, ∃ p : P, p.1 = fun i ↦ n*q.1 i` states `nQ ⊆ P`.
- The final existential `e` is an A-algebra equivalence from the algebra tensor
  product `A ⊗[AddMonoidAlgebra ℤ P] AddMonoidAlgebra ℤ Q` to the actual
  `FixedPoints.subalgebra A B (Multiplicative H)`. Its first condition is exactly
  `e (a ⊗ z^q) = a * ∏ i, x_i^(nq_i)`, using `exp` and coercion into B.
- Its second condition gives `e (1 ⊗ z^(e_i)) = t_i`, for any q whose rational
  vector is the ith coordinate vector. The preceding inclusion ensures such q
  exists for every i. Its third condition gives the exact required identity
  `c_q ^ n = ∏ i, t_i^(nq_i)` in B. Coercion from the fixed subalgebra is
  injective, so the displayed equalities equally specify equalities there.

Dependency declarations read and used:

- `def-trf-fs-log-blowup`: import
  `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`; its inherited
  `AlgebraicGeometry.IsFineSaturatedMonoid` is defined in
  `Sheaf.AlgebraicGeometry.LogRegularPair`. Its signature and full definition
  were checked; it does not include sharpness, which is a separate conjunct.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`; `MvPolynomial.aeval` in
  `Mathlib.Algebra.MvPolynomial.Eval`; `MvPolynomial.algHom_ext` in Basic.
- `def-weil-pbc-algebra-hom-quotient`: `AlgHom` in
  `Mathlib.Algebra.Algebra.Hom`, and `Ideal.Quotient.algebra` /
  `Ideal.Quotient.mkₐ` in `Mathlib.RingTheory.Ideal.Quotient.Operations`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and its pure tensors in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with `TensorProduct.lift` and
  `TensorProduct.ext'` in `Mathlib.LinearAlgebra.TensorProduct.Basic`.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`:
  `Algebra.TensorProduct.instCommRing`, `includeLeft`, `includeRight`, and `ext`
  in `Mathlib.RingTheory.TensorProduct.Basic`, and `productMap` in
  `Mathlib.RingTheory.TensorProduct.Maps`. The latter is a proof-only import.
- Proof-only imports also include `Mathlib.RingTheory.AdjoinRoot`
  (`AdjoinRoot.powerBasis'`, recorded for `lem-weil-pbc-monic-quotient-free`) and
  `Mathlib.LinearAlgebra.TensorProduct.Basis` (`Module.Basis.baseChange`, recorded
  for `lem-weil-pbc-free-module-base-change-free`). All proof dependencies are
  therefore available through imports. Their signatures and docstrings were read.

Edge cases: `n = 0` is excluded exactly by the node's `n ≥ 1`. For `n = 1`, the
separation condition is empty, H is trivial, L is integral, Q = P, and all maps
reduce to the parameter evaluation. For `r = 0`, all tuples and products are
empty, both monoids are zero and both algebras are A. No Nontrivial, domain,
regularity, reducedness, nonzero-parameter or finite-type assumption is added.
Zero/nilpotent parameters and zero divisors preserve the monic quotient basis.
For H trivial, all residue monomials occur; for H full, only integral vectors
occur. For n = r = 2 and diagonal H, `(1/2,1/2)` occurs and its image has square
`t_1*t_2`. The zero ring satisfies the stated hypotheses and both algebras are
zero; the monoid conclusions remain independent of A.

Searches retained from the earlier packet and inspected in the node:

- LeanFinder query: "Invariants under a diagonal subgroup of roots of unity of
  a multivariable nth-root quotient are the base change of the invariant exponent
  monoid algebra". Results included `IsGaloisGroup.isInvariant`,
  `autEquivRootsOfUnity_smul`, and `Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under`;
  no parameter-root monoid-algebra statement.
- LeanSearch query: "Fixed subalgebra of a root algebra under a diagonal finite
  group equals the algebra on invariant monomials". Results were the general
  `FixedPoints.subalgebra` and `Algebra.IsInvariant` interfaces, not this theorem.
- Loogle query: `"MonoidAlgebra", "invariant"`; no hits.
- Mathlib grep query:
  `invariant.*[Mm]onoid|[Mm]onoid.*invariant|diagonal.*[Ii]nvariant|[Aa]bhyankar`;
  the returned ring-action, root-system and dynamics declarations are not matches.
- Current-source rg query:
  `lem-per-diagonal-root-invariant-monoid-algebra|diagonalRootIdeal|diagonal_root_invariant_monoid_algebra`
  in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared
  `lean/Sheaf` found only a docstring citation in `PrimeToOrderSNCKummerCharts.lean`.
  There is no existing declaration to bind instead.

Source self-check: read ILO Exposé IX Proposition 2.1 proof, printed pp. 133–134
(PDF pp. 139–140) from the local PDF. It identifies the natural diagonal quotient
of the parameter-root algebra with the monoid base change. The rational-lattice
convention of this node gives the same monoid chart. Its stage-1 proof explicitly
provides the algebraic generalization to arbitrary A. No node statement fault or
STATEMENT-DISPUTED remains.

The first required dry run rejected only missing `lean.existing`. Repaired that
field to false and refreshed the recorded signature and UTC date. The saved
statement also lacked constraints on its algebra structures and the explicit
sharpness, parameter and power clauses; the repaired statement includes these.
The expanded proof docstring follows all eight steps of the DAG. No theorem was
proved, no new sorry introduced beyond the owning theorem, and no live file was edited.

## Second reading by NZ

This is the required worker self-check on resumption, not a claim of an independent
reader: the dispatcher brief forbids starting another agent and assigns independent
review to the maintainer. Opened the node and module together and matched every
hypothesis and conclusion as recorded above. Repaired the arbitrary structure-map
interfaces, missing sharpness, explicit injectivity, canonical completion compatibility,
parameter and nth-power identities, stale integer-numerator docstring, incomplete
proof docstring, missing proof-only imports, and missing `lean.existing` field.
The natural-language node is retained verbatim, so no statement_change or citer
correction is needed. The Lean data definitions contain no sorry and every variable
and universe is bound. Final validation uses only scompile.py and deliver2.py.
