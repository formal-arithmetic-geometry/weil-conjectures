## Worker report

The module `Sheaf.RingTheory.PolynomialPowerLiftingUniversalHomeomorphism` states
`PrimeSpectrum.isHomeomorph_comap_includeLeft_of_polynomial_power_lifting`.
Its only proof is `sorry`; no definitions or additional theorems are introduced.
The node is unchanged except for its `lean` record.

Hypothesis and clause correspondence:

- The commutative rings R and B are `{R : Type u} {B : Type v}` with
  `[CommRing R] [CommRing B]`. Their universes are independent.
- The arbitrary ring map f is encoded by `[Algebra R B]`, with underlying map
  `algebraMap R B`. This is equivalent data for commutative rings: any given
  `f : R →+* B` supplies `f.toAlgebra`, whose algebra map is f. No compatibility,
  faithfulness, finiteness, or other property is implicit in this encoding.
- Injectivity of f is exactly `hf : Function.Injective (algebraMap R B)`.
- Every nonnegative integer n is `∀ (n : ℕ)`. The n-variable polynomial rings
  are `MvPolynomial (Fin n) R` and `MvPolynomial (Fin n) B`; labeling the variables
  from zero rather than one changes no ring or condition.
- The coefficientwise extension f_n is `MvPolynomial.map (algebraMap R B)`.
- The clause for every polynomial b is `∀ ... (b : MvPolynomial (Fin n) B)`.
  Its positive integer exponent and preimage are precisely
  `∃ N : ℕ, 0 < N ∧ ∃ a : MvPolynomial (Fin n) R,
  MvPolynomial.map (algebraMap R B) a = b ^ N`.
  N and a may depend on both n and b; no uniform exponent is asserted.
- Every commutative R-algebra C is represented by the arbitrary binder
  `(C : Type w) [CommRing C] [Algebra R C]`. The theorem is universe-polymorphic
  also in w, independently of u and v; C is not restricted by any small test
  universe in an assumption.
- The tensor product is the recorded Mathlib `C ⊗[R] B` with its canonical
  commutative-ring structure. The specified map c ↦ c tensor 1 is exactly
  `Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[R] B`.
- The conclusion is `IsHomeomorph (PrimeSpectrum.comap ...)`, the actual map of
  Zariski spaces Spec(C tensor_R B) → Spec C. It asserts that this canonical map
  is a homeomorphism, rather than the existence of an unrelated homeomorphism.
  `PrimeSpectrum` is the underlying Zariski space of the recorded affine scheme
  `AlgebraicGeometry.Spec`; no scheme isomorphism is claimed.
- There are no Noetherian, characteristic, nontriviality, finite-generation,
  finite-presentation, flatness, or field hypotheses.

Recorded dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and
  `MvPolynomial.algHom_ext` in `Mathlib.Algebra.MvPolynomial.Basic`, together
  with `MvPolynomial.aeval` and the coefficient map `MvPolynomial.map` in
  `Mathlib.Algebra.MvPolynomial.Eval` (public import).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme` (public import); their underlying topological
  objects and maps are the `PrimeSpectrum` and `PrimeSpectrum.comap` in the statement.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct.lift`, `ext'` in
  `.Basic`, and `LinearMap.rTensor` in `.Map`, all provided through the tensor
  imports. The canonical tensor object is used without a private copy.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: the Mathlib matches
  `Algebra.TensorProduct.instCommRing`, `instAlgebra`, `tmul_mul_tmul`,
  `includeLeft`, `includeRight`, `includeLeftRingHom`, and `ext` in
  `Mathlib.RingTheory.TensorProduct.Basic`, and `productMap` with its pure-tensor
  formula and inclusion identities in `.Maps` (public import). In particular the
  ring and the exact canonical inclusion used by the conclusion are already defined.
- Proof-only imports: `PrimeSpectrum.isHomeomorph_comap` in
  `Mathlib.RingTheory.Spectrum.Prime.Homeomorph` for
  `lem-pur-all-element-powers-spectrum-homeomorphism`;
  `AlgebraicGeometry.Spec.map_surjective_baseChange` in
  `Sheaf.AlgebraicGeometry.SpecSurjectiveBaseChange` for the node of that name;
  `Ideal.radical_eq_sInf` in `Mathlib.RingTheory.Ideal.Operations` and
  `PrimeSpectrum.zeroLocus_eq_iff` in `.Spectrum.Prime.Topology` for
  `lem-weil-pbc-zero-locus-eq-iff-radical-eq`.
  The supplied same-universe scheme base-change lemma can be used after lifting
  rings to a common universe in the future proof; the statement itself keeps
  the full independent universes. No dependency-interface change is necessary.

Edge cases checked before writing:

- n = 0 is included: `Fin 0` is empty, so the polynomial ring is the coefficient
  ring, as used in proof step 1. No `NeZero n` or positive-variable restriction.
- b = 0 and the empty tensor sum are allowed, with N = 1 and a = 0.
- The zero ring is allowed for R, B, and C. If R is zero, every unital R-algebra
  is zero; if B is zero, injectivity forces R zero. If C is zero, both spectra
  in the conclusion are empty, and the canonical empty map is a homeomorphism.
- The identity inclusion satisfies the power hypothesis with N = 1 and a = b;
  its tensor base changes give the expected homeomorphisms.
- No characteristic is fixed and the powers need not be prime powers. Merely
  having elementwise powers in B would be insufficient for arbitrary base change
  (finite separable field extensions of finite fields show why all n are needed);
  the actual hypothesis retains every polynomial extension.
- Injectivity is substantive, not automatic for an arbitrary algebra structure.
  A noninjective quotient map can satisfy polynomial lifting with N = 1 but fail
  to be surjective on spectra; the explicit `hf` prevents this omitted-hypothesis fault.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: query "An injective ring homomorphism whose every
  finite polynomial extension lifts a positive power of every polynomial induces
  homeomorphisms on spectra after arbitrary tensor base change". Eight hits,
  including `PrimeSpectrum.isHomeomorph_comap`, purely-inseparable field tensor
  results, standard open immersions, and spectrum fiber comparisons. No exact
  polynomial criterion for arbitrary ring inclusions.
- `msearch.py ... loogle`: query `"PrimeSpectrum", "isHomeomorph_comap"`.
  Four hits: the bijective-map result, the nil-kernel/power-lifting single-map
  result, and the two purely-inseparable field results. None is this statement.
- `msearch.py ... grep`: query
  `isHomeomorph_comap|[Aa]dequate|[Pp]ower[Ss]urject` in `RingTheory`.
  Ten hits, the same spectrum results and irrelevant occurrences of "adequate"
  in power-series substitution and primitive roots.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for polynomial/power,
  adequate, and `isHomeomorph_comap` found only field-specialized existing
  homeomorphism applications and geometric adequate-moduli results. Inspected
  `AdequateAlgebraUnitPowerKernel`, `AdequateModuliTopologicalImages`, and
  `AdequateBaseChangeAffinization`: none states the ring criterion here.
- `grep -rn` of this exact node id in `lean/WeilConjectures` found no result.
  `rg` for the polynomial-power declaration names and
  `isHomeomorph_comap_includeLeft` in both project roots, Mathlib and
  `dag/lean_names_upstream.json` found no existing declaration.

Source validation: read the primary published PDF at
https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf,
Remark 3.2.2 (printed p.496), Lemma 3.1.4 (p.495), and Proposition 3.3.5
(p.498). The node's route applies the polynomial criterion, base-change
surjectivity, and the nil-kernel single-map homeomorphism theorem. Its wording
"kernel is nilpotent" in the source-place prose is interpreted by the actual
statement and proof step 4 as elementwise nilpotence; no uniform nilpotence
assertion is introduced into Lean. No statement correction or dispute.

Validation uses only the prescribed server `scompile.py` and `deliver2.py`
wrappers. The declaration docstring records every DAG proof step and its nodes.

## Second reading by Q146

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
