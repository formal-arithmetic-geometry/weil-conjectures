## Worker report

The module `Sheaf.RingTheory.FiniteResidueGeometricPrime` states
`Algebra.TensorProduct.finite_residue_geometric_prime`, with its proof `sorry`.
There are no new definitions, dependency modules, or statement corrections.
The node copy changes only `lean`. No statement is disputed.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| k is a field | `k : Type u`, `[Field k]` |
| Omega/k is an algebraically closed field extension | `Ω : Type v`, `[Field Ω]`, `[Algebra k Ω]`, `[IsAlgClosed Ω]`; no algebraicity hypothesis |
| T is a commutative k-algebra | `T : Type w`, `[CommRing T]`, `[Algebra k T]` |
| p is maximal | `p : Ideal T`, `[p.IsMaximal]` |
| F = T/p is finite dimensional over k | `[FiniteDimensional k (T ⧸ p)]` |
| S = T tensor_k Omega | `T ⊗[k] Ω` throughout |
| q is a prime ideal of S | `q : Ideal (T ⊗[k] Ω)`, `[q.IsPrime]` |
| q contracts to p under t mapping to t tensor 1 | `hq : q.comap (includeLeft : T →ₐ[k] T ⊗[k] Ω).toRingHom = p` |
| Canonical well-defined Omega-algebra homomorphism F tensor Omega to S/q | `∃ h : ((T ⧸ p) ⊗[k] Ω) →ₐ[Ω] ((T ⊗[k] Ω) ⧸ q)` with `∀ (t : T) (a : Ω), h (Ideal.Quotient.mk p t ⊗ₜ[k] a) = Ideal.Quotient.mk q (t ⊗ₜ[k] a)` |
| This canonical map is surjective | `Function.Surjective h` within the same existential |
| S/q is finite dimensional over Omega | `FiniteDimensional Ω ((T ⊗[k] Ω) ⧸ q)` |
| q is maximal | `q.IsMaximal` |
| Structural map Omega to S/q is an Omega-algebra isomorphism | `Function.Bijective (algebraMap Ω ((T ⊗[k] Ω) ⧸ q))` |
| Structural map Omega to kappa(q) is an Omega-algebra isomorphism | `Function.Bijective (algebraMap Ω q.ResidueField)` |
| kappa(q) is the residue field of S localized at q | Mathlib `Ideal.ResidueField`, definitionally `IsLocalRing.ResidueField (Localization.AtPrime q)` |

The existential homomorphism is pinned to the canonical map on all pure tensors,
including all representatives of T/p. Quotient surjectivity and tensor generation
make that characterization unique, so this does not substitute an arbitrary
surjection. Bijectivity of each actual structural ring homomorphism is equivalent
to being an Omega-algebra isomorphism (`AlgEquiv.ofBijective` applied to the
structural algebra homomorphism). Thus the conclusion specifies the structural
maps themselves, rather than the existence of unrelated field isomorphisms.

The applied lambda installs `Algebra.TensorProduct.rightAlgebra` for both tensor
products, by explicit application to those canonical Mathlib instances. It adds
no quantified assumption. After beta reduction, the quotient and residue-field
structures therefore send a to the class of `1 ⊗ₜ[k] a`. There is no file-local
instance or notation and no let binder. All universes and variables are explicit;
`set_option autoImplicit false` is enabled.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`;
  `[Field k] [Field Ω] [Algebra k Ω]` is its recorded field-extension specialization.
- `def-weil-algebraic-closure`: the `mathlib_match` explicitly identifies
  `IsAlgClosed` in `Mathlib.FieldTheory.IsAlgClosed.Basic` for algebraically closed
  fields, separately from `IsAlgClosure` and `AlgebraicClosure`. The node only
  assumes an algebraically closed extension, so no algebraicity is imposed.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, the finite-module abbreviation.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, used by the tensor and pure-tensor
  notation. The existing ring and scalar structures, `includeLeft`, and
  `rightAlgebra` come from `Mathlib.RingTheory.TensorProduct.Basic`; there is no
  private tensor construction.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, and `Ideal.ResidueField`,
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`. The latter publicly imports
  the recorded localization module and uses the actual localized residue field.
- `def-weil-pbc-algebra-hom-quotient`: `AlgHom` in
  `Mathlib.Algebra.Algebra.Hom`, and `Ideal.Quotient.algebra`,
  `Ideal.Quotient.mkₐ` in `Mathlib.RingTheory.Ideal.Quotient.Operations`.
  The statement uses `→ₐ[Ω]`, the canonical quotient algebra instances, and
  `Ideal.Quotient.mk`. These are exposed by the public Mathlib imports.
- Proof leaves: `fieldOfFiniteDimensional` and
  `FiniteDimensional.exists_mul_eq_one` in
  `Mathlib.LinearAlgebra.FiniteDimensional.Basic`, and
  `IsAlgClosed.algebraMap_bijective_of_isIntegral` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`. Both modules are already public imports
  because they also supply statement dependencies. The docstring includes every
  step of the five-step node proof, including the canonical localization map.

Sources read: Stacks `algebra.tex`, the tensor universal property (Tag 00CX),
Nullstellensatz (Tag 00FV), finite-dimensional domains (Tag 00GS); and
`fields.tex`, algebraic closedness and its equivalent characterizations (Tag 09GR).
The item isolates the finite-dimensional quotient argument; it does not assume
that T itself is finite type.

Edge cases checked before writing:

- T the zero ring: there is no maximal p, so the hypotheses exclude it correctly.
  In all genuine cases T/p and the prime quotient S/q are nonzero.
- k = Omega and F = k: the scalar structure is still the right tensor factor;
  no accidental left-factor instance replaces it.
- Finite purely inseparable F/k: F tensor Omega can have nilpotents; only its
  prime quotients are asserted to be scalar fields. No reducedness is assumed.
- Finite separable F/k: multiple primes above p are permitted, with the conclusion
  separately for every such q. There is no uniqueness assertion about q.
- Omega may be transcendental over k; no algebraicity or finite dimension of
  Omega/k is introduced. T may be infinitely generated over k.
- Arbitrary and independent universes u, v, w are retained; there are no test-object
  universe bounds and no restriction on characteristic.

Searches for an existing statement (all performed with msearch.py for this item):

- LeanFinder: “A prime of a tensor product above a maximal ideal with finite
  dimensional residue field over an algebraically closed extension is maximal
  with trivial residue field” returned 8 results, including
  `PrimeSpectrum.nontrivial_iff_mem_rangeComap`,
  `Ideal.fiberIsoOfBijectiveResidueField`, and
  `Algebra.instFiniteResidueFieldOfQuasiFiniteAt`; none states the tensor-quotient
  factorization, finite-dimensionality and both structural-map conclusions.
- Loogle: `Ideal.ResidueField, IsAlgClosed` returned zero results.
- LeanSearch: “A prime of a tensor product above a finite dimensional residue field
  has quotient and residue field isomorphic to the algebraically closed scalar
  field” returned 8 results, including `Ideal.Fiber`,
  `quotMapEquivQuotMapMaximalIdealOfIsLocalization`, and
  `Algebra.QuasiFinite.finite_fiber`; none states all clauses under these hypotheses.
- Mathlib grep: `residueField.*[Aa]lgClosed|[Aa]lgClosed.*residueField|rightAlgebra`
  in RingTheory returned 25 displayed hits, chiefly right-algebra usages. Direct
  source inspection found the canonical `rightAlgebra` and the residue-field API.
- Project searches with rg over both `lean/WeilConjectures` and `lean/Sheaf` for
  `lem-trf-finite-residue-geometric-prime`, `finiteResidueGeometricPrime`,
  `finite_residue_geometric_prime`, and “Geometric prime quotients” found no
  existing declaration. The same name search in `dag/lean_names_upstream.json`
  found none. A broader “finite residue field” search found point-count and
  arithmetic local-field results, not this statement. Right-algebra searches
  found established Mathlib usages and the applied-lambda convention in
  `Sheaf.RingTheory.FiniteCoefficientPolynomialLifts`.

Validation: the prescribed scompile.py compiled the delivered module in sandbox
and library mode on the server, with no errors or warnings. No other files were
compiled, and no proof was filled.

## Second reading by Q148

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
