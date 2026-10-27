## Worker report

The module `Sheaf.RingTheory.FiniteDomainPolynomialExtensionData` states
`MvPolynomial.finite_domain_polynomial_extension_data`, with one `sorry` and no
new definitions. The node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- Commutative domains A and C: `{A : Type u} {C : Type v}` with independent,
  explicit universes, `[CommRing A] [CommRing C] [IsDomain A] [IsDomain C]`.
- Normal Noetherian A: `[IsNoetherianRing A] [IsIntegrallyClosed A]`, together
  with the preceding domain assumption. No normality or Noetherianity of C
  is assumed.
- Injective homomorphism: `(φ : A →+* C) (hφ : Function.Injective φ)`.
- The prescribed finite family: `(r : ℕ) (c : Fin r → C)`; its exact module
  spanning hypothesis is `hc : ∀ x : C, ∃ a : Fin r → A,
  x = ∑ j, φ (a j) * c j`. This uses the specified structure map directly
  and imposes no choice of an additional algebra structure.
- Every nonnegative integer n: `(n : ℕ)`. The two polynomial rings are
  `MvPolynomial (Fin n) A` and `MvPolynomial (Fin n) C`.
- The coefficientwise map fixing all variables is the existing
  `MvPolynomial.map (σ := Fin n) φ`; its definition maps coefficients in
  the finitely supported monomial model. `map_C`, `map_X`, and `coeff_map`
  confirm its normalization. There is no arbitrary extension map.
- Injectivity of φ_n is `Function.Injective (map (σ := Fin n) φ)`.
- Noetherian normal domain A_n is the conjunction of `IsNoetherianRing`,
  `IsDomain`, and `IsIntegrallyClosed` on its actual polynomial ring.
- Domain C_n is `IsDomain (MvPolynomial (Fin n) C)`.
- The SAME constant family generates as a module: for every f there is
  `a : Fin r → MvPolynomial (Fin n) A` with
  `f = ∑ j, map φ (a j) * MvPolynomial.C (c j)`.
- The SAME constants generate as an algebra: `Function.Surjective
  (eval₂Hom (map (σ := Fin n) φ) (fun j : Fin r ↦ MvPolynomial.C (c j)))`.
  This evaluates the r additional algebra generators with coefficients in
  A_n through precisely φ_n. Its range is exactly the subalgebra generated
  by the constants over φ_n, so surjectivity is the node's algebra clause.
- Finite presentation is `(map (σ := Fin n) φ).FinitePresentation`.
  `RingHom.FinitePresentation` is definitionally `Algebra.FinitePresentation`
  for the algebra structure induced by that very ring homomorphism.
- Integrality is `(map (σ := Fin n) φ).IsIntegral`: its definition quantifies
  over every element, requiring a polynomial over A_n that is monic and
  evaluates to zero under φ_n. Mapping its coefficients gives exactly a
  monic polynomial with coefficients in the image of A_n, as in the node.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg` (lines 192–205).
- `def-weil-pbc-normal-ring`:
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed` (lines 65–75); the node's normal-domain specialization
  is `IsDomain` plus `IsIntegrallyClosed`.
- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial` (lines 80–83), exposed by the public Eval import;
  `Mathlib.Algebra.MvPolynomial.Eval`, `map` (331), `eval₂Hom` (158),
  `coeff_map` and `map_injective` (384–400).
- `def-weil-pbc-finitely-presented-algebra`:
  `Mathlib.RingTheory.FinitePresentation`, `Algebra.FinitePresentation`
  (44–45), `RingHom.FinitePresentation` (392–393).
- Proof dependency `lem-weil-pbc-polynomial-ring-normal-domain`:
  `Mathlib.RingTheory.Polynomial.IsIntegral`, the instance
  `instIsIntegrallyClosedPolynomialOfIsDomain` (179–181).
- Proof dependency `lem-weil-pbc-finite-type-algebra-noetherian`:
  `Mathlib.RingTheory.FiniteType`, `Algebra.FiniteType.isNoetherianRing`
  (187–189).
- Proof dependency `lem-weil-pbc-finite-type-noetherian-finite-presentation`:
  `Mathlib.RingTheory.FinitePresentation`,
  `Algebra.FinitePresentation.of_finiteType` (69). This module is already
  public because it also supplies a statement dependency.
- Proof dependency `lem-weil-pbc-finite-algebra-is-integral`:
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
  `IsIntegral.of_finite` (64) and `Algebra.IsIntegral.of_finite` (72).
  Integrality definitions were also read in IntegralClosure/IsIntegral/Defs
  (38–54). Proof-only modules are imported without `public`.

Source checks: read algebra.tex at labels lemma-polynomial-domain-normal
(Tag 030A), lemma-Noetherian-permanence (00FN),
lemma-Noetherian-finite-type-is-finite-presentation (00FP, clause 3), and
lemma-finite-is-integral (00GK). Read more-morphisms.tex at
lemma-quasi-finite-Noetherian-universally-open (0F32), including its opening
polynomial-base-change reduction. The node's explicit coefficient expansion
supplies the unchanged-generator calculation; the declaration docstring
carries all five accepted proof steps and their DAG references.

Edge cases checked before writing: n = 0 uses `Fin 0`, whose unique monomial
is the constant monomial, and the conclusions reduce to the original finite
inclusion. r = 0 is not artificially excluded; its spanning hypothesis
would force every element of the nontrivial domain C to be zero, so that
case is already impossible. Repeated and zero generators remain permitted.
The identity inclusion, Z into Z[i], arbitrary characteristics and unequal
coefficient universes cause no restriction. C need not be normal: a finite
order such as Z[sqrt(-3)] is allowed. No statement fault or disputed clause
was found.

Searches actually run on 2026-10-24:

- msearch.py LeanFinder: “A finite injective extension of domains over a
  normal Noetherian domain stays injective integral and finitely presented
  after adjoining finitely many variables with the same prescribed module
  generators”. Eight hits, including `fg_of_fg_of_fg`,
  `exists_integral_inj_algHom_of_fg`, `exists_finite_inj_algHom_of_fg`,
  `IsIntegralClosure.finite` and smooth-presentation cotangent results.
  These choose a new Noether-normalization map, concern towers, or concern
  unrelated presentations; none asserts the full conjunction for the
  fixed map and fixed family.
- msearch.py Loogle: `MvPolynomial.map, RingHom.FinitePresentation`:
  OK, zero hits.
- msearch.py LeanSearch: “The same prescribed module generators generate
  the polynomial extension of a finite injective extension of normal
  Noetherian domains”: eight hits, including
  `exists_finite_inj_algHom_of_fg`, `Module.Finite.of_injective`,
  `Algebra.Generators.toExtension`, `fg_of_injective`, and
  `instIsIntegralPolynomial`. None states this conjunction or the
  prescribed-family clause.
- msearch.py grep: `map_injective|eval₂Hom|FinitePresentation|IsIntegral`,
  subdirectory `Algebra/MvPolynomial`: 25 returned hits, primarily
  evaluation identities and `eval₂Hom`; read Eval directly to inspect
  `map`, `coeff_map`, `map_injective` and the evaluation signature.
- rg in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for
  `finite.domain.polynomial|polynomial.extension.data|MvPolynomial.map.*FinitePresentation`:
  no match. The required grep of WeilConjectures for the exact node id
  also returned no match.
- Additional rg in both RingTheory directories for polynomial-extension
  and generator phrases returned general Popescu/presentation modules,
  not this statement. An initially broad `MvPolynomial` search returned
  many unrelated occurrences and was narrowed to these phrases.
- Exact proposed declaration/module-name search throughout Mathlib,
  WeilConjectures, Sheaf and the upstream name index: no match.

Validation: scompile.py compiled both its sandbox module and
`Sheaf.RingTheory.FiniteDomainPolynomialExtensionData` on the server cleanly
(3.8 s and 3.9 s respectively), with no errors or warnings.

## Second reading by Q33

This is the dispatcher's single-worker consistency reading; no separate
agent was started, as required by the assignment. The maintainer supplies
independent review of the delivery. Re-read the node, dependency records,
and complete final module side by side. Checked each correspondence above,
particularly that `c` is retained in both generation conclusions, the
coefficient hom is exactly `map φ`, the algebra-generation evaluation has
r variables over A_n rather than n variables over A, and finite presentation
and monic equations use the same coefficient map. All assumptions remain
explicit and there are no auto-bound universes. `n : ℕ` retains zero, and
there is no added bound on r or normality assumption on C. No mismatch was
found and no statement correction or dependency repair was needed. Only
the node's `lean` field changed. All theorem proofs remain `sorry`.
