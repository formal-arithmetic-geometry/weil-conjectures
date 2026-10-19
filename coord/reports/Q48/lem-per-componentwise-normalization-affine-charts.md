## Worker report

The delivery states `AlgebraicGeometry.componentwise_normalization_affine_charts` in
`Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts`. Its only proof is `sorry`.
No definitions, dependency repairs, new nodes, or statement corrections are needed.
The node copy changes only `lean`. The module includes the complete seven-step natural-language
proof plan, with its node references, and the available proof-dependency imports.

Clause-by-clause correspondence:

- A reduced locally Noetherian scheme is `(X : Scheme.{u}) [IsReduced X]
  [IsLocallyNoetherian X]`; these are the recorded Mathlib predicates.
- The componentwise normalization and its map are the existing `X.reducedNormalization`
  and `X.fromReducedNormalization`, not a new normalization construction.
- An arbitrary affine open is `(U : X.Opens) (hU : IsAffineOpen U)`. Its coordinate ring A
  is `Γ(X, U)`. The isomorphism `hU.isoSpec` identifies this open scheme with `Spec A`.
  This is the intrinsic-coordinate-ring presentation of any affine open Spec A, without
  adding a chosen presentation or restricting the class of affine opens.
- The finite repetition-free complete enumeration is `∃ (t : ℕ)
  (p : Fin t → Ideal Γ(X, U))`, together with membership in `minimalPrimes`, injectivity,
  and `Set.range p = minimalPrimes Γ(X, U)`. The definition of Mathlib `minimalPrimes`
  is minimal among prime ideals, exactly the node's parenthetical condition.
- The component domain is `Γ(X, U) ⧸ p i`, its fraction field is
  `FractionRing (Γ(X, U) ⧸ p i)`, and B_i is Mathlib `integralClosure` of this quotient
  in that fraction ring. Membership in `minimalPrimes` ensures each quotient is a domain;
  thus this standard localization really is its field of fractions. No extra domain or
  finiteness assumption is imposed. These expressions use existing definitions throughout.
- The first isomorphism `e₁` has source `(X.fromReducedNormalization ⁻¹ᵁ U).toScheme`
  and target `∐ i : Fin t, Spec B_i`. Its equation, after the coproduct map to `Spec A`
  and `hU.isoSpec.inv`, is exactly `X.fromReducedNormalization ∣_ U`. It is an isomorphism
  over U, with the specified component maps.
- The second isomorphism `e₂` has target `Spec (∀ i : Fin t, B_i)`.
  Its hom is required to equal Mathlib `sigmaSpec`; this fixes the canonical map and,
  by `ι_sigmaSpec`, its factor coprojections are the spectra of the ring projections.
- The maps `q i` are constrained pointwise to be the quotient map followed by the canonical
  `algebraMap (A ⧸ p i) B_i`. The map `φ` into the product is constrained by
  `∀ a i, φ a i = q i a`. These are fully specified canonical ring maps, not arbitrary
  maps used as hypotheses. The equation `e₂.hom ≫ Spec.map φ = Sigma.desc (Spec.map ∘ q)`
  identifies the product structural map; together with the first equation, both displayed
  isomorphisms are over U for exactly the ring map in the node.
- The empty clause is `U = ⊥ → t = 0 ∧ IsEmpty ... ∧ IsEmpty ... ∧ ∀ b, b = 0`.
  It explicitly says the index has size zero, the inverse image and coproduct are empty,
  and every element of the product ring is zero. The second isomorphism also identifies
  the product spectrum with that empty coproduct. No nonemptiness binder excludes this case.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  and its `component_noetherian` field (the affine-open-Noetherian proof input).
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization`,
  `Scheme.fromReducedNormalization`, `Scheme.reducedNormalizationComponent`, and
  `Scheme.isIntegral_reducedNormalizationComponent`. The module defines the disjoint
  union of actual function-field normalizations of reduced induced components.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, the subalgebra
  whose carrier is the elements integral over its base ring.
- `Mathlib.AlgebraicGeometry.Limits`: the scheme coproduct instances, `sigmaOpenCover`,
  `disjoint_opensRange_sigmaι`, `sigmaSpec`, `ι_sigmaSpec`, and the finite-index IsIso
  instance. This is the recorded mathlib_match of the coproduct dependency; it requires
  no extra `lean` record or duplicate theorem.
- Auxiliary existing Mathlib notation/constructions: `FractionRing`, `Ideal.Quotient.mk`,
  `minimalPrimes`, `IsAffineOpen.isoSpec`, `morphismRestrict`, and `Sigma.desc`.
- Proof inputs are imported nonpublicly: `Ideal.finite_minimalPrimes_of_isNoetherianRing`
  in `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`;
  `PrimeSpectrum.zeroLocus_minimalPrimes` in `Mathlib.RingTheory.Spectrum.Prime.Topology`;
  `preimage_mem_irreducibleComponents`, `closure_image_preimage_of_isPreirreducible`,
  `exists_mem_irreducibleComponents_subset_of_isIrreducible`, `mem_irreducibleComponent`,
  and `irreducibleComponent_mem_irreducibleComponents` in `Mathlib.Topology.Irreducible`;
  `functionField_isFractionRing_of_isAffineOpen` in `Mathlib.AlgebraicGeometry.FunctionField`;
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme` in the recorded side module
  `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`. The normalization-in-extension
  declaration `Scheme.normalizationIn` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization` is already publicly imported
  by ReducedNormalization. No missing proof input has been restated.

Source checked directly: `literature/stacks-project/morphisms.tex`,
`lemma-description-normalization` (Tag 035P), parts (1), (3), (4), and
`lemma-normalization-in-terms-of-components` (Tag 0CDV). Their affine description gives
exactly the product of component integral closures and its canonical structural map.
The node assumes locally Noetherian, so its finite-component hypothesis is satisfied.

Edge cases checked mathematically before writing:

- Empty X or empty U: A is the zero ring, its prime set is empty, t = 0, the empty
  product has one element, and the inverse image and coproduct are empty.
- A normal domain: t = 1 and B = A under its canonical fraction-field embedding.
- A nonnormal domain such as k[t²,t³]: the one factor is the genuine integral closure
  k[t], not the original ring.
- A reduced ring with crossing components, k[x,y]/(xy): the two factors are k[x] and
  k[y], and the quotient maps keep both component maps.
- A product k × k: the two primes remain distinct; no connectedness is assumed.
- Components of X missing U disappear on restriction; no global finiteness of the
  components of X, excellence, Nagata hypothesis, or finite normalization is asserted.
- Universe u is explicitly bound and shared by schemes and their rings; Fin t excludes
  no finite enumeration. All variables are explicitly bound, with autoImplicit false.

Searches (2026-10-18):

- `msearch.py ... leanfinder`: “For a reduced locally Noetherian scheme, the inverse image
  of an affine open under componentwise normalization is the spectrum of the product of
  the integral closures of minimal prime quotients in their fraction fields”. Eight hits
  concern relative normalization (`Hom.toNormalization_app_preimage`,
  `Hom.fromNormalization_preimage`, `Hom.ι_toNormalization`, `Hom.ι_fromNormalization`,
  their associative variants, `Hom.normalizationDiagram`, `Hom.normalization`). None
  identifies the absolute componentwise normalization with this minimal-prime product.
- `msearch.py ... loogle`: `AlgebraicGeometry.Scheme.reducedNormalization,
  integralClosure, minimalPrimes`. No hits; the side declaration is absent from Loogle.
- `msearch.py ... leansearch`: “Normalization of a reduced scheme on an affine open is
  the product of integral closures of its minimal prime quotients”. Eight hits concern
  relative normalization and integral/reduced schemes, with no exact matching statement.
- `msearch.py ... grep`: `reducedNormalization|componentwise.normalization|
  normalization.*minimalPrimes` in Mathlib AlgebraicGeometry. No hits.
- Direct `rg` searches for `reducedNormalization`, `componentwise.normalization`, the item
  id, and integral closure of quotient/fraction rings in upstream WeilConjectures and
  side `lean/Sheaf` found the dependency construction and specialized curve/excellence/
  field-change results. No exact statement. Searching `dag/lean_names_upstream.json`
  and upstream Lean for the item id found none. The finite product spectrum statement
  already exists as `sigmaSpec`; it is used, not duplicated.

No STATEMENT-DISPUTED issue or node fault was found. The module was checked through
`scompile.py`; the final compile and delivery dry run are recorded by the delivery tool.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
