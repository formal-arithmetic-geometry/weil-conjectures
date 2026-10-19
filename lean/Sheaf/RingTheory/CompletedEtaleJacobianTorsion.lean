/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.RingTheory.CompletedPolynomialConormal
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.EtaleRingMapConormalCriterion
import WeilConjectures.RingTheory.FiniteModuleComplete
import WeilConjectures.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent

/-!
# Completed Jacobian torsion for a finite algebra étale away from an ideal

Source: Stacks Project, restricted.tex, Tags 0AJP, 0ALQ(1), 0AJU(3), and 0GAF;
algebra.tex, Tag 00MA(3) (blueprint: lem-per-completed-etale-jacobian-torsion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite algebra over a complete Noetherian base, étale off the completion ideal,
admits a completed polynomial presentation whose conormal differential has kernel and
cokernel killed by one power of that ideal. The differential is written on `P/ker f`,
canonically identified with `E` by the surjective algebra map `f`; its finite coordinate
module is the finite direct sum in the statement. The reduction map is the canonical
`A/I → E/IE` ring map.

Source: Stacks Project, restricted.tex, Tags 0AJP, 0ALQ(1), 0AJU(3), and 0GAF;
algebra.tex, Tag 00MA(3) (blueprint: lem-per-completed-etale-jacobian-torsion).

Proof:
1. Apply `lem-weil-pbc-finite-module-complete-over-complete-noetherian` to the finite
   A-module E to identify E with its completion. Module generators also generate E as
   an algebra, and their reductions generate E/IE over A/I
   (`def-weil-pbc-finite-type-algebra`).
2. Choose an ordinary finite polynomial presentation S → E with finitely generated
   kernel K using `lem-weil-pbc-finite-type-noetherian-finite-presentation`. Its conormal
   map d₀ exists by `lem-weil-pbc-etale-ring-map-conormal-criterion`. Its kernel U and
   cokernel V are finite E-modules: E is Noetherian by
   `lem-weil-pbc-finite-algebra-noetherian`, and use
   `lem-weil-pbc-noetherian-submodule-finite` for U.
3. For a in I, put g = a in E. The principal-open and basic-open pullback lemmas
   (`lem-weil-pbc-principal-localization-open-immersion` and
   `lem-weil-pbc-basic-open-pullback`) identify the restriction over D(a) with E_g.
   The hypothesis and `lem-weil-pbc-etale-composition-cancellation` make E_g étale
   over A. Present E_g by S[t] with t mapping to 1/g. Its conormal map is bijective
   by `lem-weil-pbc-etale-ring-map-conormal-criterion`. The polynomial Kähler basis
   (`lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`) identifies this map
   with the differential in `lem-weil-pbc-principal-localization-naive-cotangent`.
   That differential splits as (d₀)_g plus invertible multiplication by g, so (d₀)_g
   is bijective.
4. Exact localization (`lem-weil-pbc-localization-module-exact`) gives U_g = V_g = 0.
   The zero-fraction criterion (`def-weil-pbc-module-localization`) kills each finite
   generator by a power of g. The maximum of these exponents kills both modules.
5. Choose ideal generators aᵢ of I (`def-weil-pbc-noetherian-ring`), and positive
   exponents nᵢ killing U and V. For a nonempty list set c = 1 + Σ(nᵢ - 1).
   Every degree-c generator monomial has an exponent at least nᵢ, so I^c kills
   U and V. For an empty list I = 0, and c = 1 works.
6. Apply `lem-per-polynomial-conormal-completion` to S → E. It gives the completed
   surjection with kernel J = KP and identifies J/J² and its continuous-derivative
   differential with the base change of the ordinary ones. Compose with Ê ≃ E
   from Step 1. The tensor identifications m ⊗ e ↦ em and m ↦ m ⊗ 1
   (`def-weil-pbc-module-tensor-product`) identify its kernel and cokernel with U
   and V, so the same exponent c works. Step 1 gives the remaining clauses. -/
theorem exists_completedEtaleJacobianTorsion
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    (E : Type u) [CommRing E] [Algebra A E] [Module.Finite A E]
    (het : Etale (Spec.map (CommRingCat.ofHom (algebraMap A E)) ∣_
      ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
        (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩)) :
    IsAdicComplete I E ∧
      RingHom.FiniteType
        (Ideal.quotientMap (I.map (algebraMap A E)) (algebraMap A E)
          Ideal.le_comap_map) ∧
      ∃ (r : ℕ) (f : rigPolynomialCompletion I r →ₐ[A] E),
        Function.Surjective f ∧ ∃ c : ℕ,
          I ^ c • (rigJacobianDifferential r I (RingHom.ker f.toRingHom)).ker ≤ ⊥ ∧
          I ^ c •
            (⊤ : Submodule A ((Fin r →
              (rigPolynomialCompletion I r ⧸ RingHom.ker f.toRingHom)) ⧸
                (rigJacobianDifferential r I (RingHom.ker f.toRingHom)).range)) ≤ ⊥ := by
  sorry

end AlgebraicGeometry
