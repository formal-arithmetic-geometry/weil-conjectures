/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.InertiaStrictHenselization
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Strict-local inertia: SchemeCore

Source: Stacks Project, Tag 0BSW
(blueprint: lem-dl-a1-strict-local-inertia-identification-scheme-core).
-/

@[expose] public section
set_option autoImplicit false
universe u w z
open CategoryTheory AlgebraicGeometry

/-- Inertia on an affine normalization chart is conjugate to the strict-local fixing group.

Source: Stacks Project, pione.tex, Tag 0BSW, scheme setup following the proof
(blueprint: lem-dl-a1-strict-local-inertia-identification-scheme-core).

Proof:
1. Put `A = O_{X,x}`. On `U = Spec R`, let `p` be the prime corresponding to `x` and
   `D = integralClosure R Ω`. Integral closure commutes with localization, so the integral
   closure `B` of `A` is the localization of `D` away from `p`. The given prime `r` induces
   a prime `Q` of `B` above the maximal ideal of `A`. Since `B` is integral over `A`, its
   quotient by `Q` is integral over a field, hence is a field, making `Q` maximal.
2. The transitivity of localization identifies `D_r` with `B_Q` and their residue fields.
   The Galois action commutes with the maps, since it fixes `R` and the denominators.
   Thus preserving the prime and fixing the residue field gives the same inertia subgroup.
3. The function-field/stalk theorem identifies the fraction field of `A` with `X.functionField`.
   The given normality makes `A` a normal local domain. Transfer the specified presentation
   of `C'` to its local filtered etale diagram, using the triples equivalence. The normal
   local etale-colimit theorem makes `C'` a normal domain and the structure map injective.
4. Apply the ring-core theorem to `A`, `C'`, and `Q`, lifting to a common universe where
   necessary. Its compatible distinguished embedding identifies the inertia fixed field.
   Closedness of inertia identifies its fixing subgroup. Extend the isomorphism from that
   embedded field to the prescribed image of `e'` to an automorphism of the separable closure;
   conjugating fixes precisely the elements of the other image. Transport Step 2 back to `r`.
   This also proves the generic-point case: then the strict-local field is a separable
   closure and both fixing subgroups are trivial.
-/
theorem strictLocalInertiaIdentificationSchemeCore
    (Ω : Type u) [Field Ω] :
      ∀ (X : Scheme.{u}) [IsIntegral X]
          (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
          (x : X) (K' C' : Type (max u w)) [Field K'] [CommRing C']
          [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x)) K']
          [IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)) K']
          [Algebra (X.presheaf.stalk x) K']
          [IsScalarTower (X.presheaf.stalk x)
            (IsLocalRing.ResidueField (X.presheaf.stalk x)) K']
          [Algebra (X.presheaf.stalk x) C']
          (hC' : Algebra.StrictHenselizationPresentationIn.{u, w}
            (X.presheaf.stalk x) K' C')
          (E' : Type z) [Field E'] [Algebra C' E'] [IsFractionRing C' E']
          [Algebra (X.presheaf.stalk x) E']
          [IsScalarTower (X.presheaf.stalk x) C' E']
          [Algebra X.functionField E']
          [IsScalarTower (X.presheaf.stalk x) X.functionField E']
          [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]
          (e' : E' →ₐ[X.functionField] Ω),
          ∀ (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
            [Algebra Γ(X, U) Ω] [IsScalarTower Γ(X, U) X.functionField Ω]
            (r : PrimeSpectrum (integralClosure Γ(X, U) Ω)),
            (Spec.map (CommRingCat.ofHom
              (algebraMap Γ(X, U) (integralClosure Γ(X, U) Ω))) ≫ hU.fromSpec) r = x →
            ∃ g : Ω ≃ₐ[X.functionField] Ω, ∀ h : Ω ≃ₐ[X.functionField] Ω,
              h ∈ r.asIdeal.inertia (Ω ≃ₐ[X.functionField] Ω) ↔
                g⁻¹ * h * g ∈ e'.fieldRange.fixingSubgroup := by
  sorry
