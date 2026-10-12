/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.CohomologyFractionPresentation
public import Mathlib.Algebra.Exact.Basic

/-! # Exact Mayer--Vietoris row of fractions

Source: Stacks Project, Tag 09MR, Mayer--Vietoris paragraph.
(blueprint: lem-sc-cohomology-fraction-mayer-vietoris-exact)
-/

@[expose] public section

universe uMV

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

/-- An exact module-natural Mayer--Vietoris family induces an exact sequence on
cohomology fractions, with the prescribed restriction, difference, and boundary formulas.
This statement concerns only the upper row: it has no nonvanishing open or comparison map.

Source: Stacks Project, Tag 09MR, Mayer--Vietoris paragraph; Tag 01EB.
Proof: Apply the given family to every nonnegative twist F tensor L^n. Naturality
of its connecting transformations and of cohomology restriction makes the maps commute
with every transition multiplication by s^b. Extend each map to direct sums; the
fraction relations are preserved, so quotient descent gives a, b, and d, and the four
formulas follow on generators. The fraction presentation is the sequential direct
limit of these twists: finite sums can be moved to a common denominator, and zero
means zero after some further transition. For a class in a kernel, represent it at
one denominator and increase that denominator until its image is zero. Exactness of
the twist at that denominator supplies a preimage. Its fraction gives the required
preimage in the quotient. Conversely composites vanish at each twist and hence on
fractions. If a degree-zero class maps to zero, increase its denominator to make both
restrictions zero; injectivity at that twist makes the numerator zero. This proves
injectivity of a 0 as well. Neither compactness nor quasi-coherence is needed.
(blueprint: lem-sc-cohomology-fraction-mayer-vietoris-exact). -/
theorem exists_cohomologyFraction_mayerVietoris_exact (X : Scheme.{uMV})
    (L F : X.Modules) [L.IsInvertible]
    (s : Γ(L, ⊤))
    (U V : X.Opens) (δ : ∀ (A B : X.Opens) (p : ℕ),
      openModuleCohomology X.toRingedSpace p (A ⊓ B) ⟶
        openModuleCohomology X.toRingedSpace (p + 1) (A ⊔ B))
    (_hinj :
      (∀ (A B : X.Opens) (G : X.Modules),
        Function.Injective
          (fun x : (openModuleCohomology X.toRingedSpace 0 (A ⊔ B)).obj G =>
            ((openModuleCohomologyRestriction X.toRingedSpace 0
                (homOfLE (le_sup_left : A ≤ A ⊔ B))).app G x,
              (openModuleCohomologyRestriction X.toRingedSpace 0
                (homOfLE (le_sup_right : B ≤ A ⊔ B))).app G x))))
    (_hexact :
      (∀ (A B : X.Opens) (G : X.Modules) (p : ℕ),
        Function.Exact
          (fun x : (openModuleCohomology X.toRingedSpace p (A ⊔ B)).obj G =>
            ((openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (le_sup_left : A ≤ A ⊔ B))).app G x,
              (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (le_sup_right : B ≤ A ⊔ B))).app G x))
          (fun x : (openModuleCohomology X.toRingedSpace p A).obj G ×
              (openModuleCohomology X.toRingedSpace p B).obj G =>
            (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_le_left : A ⊓ B ≤ A))).app G x.1 -
              (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_le_right : A ⊓ B ≤ B))).app G x.2) ∧
        Function.Exact
          (fun x : (openModuleCohomology X.toRingedSpace p A).obj G ×
              (openModuleCohomology X.toRingedSpace p B).obj G =>
            (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_le_left : A ⊓ B ≤ A))).app G x.1 -
              (openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_le_right : A ⊓ B ≤ B))).app G x.2)
          ((δ A B p).app G) ∧
        Function.Exact ((δ A B p).app G)
          (fun x : (openModuleCohomology X.toRingedSpace (p + 1) (A ⊔ B)).obj G =>
            ((openModuleCohomologyRestriction X.toRingedSpace (p + 1)
                (homOfLE (le_sup_left : A ≤ A ⊔ B))).app G x,
              (openModuleCohomologyRestriction X.toRingedSpace (p + 1)
                (homOfLE (le_sup_right : B ≤ A ⊔ B))).app G x)))) :
    ∃ (a : ∀ p : ℕ, CohomologyFractionPresentation L F s p (U ⊔ V) →+
        CohomologyFractionPresentation L F s p U × CohomologyFractionPresentation L F s p V)
      (b : ∀ p : ℕ,
        CohomologyFractionPresentation L F s p U × CohomologyFractionPresentation L F s p V →+
          CohomologyFractionPresentation L F s p (U ⊓ V))
      (d : ∀ p : ℕ, CohomologyFractionPresentation L F s p (U ⊓ V) →+
        CohomologyFractionPresentation L F s (p + 1) (U ⊔ V)),
      (∀ (p n : ℕ) (ξ : (openModuleCohomology X.toRingedSpace p (U ⊔ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        a p (cohomologyFraction L F s p (U ⊔ V) n ξ) =
          (cohomologyFraction L F s p U n
            ((openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE le_sup_left)).app (F ⊗ L.tensorPow n : X.Modules) ξ),
          cohomologyFraction L F s p V n
            ((openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE le_sup_right)).app (F ⊗ L.tensorPow n : X.Modules) ξ))) ∧
      (∀ (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p U).obj (F ⊗ L.tensorPow n : X.Modules)),
        b p (cohomologyFraction L F s p U n ξ, 0) = cohomologyFraction L F s p (U ⊓ V) n
          ((openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE inf_le_left)).app (F ⊗ L.tensorPow n : X.Modules) ξ)) ∧
      (∀ (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p V).obj (F ⊗ L.tensorPow n : X.Modules)),
        b p (0, cohomologyFraction L F s p V n ξ) = -cohomologyFraction L F s p (U ⊓ V) n
          ((openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE inf_le_right)).app (F ⊗ L.tensorPow n : X.Modules) ξ)) ∧
      (∀ (p n : ℕ) (ξ : (openModuleCohomology X.toRingedSpace p (U ⊓ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        d p (cohomologyFraction L F s p (U ⊓ V) n ξ) =
          cohomologyFraction L F s (p + 1) (U ⊔ V) n
            ((δ U V p).app (F ⊗ L.tensorPow n : X.Modules) ξ)) ∧
      Function.Injective (a 0) ∧
      (∀ p : ℕ, Function.Exact (a p) (b p) ∧ Function.Exact (b p) (d p) ∧
        Function.Exact (d p) (a (p + 1))) := by sorry

end AlgebraicGeometry
