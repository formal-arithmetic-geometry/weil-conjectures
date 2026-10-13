/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! Base localization of a single root factor at a specified point. -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Localization of a root algebra at a prime commutes with localization of its base.

Source: Stacks Project, Tags 0EYH and 0EYI, base change of the affine root factors.
(blueprint: lem-sbc-root-factor-stalk-localization)

Proof: Identify the base stalk at q(w) with R localized at the contraction of w.
Take f0 to be the image of f; its maximal-ideal membership follows from hf.
The polynomial ring over this base localization is the localization of R[T]
at the constant polynomials coming from the complement of that contraction.
Localization commutes with the quotient by the principal ideal (T^d-f), giving
the concrete AdjoinRoot quotient over the base stalk. The prime w extends to a
prime P of this quotient, whose contraction is the maximal ideal of the base.
Since d is positive, the polynomial is monic and this quotient is integral over
the base. The prime P is therefore maximal. Transitivity of localization
identifies the localization at w of the original quotient with D_P. Compose
with the standard spectrum-stalk identification to get theta. Both quotient
and localization identifications respect the coefficient maps, so theta
composed with the structural stalk map is the displayed canonical map.
This construction uses no etale hypothesis, product decomposition or flat map. -/
theorem rootFactor_stalk_localization (R : CommRingCat.{u}) (f : R)
    (d : ℕ) (hd : 0 < d)
    (q : Spec (CommRingCat.of
      (AdjoinRoot ((Polynomial.X : Polynomial R) ^ d - Polynomial.C f))) ⟶ Spec R)
    (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R
      (AdjoinRoot ((Polynomial.X : Polynomial R) ^ d - Polynomial.C f)))))
    (w : Spec (CommRingCat.of
      (AdjoinRoot ((Polynomial.X : Polynomial R) ^ d - Polynomial.C f))))
    (hf : f ∈ (q w).asIdeal) :
    let R₀ := (Spec R).presheaf.stalk (q w)
    ∃ (f₀ : R₀), f₀ ∈ IsLocalRing.maximalIdeal R₀ ∧
      let p := (Polynomial.X : Polynomial R₀) ^ d - Polynomial.C f₀
      let D := AdjoinRoot p
      ∃ (P : Ideal D) (hP : P.IsMaximal),
        letI : P.IsPrime := hP.isPrime
        let E := Localization.AtPrime P
        ∃ θ : (Spec (CommRingCat.of
          (AdjoinRoot ((Polynomial.X : Polynomial R) ^ d - Polynomial.C f)))).presheaf.stalk w
            ≃+* E,
          θ.toRingHom.comp (q.stalkMap w).hom =
            (algebraMap D E).comp (AdjoinRoot.of p) := by sorry

end AlgebraicGeometry.Scheme
