/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! Stalk localization of a root product chart. 
Source: Stacks Project, Tags 0EYH, 0EYI and 0EYJ.
(blueprint: lem-sbc-root-product-chart-stalk-localization)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Extract a localized root factor from an affine etale product chart.

Source: Stacks Project, Tag 0EYH, its etale local description; Tag 0EYI,
the choice of a pointed etale neighbourhood.
(blueprint: lem-sbc-root-product-chart-stalk-localization)

Proof: The residue fields of x and y have a common field extension, so the equality
of their images gives a point z of the fibre product above both. Under alpha its
prime in a finite product belongs to a unique factor k. Localize R at y, obtaining
R0 and the image f0 of f, which belongs to its maximal ideal. Localization commutes
with the polynomial quotient and with passage to the chosen root factor. Thus the
stalk at z is D_P for a prime P of R0[T]/(T^(e k)-f0) over the closed point of R0.
The root polynomial is monic because e k is positive, so D is finite integral over
R0, and P is maximal. The projection to N is etale; its stalk map beta is local
and flat. The local map on base stalks induced by phi is essentially etale, so the
extended maximal ideal of O_(L,n x) is the maximal ideal of R0: its closed fibre is
a localization of a finite separable residue algebra, hence a field. The structural
identity for alpha gives a commuting square of these stalk maps. Extending the
base maximal-ideal equality through D_P yields J.map beta = m_R0 D_P. The case
m=0 cannot have z, and no locality of the unlocalized root algebra is used. -/
theorem rootProductChart_stalk_localization {L N : Scheme.{u}} (n : N ⟶ L)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (y : Spec R) (hφ : Etale φ)
    (x : N) (hy : φ y = n x) (f : R) (hf : f ∈ y.asIdeal)
    (m : ℕ) (e : Fin m → ℕ) (he : ∀ k, 0 < e k)
    (α : pullback n φ ≅ Spec (CommRingCat.of (∀ k : Fin m,
      AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (∀ k : Fin m,
        AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)))) =
        pullback.snd n φ) :
    let B := N.presheaf.stalk x
    let J := (IsLocalRing.maximalIdeal (L.presheaf.stalk (n x))).map (n.stalkMap x).hom
    ∃ (k : Fin m) (R₀ : CommRingCat.{u}) (_ : IsLocalRing R₀) (f₀ : R₀),
      f₀ ∈ IsLocalRing.maximalIdeal R₀ ∧
      let p := (Polynomial.X : Polynomial R₀) ^ e k - Polynomial.C f₀
      let D := AdjoinRoot p
      ∃ (P : Ideal D) (hP : P.IsMaximal),
        letI : P.IsPrime := hP.isPrime
        let E := Localization.AtPrime P
        ∃ β : B →+* E, IsLocalHom β ∧ β.Flat ∧
          J.map β = (IsLocalRing.maximalIdeal R₀).map
            ((algebraMap D E).comp (AdjoinRoot.of p)) := by sorry

end AlgebraicGeometry.Scheme
