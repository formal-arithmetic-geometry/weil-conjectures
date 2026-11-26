/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuSpecialChartMap
import WeilConjectures.RingTheory.PopescuSpecialChartSubstitution

/-!
# Injectivity of the special-chart map

The canonical map from the polynomial algebra over `(Cbar/πCbar)[1/a_k]` to the localized
special fibre of the Popescu lifting algebra is injective.

## Implementation details

The proof constructs a left inverse by polynomial elimination, without any assumption that the
coefficient rings are nontrivial.

## References

* [Stacks, Tag 07CP] (polynomial elimination modulo `π` and comparison of the other chart
  relations)
-/

@[expose] public section

universe a c

namespace Algebra

/-- The canonical special-chart map is injective. -/
theorem popescu_special_chart_map_injective (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (cmod : (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) →+*
      (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hc : ∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = Ideal.Quotient.mk _ (d.x i))
    (hcmod : cmod.comp (Ideal.Quotient.mk _) = c.toRingHom) (k : Fin d.r) :
    Function.Injective (popescu_special_chart_map R Cbar π d c cmod hcmod k) := by
  let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
  let D₀ := d.liftingAlgebra ⧸
    Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)
  let := cmod.toAlgebra
  let a₀ : C₀ := Ideal.Quotient.mk _ (d.ε (d.reduced (d.a k)))
  let A := Localization.Away a₀
  let P := MvPolynomial (d.E k) A
  let t : D₀ := c (d.ε (d.reduced (d.a k)))
  let T := Localization.Away t
  obtain ⟨g, hg⟩ := popescu_special_chart_substitution R Cbar π d hd c cmod hc hcmod k
  have ht : t = algebraMap C₀ D₀ a₀ :=
    (DFunLike.congr_fun hcmod (d.ε (d.reduced (d.a k)))).symm
  have hu : IsUnit (g t) := by
    rw [ht, g.commutes]
    exact (IsLocalization.Away.algebraMap_isUnit a₀).map MvPolynomial.C
  let G : T →ₐ[C₀] P := IsLocalization.Away.liftAlgHom t (f := g) hu
  let f := popescu_special_chart_map R Cbar π d c cmod hcmod k
  have hX (j : d.E k) : G (f (MvPolynomial.X j)) = MvPolynomial.X j := by
    simp only [f, popescu_special_chart_map, MvPolynomial.aevalTower_X]
    change IsLocalization.Away.lift t hu _ = _
    rw [IsLocalization.Away.lift_eq]
    exact hg j
  have hC : ∀ b : A, G (f (MvPolynomial.C b)) = MvPolynomial.C b := by
    have hcoeff :
        (G.toRingHom.comp (f.toRingHom.comp MvPolynomial.C)) =
          (MvPolynomial.C : A →+* P) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers a₀)
      apply RingHom.ext
      intro b
      simp only [RingHom.comp_apply]
      change G (f (algebraMap C₀ P b)) = algebraMap C₀ P b
      rw [f.commutes, G.commutes]
    exact DFunLike.congr_fun hcoeff
  have hid : G.toRingHom.comp f.toRingHom = RingHom.id P :=
    MvPolynomial.ringHom_ext hC hX
  have hleft : Function.LeftInverse G f := fun p ↦ DFunLike.congr_fun hid p
  exact hleft.injective

end Algebra
