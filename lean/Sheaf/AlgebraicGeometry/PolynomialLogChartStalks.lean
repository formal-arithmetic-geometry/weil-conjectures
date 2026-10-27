/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PolynomialLogChartBasic

/-!
# Characteristic and boundary ideal of a polynomial logarithmic chart

Source: ILO, Exposé VI 1.1--1.2 and the polynomial case of 1.8, pp.69--71.
(blueprint: lem-trf-polynomial-log-chart-stalks).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Polynomial chart calculation, independent of log regularity of the base.
Source: ILO VI 1.1--1.2, polynomial case of 1.8, pp.69--71
(blueprint: lem-trf-polynomial-log-chart-stalks).

Proof:
1. The product of an fs monoid with the free monoid on finitely many generators
is fs: unite the two finite generating sets; group completion is the product of
completions, so injectivity and saturation are checked in each factor. The given
global stalk chart therefore witnesses that N is fine saturated at every point.
2. In the canonical strict-local map A → B the inverse image of the maximal
ideal is the maximal ideal. For the polynomial structural map, the elements
mapping to units form H × N^(Kᶜ), where H is the unit face of the base chart:
a product is a unit exactly when each factor is, and t_i is a nonunit exactly
when i belongs to K. Apply chart-face localization and logification to both
charts. Inverting this face and quotienting its group of units identifies the
characteristic with the base characteristic times N^K. The map kills precisely
the complementary coordinate generators, giving the displayed formula on (p,n).
3. Group completion of the characteristic product is the product with Z^K.
After tensoring with Q it is the direct sum with Q^K; take dimensions and apply
Cardinal.toENat to obtain the rank equation, also if the base rank is infinite.
4. Every log germ is a chart germ times a ring unit. The nonunit chart elements
are precisely those whose base component is a nonunit or whose exponent of
some t_i, i ∈ K, is positive. Their images lie in IB + (t_i : i ∈ K).
Conversely every base nonunit generator remains a nonunit, by locality of A → B,
and every selected t_i is a nonunit. This proves the ideal equality. Images of
base log nonunits lie in m_A since the log structure reflects ring units;
taking their ideal span gives I ≤ m_A. The strict-local comparison transports
these statements to the recorded affine-colimit rings. Empty K and r = 0 use
the same empty sums; the empty base has no geometric points.
-/
theorem polynomial_log_chart_stalks
    (C P : Type u) [CommRing C] [CommMonoid P]
    [hN : IsLocallyNoetherian (Spec (.of C))]
    (M : EtaleLogStructure (Spec (.of C))) (hfs : M.IsFineSaturated)
    (hP : IsFineSaturatedMonoid P) (α : P →* C)
    (cY : P →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of C))))))
    (hcY : M.IsChart (Scheme.Etale.mk (𝟙 (Spec (.of C)))) cY)
    (hα : ∀ p : P, M.alpha.app (op (Scheme.Etale.mk (𝟙 (Spec (.of C))))) (cY p) =
      (Scheme.ΓSpecIso (.of C)).inv (α p))
    (r : ℕ) (N : EtaleLogStructure (Spec (.of (MvPolynomial (Fin r) C))))
    (cW : P × Multiplicative (Fin r →₀ ℕ) →*
      N.monoidSheaf.obj.obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of (MvPolynomial (Fin r) C)))))))
    (hcW : N.IsChart (Scheme.Etale.mk (𝟙 (Spec (.of (MvPolynomial (Fin r) C))))) cW)
    (hβ : ∀ q : P × Multiplicative (Fin r →₀ ℕ),
      N.alpha.app (op (Scheme.Etale.mk (𝟙 (Spec (.of (MvPolynomial (Fin r) C)))))) (cW q) =
        (Scheme.ΓSpecIso (.of (MvPolynomial (Fin r) C))).inv
          (PolynomialLogChart.structuralMap α r q)) :
    N.IsFineSaturated ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (w : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin r) C)))
        (y : Spec (.of Ω) ⟶ Spec (.of C))
        (hy : w ≫ Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : C →+* MvPolynomial (Fin r) C)) = y),
        (∃ e : N.characteristic w ≃*
            M.characteristic y × Multiplicative (PolynomialLogChart.vanishingCoordinates w →₀ ℕ),
          ∀ (p : P) (n : Multiplicative (Fin r →₀ ℕ)),
            e (PolynomialLogChart.characteristicChart N cW w (p, n)) =
              (PolynomialLogChart.characteristicChart M cY y p,
                Multiplicative.ofAdd (n.toAdd.subtypeDomain
                  (fun i ↦ i ∈ PolynomialLogChart.vanishingCoordinates w)))) ∧
        N.characteristicRank w = M.characteristicRank y +
          (PolynomialLogChart.vanishingCoordinates w).card ∧
        PolynomialLogChart.nonunitIdeal N w =
          Ideal.map (strictHenselizationRingMapAlong
            (Spec.map (CommRingCat.ofHom
              (MvPolynomial.C : C →+* MvPolynomial (Fin r) C))) y w hy)
            (PolynomialLogChart.nonunitIdeal M y) ⊔ PolynomialLogChart.coordinateIdeal w ∧
        PolynomialLogChart.nonunitIdeal M y ≤
          IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing y) := by sorry

end AlgebraicGeometry
