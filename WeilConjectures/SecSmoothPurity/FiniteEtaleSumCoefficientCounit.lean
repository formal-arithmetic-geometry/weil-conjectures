/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleCoefficientCompatibility
public import WeilConjectures.AlgebraicGeometry.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportNormalization
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Finite étale sum coefficient counit

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
 sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts;
(blueprint: lem-sp-finite-etale-sum-coefficient-counit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Etale
open AlgebraicGeometry.ProEtale.CoefficientCompatibility

namespace AlgebraicGeometry.Etale

/-- Finite coefficient extension commutes with the normalized étale sum counit.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
 sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts:
 summation over geometric fibres and the sum-normalization part of Step 11
(blueprint: lem-sp-finite-etale-sum-coefficient-counit).

Proof: (1) Choose bounded flat models for the bounded constructible finite-Tor inputs.
Their scalar extensions are computed by termwise tensor; exact inverse image preserves
flat terms, and exact sum extension preserves flat terms and K-flatness. Thus the sum
comparison and the sum/evaluation counits are represented by their degreewise maps.
(2) The compactification coefficient computation identifies the proper counit mate
followed by open balancing, under graph normalization, with the summandwise chain map
`(x_s)_s ⊗ b ↦ (x_s ⊗ b)_s`. Naturality transports this square from the chosen model to
`M`. Equivalently, the first equality is the symmetric instance of the published
`ordinaryChartSumNormalization` with both canonical normalization records.
(3) On a generating finite-support section, the summandwise map followed by pullback
balancing and the `B` fold sends `(x_s)_s ⊗ b` to `∑ s, x_s ⊗ b`. Tensor of the `A` fold
sends it to `(∑ s, x_s) ⊗ b`, the same section by bilinearity. Sheafification and
localization give the second equality, and naturality transports it to `K`.
(4) Pullback preserves bounded constructibility and finite Tor amplitude, so the first
equality applies to `e* K`. Move the pullback comparison through the graph normalization
by naturality, apply the first and second equalities, and use functoriality of scalar
extension. The result is the third equality, since the compact-support counit is the
sum/evaluation counit after graph normalization. Empty sheet families give zero maps;
infinite families still have finite support. No step uses flatness of `B` over `A`.
The proof is deliberately postponed at this stage.
-/
theorem finiteEtaleSumCoefficientCounit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (N : ℕ) (_hN : 0 < N) (_hNA : (N : A) = 0) (_hNB : (N : B) = 0)
    (φ : A →+* B) {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    (_hNU : ∀ t : U, IsUnit (N : U.presheaf.stalk t))
    (_hNV : ∀ t : V, IsUnit (N : V.presheaf.stalk t))
    (e : U ⟶ V) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification e)
    (M : DerivedCategoryModule A U)
    (_hM : DerivedCategory.isBoundedConstructible A U M ∧
      ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A U a b M)
    (K : DerivedCategoryModule A V)
    (_hK : DerivedCategory.isBoundedConstructible A V K ∧
      ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A V a b K) :
    ((scalarExtension φ V).map
          (((canonicalEtaleCompactSupportNormalization A).comparison e c).hom.app M) ≫
        (sumCoefficientIso φ e).hom.app M =
      (compactScalarMap φ c).app M ≫
        ((canonicalEtaleCompactSupportNormalization B).comparison e c).hom.app
          ((scalarExtension φ U).obj M)) ∧
    ((sumCoefficientIso φ e).hom.app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
        (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
          ((properOpenCoefficientPullbackIso φ e).inv.app K) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) e inferInstance).counit.app ((scalarExtension φ V).obj K) =
      (scalarExtension φ V).map
        ((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).counit.app K)) ∧
    (((compactScalarMap φ c).app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          ((properOpenCoefficientPullbackIso φ e).inv.app K) ≫
        ((canonicalEtaleCompactSupportNormalization B).comparison e c).hom.app
          ((upperStar (ModuleCat.{u + 1} B) e).mapDerivedCategory.obj
            ((scalarExtension φ V).obj K)) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) e inferInstance).counit.app ((scalarExtension φ V).obj K) =
      (scalarExtension φ V).map
        (((canonicalEtaleCompactSupportNormalization A).comparison e c).hom.app
            ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
          (derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app K)) := by
  sorry

end AlgebraicGeometry.Etale
