/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationCoefficientsFrame
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionCanonicalIso
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionKummer
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionKummerBoundary
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionTateTwist
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionLowerShriekIso

/-!
# The frame classes and the section invariant under the reduction of coefficients

Let `Ψ` be the derived extension of scalars along a surjective morphism `ρ : Λ →+* Λ'` of
finite rings with principal kernel, with its canonical Tate data
(`AlgebraicGeometry.Etale.reductionTateTwistShiftData`). This file states the hypotheses of the
compatibility of the diagonal orientation with `Ψ`
(`Etale.map_dualizingComplexTwistShiftIso_reduction_canonical`):

* `Etale.reductionTateTwistShiftData_preservesKummerBoundaries`: `Ψ` preserves the Kummer
  boundaries, hence the frame classes;
* `Etale.reductionTateTwistShiftData_preservesSectionInvariantIso`: `Ψ` preserves the section
  invariant construction at a closed immersion.
-/

@[expose] public section

set_option profiler true
set_option profiler.threshold 3000

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

attribute [local instance] HasInvertibleExponent.opens

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) [Finite Λ] [Finite Λ']
  [NeZero (ringChar Λ)] [NeZero (ringChar Λ')] (k : ℕ) (hk : ringChar Λ = ringChar Λ' * k)

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The reduction of coefficients commutes with the cup products with supports**
(`AlgebraicGeometry.Etale.cupWithSupportsTateObject`), for the canonical Tate data: the
derived extension of scalars is monoidal, compatible with the diagonal `Λ ⟶ Λ ⊗ᴸ Λ` and with
the products `Λ(m)[2m] ⊗ᴸ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]` of the twists
(`AlgebraicGeometry.Etale.reductionTateTwistShiftData_mul`), see
`Etale.MonoidalSupportedCoefficientChange.mapSupportedClass_cupWithSupportsTateObject`. -/
theorem reductionTateTwistShiftData_mapSupportedClass_cupWithSupportsTateObject
    {U Z₁ Z₂ Z : Scheme.{u}} [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U]
    (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsClosedImmersion i] (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (m m' : ℤ)
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![Λ]).obj ((tateObject Λ U m)⟦2 * m⟧)))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![Λ]).obj ((tateObject Λ U m')⟦2 * m'⟧))) :
    (reductionSupportedCoefficientChange hρ ha
      (reductionTateTwistShiftData hρ ha k hk)).mapSupportedClass i
        ((reductionSupportedCoefficientChange hρ ha
          (reductionTateTwistShiftData hρ ha k hk)).tateShiftIso U (m + m'))
        (cupWithSupportsTateObject Λ i₁ i₂ i h α β) =
      cupWithSupportsTateObject Λ' i₁ i₂ i h
        ((reductionSupportedCoefficientChange hρ ha
          (reductionTateTwistShiftData hρ ha k hk)).mapSupportedClass i₁
          ((reductionSupportedCoefficientChange hρ ha
            (reductionTateTwistShiftData hρ ha k hk)).tateShiftIso U m) α)
        ((reductionSupportedCoefficientChange hρ ha
          (reductionTateTwistShiftData hρ ha k hk)).mapSupportedClass i₂
          ((reductionSupportedCoefficientChange hρ ha
            (reductionTateTwistShiftData hρ ha k hk)).tateShiftIso U m') β) :=
  sorry

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The reduction of coefficients preserves the Kummer boundaries**, for the canonical Tate data
(`AlgebraicGeometry.Etale.reductionTateTwistShiftData`): it carries the unit classes
(`AlgebraicGeometry.Etale.reductionTateTwistShiftData_unit`), the Kummer boundaries `∂κ(f)`
(from the Kummer classes, `AlgebraicGeometry.Etale.map_kummerClass_comp_shift`, and the
localization boundaries,
`Etale.reductionSupportedCoefficientChange_mapSupportedClass_localizationBoundaryClass`)
and the cup products with supports over `Λ` to those over `Λ'`. Hence it carries frame classes
to frame classes
(`Etale.SupportedCoefficientChange.PreservesKummerBoundaries.mapSupportedClass_frameClass`). -/
theorem reductionTateTwistShiftData_preservesKummerBoundaries :
    (reductionSupportedCoefficientChange hρ ha
      (reductionTateTwistShiftData hρ ha k hk)).PreservesKummerBoundaries where
  map_unitClass U _ _ := reductionTateTwistShiftData_unit hρ ha k hk U
  mapSupportedClass_kummerBoundary {U} _ _ f :=
    (reductionSupportedCoefficientChange hρ ha
      (reductionTateTwistShiftData hρ ha k hk)).mapSupportedClass_kummerBoundary
      (fun X _ _ ↦ ((derivedExtendScalars hρ ha X).commShiftIso (1 : ℤ)).app _ ≪≫
        (shiftFunctor _ (1 : ℤ)).mapIso (reductionTateTwistIso hρ ha k hk X 1))
      (fun X _ _ v ↦ map_kummerClass_comp_shift hρ ha X k hk _
        (by rw [reductionTateTwistIso_one, reductionTateTwistOneIso_hom]; rfl) _
        (derivedExtendScalarsConstantComplexIso_hom_eq hρ ha X) v) f
      (reductionSupportedCoefficientChange_mapSupportedClass_localizationBoundaryClass hρ ha f
        (reductionTateTwistShiftData hρ ha k hk)
        (fun X _ _ ↦ reductionTateTwistIso hρ ha k hk X 1)
        (reductionTateTwistShiftData_iso_hom hρ ha k hk U 1)
        (reductionTateTwistIso_pullback hρ ha k hk (U.basicOpen f).ι 1))
  mapSupportedClass_cupWithSupportsTateObject i₁ i₂ i _ _ _ h m m' α β :=
    reductionTateTwistShiftData_mapSupportedClass_cupWithSupportsTateObject hρ ha k hk
      i₁ i₂ i h m m' α β
/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The reduction of coefficients preserves the section invariant construction** at a closed
immersion `s` (`AlgebraicGeometry.Etale.SupportedCoefficientChange.PreservesSectionInvariantIso`):
the derived extension of scalars is monoidal and compatible with the tensor maps
`Rs^! M ⊗ᴸ Ls^* N ⟶ Rs^!(M ⊗ᴸ N)`
(`AlgebraicGeometry.Etale.MonoidalSupportedCoefficientChange.preservesSectionInvariantIso`). -/
theorem reductionTateTwistShiftData_preservesSectionInvariantIso {V B : Scheme.{u}} (s : B ⟶ V)
    [IsClosedImmersion s] :
    (reductionSupportedCoefficientChange hρ ha
      (reductionTateTwistShiftData hρ ha k hk)).PreservesSectionInvariantIso s :=
  sorry

end AlgebraicGeometry.Etale
