/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationCoefficientsFrame
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionCanonicalIso
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionTateTwist
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionLowerShriekIso
public import WeilConjectures.SmoothPurity.OrientationTransitionUnit
public import WeilConjectures.SmoothPurity.OrientationFinite
public import WeilConjectures.SmoothPurity.OrientationTransitionUpperShriek

/-!
# The finite orientations under the reduction of coefficients, on the étale site

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type which is smooth of pure
relative dimension `d`, and `Ψ` the derived extension of scalars along
`Λ = 𝒪_E ⧸ ℓⁿ⁺² ⟶ Λ' = 𝒪_E ⧸ ℓⁿ⁺¹`. The canonical finite orientation
`θₘ : red_m(𝒪(d))[2d] ≅ red_m(Rf^! 𝒪)` (`ProEtale.CondensedRing.etaleReductionSmoothOrientationIso`)
is assembled from three constituents: the reduction of the Tate twist, the diagonal orientation
`ω_f ≅ Λ_X(d)[2d]` (`Etale.dualizingComplexTwistShiftIso`) and the reduction of `Rf^! 𝒪`. This
file proves that `Ψ θₙ₊₂` is `θₙ₊₁` through the isomorphisms `β : Ψ(red_{n+2} -) ≅ red_{n+1} -`
(`ProEtale.CondensedRing.map_etaleReductionSmoothOrientationIso_hom_comp`), from the
compatibility of each constituent:

* the reduction of `Rf^! 𝒪`: `ProEtale.CondensedRing.map_etaleReductionUpperShriekUnitIso_hom_comp_dualizingComplexMap`;
* the diagonal orientation: `Etale.map_dualizingComplexTwistShiftIso_reduction_canonical`, for
  the canonical Tate data `Etale.reductionTateTwistShiftData`; its hypotheses are
  `Etale.reductionTateTwistShiftData_preservesKummerBoundaries` (frame classes) and
  `Etale.reductionTateTwistShiftData_preservesSectionInvariantIso`;
* the Tate twist: `ProEtale.CondensedRing.map_etaleReductionIntegralTateTwistIso_comp`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) [Finite Λ] [Finite Λ']
  [NeZero (ringChar Λ)] [NeZero (ringChar Λ')] (k : ℕ) (hk : ringChar Λ = ringChar Λ' * k)

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The reduction of coefficients preserves the Kummer boundaries**, for the canonical Tate data
(`AlgebraicGeometry.Etale.reductionTateTwistShiftData`): it carries the unit classes, the Kummer
boundaries `∂κ(f)` and the cup products with supports over `Λ` to those over `Λ'`. Hence it
carries frame classes to frame classes
(`AlgebraicGeometry.Etale.SupportedCoefficientChange.PreservesKummerBoundaries.mapSupportedClass_frameClass`). -/
theorem reductionTateTwistShiftData_preservesKummerBoundaries :
    (reductionSupportedCoefficientChange hρ ha
      (reductionTateTwistShiftData hρ ha k hk)).PreservesKummerBoundaries :=
  sorry

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

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

/-- The canonical Tate data of the reduction `𝒪_E ⧸ ℓⁿ⁺² ⟶ 𝒪_E ⧸ ℓⁿ⁺¹`
(`Etale.reductionTateTwistShiftData`, for the `ℓ`-th power map on the roots of unity). -/
noncomputable abbrev integersModPowTateShiftData (n : ℕ) :=
  Etale.reductionTateTwistShiftData (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
    (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) ℓ
    (ringChar_integersModPowCoeff_succ ℓ E.1 (n + 1))

/-- The reduction `𝒪_E ⧸ ℓⁿ⁺² ⟶ 𝒪_E ⧸ ℓⁿ⁺¹` as a change of coefficients with supports. -/
noncomputable abbrev integersModPowSupportedCoefficientChange (n : ℕ) :=
  Etale.reductionSupportedCoefficientChange (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
    (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) (integersModPowTateShiftData ℓ E n)

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The reduction of the integral Tate twist is compatible with the reduction of coefficients**:
through `β : Ψ(red_{n+2} -) ≅ red_{n+1} -`, the identifications
`red_m(𝒪_{E,X}(d)) ≅ Λ_X(d)` (`etaleReductionIntegralTateTwistIso`) for `m = n + 2` and
`m = n + 1` correspond under the canonical Tate data `Ψ(Λ_X(d)[2d]) ≅ Λ'_X(d)[2d]`. -/
theorem map_etaleReductionIntegralTateTwistIso_comp (n : ℕ)
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) X.left]
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1)) X.left] :
    (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
          ((shiftFunctor _ (2 * d : ℤ)).map
            (etaleReductionIntegralTateTwistIso ℓ E.1 (n + 1 + 1) X d ≪≫ (λ_ _).symm).hom) ≫
        ((integersModPowSupportedCoefficientChange ℓ E n).twistShiftConstantComplexIso
          X.left d).hom =
      ((integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).commShiftIso
          (2 * d : ℤ)).hom.app _ ≫
        (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom⟦(2 * d : ℤ)⟧' ≫
          (shiftFunctor _ (2 * d : ℤ)).map
            (etaleReductionIntegralTateTwistIso ℓ E.1 (n + 1) X d ≪≫ (λ_ _).symm).hom :=
  sorry

/-- A formal pasting: if `F` carries `S₂`, `D₂` and `V₂` to `S₁`, `D₁` and `V₁` through `t`, `ω`
and `w`, then it carries `S₂ ≫ D₂⁻¹ ≫ V₂⁻¹` to `S₁ ≫ D₁⁻¹ ≫ V₁⁻¹`. -/
lemma Functor.map_comp_inv_comp_inv_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b c e : C} {b' c' e' p q : D} (S₂ : a ⟶ b) (D₂ : c ≅ b) (V₂ : e ≅ c)
    (w : F.obj e ⟶ e') (p₁ : F.obj a ⟶ p) (p₂ : p ⟶ q) (S₁ : q ⟶ b') (D₁ : c' ≅ b')
    (V₁ : e' ≅ c') (t : F.obj b ⟶ b') (ω : F.obj c ⟶ c') [IsIso ω]
    (hT : F.map S₂ ≫ t = p₁ ≫ p₂ ≫ S₁) (hD : F.map D₂.hom ≫ t = ω ≫ D₁.hom)
    (hW : F.map V₂.hom ≫ ω = w ≫ V₁.hom) :
    F.map (S₂ ≫ D₂.inv ≫ V₂.inv) ≫ w = p₁ ≫ p₂ ≫ S₁ ≫ D₁.inv ≫ V₁.inv := by
  have hD' : F.map D₂.inv = t ≫ D₁.inv ≫ inv ω := by
    rw [← cancel_epi (F.map D₂.hom), ← F.map_comp, D₂.hom_inv_id, F.map_id, reassoc_of% hD,
      D₁.hom_inv_id_assoc, IsIso.hom_inv_id]
  have hW' : F.map V₂.inv ≫ w = ω ≫ V₁.inv := by
    rw [← cancel_epi (F.map V₂.hom), ← F.map_comp_assoc, V₂.hom_inv_id, F.map_id,
      Category.id_comp, reassoc_of% hW, V₁.hom_inv_id, Category.comp_id]
  simp only [F.map_comp, Category.assoc, hW', hD', IsIso.inv_hom_id_assoc, reassoc_of% hT]

/-- **The compatibility of the finite orientations with the reduction, from its three
constituents.** Write `θₘ` for the canonical finite orientation
(`etaleReductionSmoothOrientationIso`), built from the reduction of the Tate twist, the diagonal
orientation `Dₘ : ω_f ≅ Λ_X(d)[2d]` (`Etale.dualizingComplexTwistShiftIso`) and the reduction of
`Rf^! 𝒪` (`etaleReductionUpperShriekIso`, `etaleReductionUnitIso`). Given identifications
`tsc : Ψ(Λ_X(d)[2d]) ≅ Λ'_X(d)[2d]` and `vω : Ψ ω_f ⟶ ω'_f` such that the three constituents
are compatible with `β` (`hT`, `hW`) and `Ψ D_{n+2}` is `D_{n+1}` (`hD`), `Ψ θ_{n+2}` is
`θ_{n+1}` through `β`. -/
theorem map_etaleReductionSmoothOrientationIso_hom_comp_of (n : ℕ)
    [HasCompactification f.left]
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) X.left]
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) Y.left]
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1)) X.left]
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1)) Y.left]
    (tsc : (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).obj
        ((Etale.twistShift (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) X.left d).obj
          (Etale.constantComplex _ X.left)) ≅
      (Etale.twistShift (integersModPowCoeff.{u} ℓ E.1 (n + 1)) X.left d).obj
          (Etale.constantComplex _ X.left))
    (vω : (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).obj
        (Etale.dualizingComplex (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) f.left) ⟶
      Etale.dualizingComplex (integersModPowCoeff.{u} ℓ E.1 (n + 1)) f.left) [IsIso vω]
    (hT : (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
          ((shiftFunctor _ (2 * d : ℤ)).map
            (etaleReductionIntegralTateTwistIso ℓ E.1 (n + 1 + 1) X d ≪≫ (λ_ _).symm).hom) ≫
        tsc.hom =
      ((integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).commShiftIso
          (2 * d : ℤ)).hom.app _ ≫
        (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom⟦(2 * d : ℤ)⟧' ≫
          (shiftFunctor _ (2 * d : ℤ)).map
            (etaleReductionIntegralTateTwistIso ℓ E.1 (n + 1) X d ≪≫ (λ_ _).symm).hom)
    (hD : (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
          (Etale.dualizingComplexTwistShiftIso (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1))
            f.left d Y.hom).hom ≫ tsc.hom =
      vω ≫ (Etale.dualizingComplexTwistShiftIso (integersModPowCoeff.{u} ℓ E.1 (n + 1))
            f.left d Y.hom).hom)
    (hW : (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
          ((etaleReductionUpperShriekIso ℓ E.1 (n + 1 + 1) f).app (𝟙_ _) ≪≫
            (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1))
              f.left).mapIso (etaleReductionUnitIso ℓ E.1 (n + 1 + 1) Y)).hom ≫ vω =
      (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom ≫
        ((etaleReductionUpperShriekIso ℓ E.1 (n + 1) f).app (𝟙_ _) ≪≫
          (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E.1 (n + 1))
            f.left).mapIso (etaleReductionUnitIso ℓ E.1 (n + 1) Y)).hom) :
    (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
        (etaleReductionSmoothOrientationIso ℓ E f d (n + 1 + 1)).hom ≫
      (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom =
    ((integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).commShiftIso (2 * d : ℤ)).hom.app _ ≫
      (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom⟦(2 * d : ℤ)⟧' ≫
        (etaleReductionSmoothOrientationIso ℓ E f d (n + 1)).hom := by
  exact Functor.map_comp_inv_comp_inv_comp_eq _ _
    (Etale.dualizingComplexTwistShiftIso (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) f.left d
      Y.hom)
    ((etaleReductionUpperShriekIso ℓ E.1 (n + 1 + 1) f).app (𝟙_ _) ≪≫
      (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1))
        f.left).mapIso (etaleReductionUnitIso ℓ E.1 (n + 1 + 1) Y)) _ _ _ _
    (Etale.dualizingComplexTwistShiftIso (integersModPowCoeff.{u} ℓ E.1 (n + 1)) f.left d Y.hom)
    ((etaleReductionUpperShriekIso ℓ E.1 (n + 1) f).app (𝟙_ _) ≪≫
      (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E.1 (n + 1))
        f.left).mapIso (etaleReductionUnitIso ℓ E.1 (n + 1) Y)) tsc.hom vω hT hD hW


/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The canonical finite orientations `θₙ : red_n(𝒪(d))[2d] ≅ red_n(Rf^! 𝒪)` are compatible with the
reduction of coefficients**: `Ψ θₙ₊₂` is `θₙ₊₁` through `β` and the commutation of `Ψ` with the
shift. -/
theorem map_etaleReductionSmoothOrientationIso_hom_comp (n : ℕ) :
    (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
        (etaleReductionSmoothOrientationIso ℓ E f d (n + 1 + 1)).hom ≫
      (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom =
    ((integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).commShiftIso (2 * d : ℤ)).hom.app _ ≫
      (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom⟦(2 * d : ℤ)⟧' ≫
        (etaleReductionSmoothOrientationIso ℓ E f d (n + 1)).hom := by
  haveI := HasCompactification.of_over f
  haveI : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) X.left :=
    HasInvertibleExponent.of_hom X.hom
  haveI : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1)) X.left :=
    HasInvertibleExponent.of_hom X.hom
  haveI : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) Y.left :=
    HasInvertibleExponent.of_hom Y.hom
  haveI : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1)) Y.left :=
    HasInvertibleExponent.of_hom Y.hom
  haveI : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1))
      (pullback f.left f.left) := HasInvertibleExponent.of_hom (pullback.fst f.left f.left)
  haveI : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1))
      (pullback f.left f.left) := HasInvertibleExponent.of_hom (pullback.fst f.left f.left)
  haveI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  haveI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  haveI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  haveI : QuasiCompact f.left := HasCompactification.quasiCompact_of_locallyOfFiniteType f.left Y.hom
  haveI := Etale.isIso_derivedExtendScalarsLowerShriekMap_of_locallyOfFiniteType
    (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
    (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) f.left Y.hom
  haveI := Etale.isIso_derivedExtendScalarsLowerShriekMap_of_locallyOfFiniteType
    (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
    (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) (pullback.fst f.left f.left) X.hom
  have hframe := fun (F : (pullback.diagonal f.left).EtaleFrame d) (_ : IsOpenImmersion F.e) ↦
    (Etale.reductionTateTwistShiftData_preservesKummerBoundaries
      (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
      (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) ℓ
      (ringChar_integersModPowCoeff_succ ℓ E.1 (n + 1))).mapSupportedClass_frameClass F
  have hL : (integersModPowSupportedCoefficientChange ℓ E n).PreservesSectionInvariantIso
      (pullback.diagonal f.left) := Etale.reductionTateTwistShiftData_preservesSectionInvariantIso
    (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
    (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) ℓ
    (ringChar_integersModPowCoeff_succ ℓ E.1 (n + 1)) (pullback.diagonal f.left)
  have := Etale.isIso_derivedExtendScalarsRightDerivedUpperShriekMap_app
    (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
    (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) f.left (integersModPowTateShiftData ℓ E n)
    d Y.hom hframe
  exact map_etaleReductionSmoothOrientationIso_hom_comp_of ℓ E f d n
    ((integersModPowSupportedCoefficientChange ℓ E n).twistShiftConstantComplexIso X.left d)
    (Etale.derivedExtendScalarsDualizingComplexMap
      (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
      (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) f.left
      (Etale.derivedExtendScalarsConstantComplexIso
        (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
        (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) Y.left))
    (map_etaleReductionIntegralTateTwistIso_comp ℓ E d n)
    (Etale.map_dualizingComplexTwistShiftIso_reduction_canonical
      (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
      (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) f.left (integersModPowTateShiftData ℓ E n)
      d Y.hom hframe hL)
    (map_etaleReductionUpperShriekUnitIso_hom_comp_dualizingComplexMap ℓ E.1 (n + 1) f
      (map_etaleReductionUnitIso_hom_comp_constantComplexIso ℓ E.1 (n + 1) Y))

end AlgebraicGeometry.ProEtale.CondensedRing
