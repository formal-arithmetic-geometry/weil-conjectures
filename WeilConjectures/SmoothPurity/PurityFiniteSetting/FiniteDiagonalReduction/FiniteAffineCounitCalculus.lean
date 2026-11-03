/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionAffineOrientation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionLineInputConstructible
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteOrientationCounitReduction
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Counit calculus for the affine coefficient reduction

Source: blueprint finite reduction of purity, Step 4.
(blueprint: lem-pur-affine-reduction-counit-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The coefficient unit is finite-Tor constructible.
Source: blueprint finite reduction Step 4, bounded affine input
(blueprint: lem-pur-affine-reduction-counit-calculus).
Proof: the constructible root line shifted by two is isomorphic, by any primitive
root chart, to the coefficient unit shifted by two. The finite-Tor constructible
subcategory is invariant under isomorphisms and shifts. Cancel the shift. -/
theorem affineCoefficientUnit_ctf (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T
      (P.coefficientUnit T) := by
  have hl : (P.coefficients.l : P.field.k) ≠ 0 := by
    let : Fintype P.field.k₀ := Fintype.ofFinite _
    have : Fact P.field.p.Prime := ⟨P.field.prime⟩
    have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
    have : CharP P.field.k P.field.p :=
      charP_of_injective_algebraMap' P.field.k₀ P.field.p
    exact CharP.cast_ne_zero_of_ne_of_prime _
      (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm
  have : NeZero (P.diagonalExponent : P.field.k) := ⟨by
    change ((P.coefficients.l ^ P.level : ℕ) : P.field.k) ≠ 0
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot P.field.k P.diagonalExponent
  let Q : ObjectProperty (Scheme.proEtaleDerivedCategory T P.Ring) :=
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T
  have : Q.IsClosedUnderIsomorphisms :=
    (Scheme.finite_ctf_isTriangulated P.coefficients.l P.extension P.level P.level_pos T).1
  have : Q.IsTriangulated :=
    (Scheme.finite_ctf_isTriangulated P.coefficients.l P.extension P.level P.level_pos T).2.1
  exact (Q.prop_shift_iff_of_isStableUnderShift (P.coefficientUnit T) (2 : ℤ)).mp
    (Q.prop_of_iso (P.finiteReductionLineChart T ζ hζ)
      (P.finiteReductionLineInput_constructible T))

section
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

omit [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))] in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The compact-support scalar mate is natural.
Source: blueprint finite reduction Step 4
(blueprint: lem-pur-affine-reduction-counit-calculus).
Proof: transpose through scalar adjunction; naturality of its unit and the proper/open
restriction comparison give the same map on the restriction side. -/
theorem affineReductionSupport_naturality
    {K L : Scheme.proEtaleDerivedCategory X P.Ring} (a : K ⟶ L) :
    (P.finiteReduction m hm hmn Y).map ((P.smoothCompactSupport f).map a) ≫
        P.finiteReductionCompactSupportComparison m hm hmn f L =
      P.finiteReductionCompactSupportComparison m hm hmn f K ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          ((P.finiteReduction m hm hmn X).map a) := by
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  unfold finiteReductionCompactSupportComparison
  rw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  have hu := (P.finiteReductionAdjunction m hm hmn X).unit.naturality a
  have hc := (Scheme.sfCompactSupportRestriction.{u}
    (HasCompactification.compactification f)
      (P.finiteReductionRingHom m hm hmn)).hom.naturality
        ((P.finiteReduction m hm hmn X).map a)
  simp only [Functor.comp_map, Functor.id_map] at hu hc
  change (P.smoothCompactSupport f).map
      ((X.proEtaleCoefficientRestrictScalars.{u}
        (P.finiteReductionRingHom m hm hmn)).mapDerivedCategory.map
          ((P.finiteReduction m hm hmn X).map a)) ≫ _ =
    _ ≫ (Y.proEtaleCoefficientRestrictScalars.{u}
      (P.finiteReductionRingHom m hm hmn)).mapDerivedCategory.map
        (((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          ((P.finiteReduction m hm hmn X).map a)) at hc
  rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc, hc]
  simp only [Category.assoc]

omit [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))] in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The bounded exceptional counit is natural on finite-Tor constructible inputs.
Source: blueprint finite reduction Step 4
(blueprint: lem-pur-affine-reduction-counit-calculus).
Proof: use boundedness of the two inputs to select the actual pro-etale counits.
Their naturality, compact-support comparison naturality, and realization counit
naturality give the asserted intrinsic equation. -/
theorem affineSmoothCounit_naturality
    {K L : Scheme.proEtaleDerivedCategory Y P.Ring}
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (hL : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y L)
    (a : K ⟶ L) :
    (P.smoothCompactSupport f).map ((P.compositionExceptional f).map a) ≫
        P.smoothExceptionalCounit f L = P.smoothExceptionalCounit f K ≫ a := by
  let := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  let := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k)))
  let E := Scheme.sfIntrinsicDerivedEquivalence X P.Ring
  let H := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  have hK' := (P.compositionInput_bounded K hK).plusEtaleOrigin.plus
  have hL' := (P.compositionInput_bounded L hL).plusEtaleOrigin.plus
  have hn := ProEtale.rightDerivedUpperShriekCounit_naturality f hK' hL'
    (H.inverse.map a)
  have hs := (ProEtale.sfIntrinsicCompactSupportComparison P.Ring
    (HasCompactification.compactification f)).hom.naturality
      ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
        (H.inverse.map a))
  change (P.smoothCompactSupport f).map
      (E.functor.map ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
        (H.inverse.map a))) ≫ _ = _ at hs
  have hc := H.counitIso.hom.naturality a
  simp only [Functor.comp_map, Functor.id_map] at hc
  simp only [smoothExceptionalCounit, dif_pos hK', dif_pos hL']
  change (P.smoothCompactSupport f).map
      (E.functor.map ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
        (H.inverse.map a))) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, hs, Category.assoc, Category.assoc]
  simp only [Functor.comp_map]
  erw [← H.functor.map_comp_assoc, hn]
  rw [H.functor.map_comp, Category.assoc, Category.assoc, hc]
  simp only [Category.assoc]
  rfl

end

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- Coefficient compatibility of supported counit transposes implies compatibility
of the orientations themselves.
Source: blueprint finite reduction Step 4, exceptional adjunction
(blueprint: lem-pur-affine-reduction-counit-calculus).
Proof: the lower-level exceptional adjunction is injective on Hom from the reduced
coefficient unit. Precompose its image with the invertible compact-support scalar
comparison on that unit. Compact-support naturality, the normalized exceptional
comparison equation and counit naturality identify the left side with the reduced
supported class. The assumed supported square identifies it with the right side. -/
theorem affineOrientationReduction_of_counitSquare
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (S : Scheme.{u}) [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    (hclass :
      (P.finiteReduction m hm hmn (AffineSpace (ULift.{u} (Fin 1)) S)).map
        ((P.smoothCompactSupport (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).map
          (P.finiteReductionOrientation S) ≫
            P.smoothExceptionalCounit (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
              (P.finiteReductionOrientationInput S)) ≫
        (P.finiteReductionOrientationInputComparison m hm hmn S).hom =
      P.finiteReductionCompactSupportComparison m hm hmn
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) (P.coefficientUnit S) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).map
          (P.finiteReductionUnitComparison m hm hmn S) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).map
          ((P.finiteReductionSetting m hm).finiteReductionOrientation S) ≫
        (P.finiteReductionSetting m hm).smoothExceptionalCounit
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
          ((P.finiteReductionSetting m hm).finiteReductionOrientationInput S)) :
    (P.finiteReduction m hm hmn S).map (P.finiteReductionOrientation S) ≫
      P.finiteReductionOrientationExceptionalComparison m hm hmn S ≫
      ((P.finiteReductionSetting m hm).compositionExceptional
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).map
          (P.finiteReductionOrientationInputComparison m hm hmn S).hom =
    P.finiteReductionUnitComparison m hm hmn S ≫
      (P.finiteReductionSetting m hm).finiteReductionOrientation S := by
  let Q := P.finiteReductionSetting m hm
  let T := AffineSpace (ULift.{u} (Fin 1)) S
  let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) S
  have hu := affineCoefficientUnit_ctf P S
  let := P.finiteReductionCompactSupportComparison_isIso m hm hmn s
    (P.coefficientUnit S) hu
  have hsmall := Q.finiteReductionLineInput_constructible T
  have hlarge := P.finiteReduction_preserves_ctf m hm hmn T
    (P.finiteReductionOrientationInput S) (P.finiteReductionLineInput_constructible T)
  exact orientationSquare_of_supportedSquare
    (P.smoothCompactSupport s) (P.compositionExceptional s)
    (Q.smoothCompactSupport s) (Q.compositionExceptional s)
    (P.finiteReduction m hm hmn S) (P.finiteReduction m hm hmn T)
    (P.finiteReductionOrientation S) (Q.finiteReductionOrientation S)
    (P.finiteReductionUnitComparison m hm hmn S)
    (P.finiteReductionOrientationInputComparison m hm hmn S).hom
    (P.finiteReductionOrientationExceptionalComparison m hm hmn S)
    (P.finiteReductionCompactSupportComparison m hm hmn s (P.coefficientUnit S))
    (P.finiteReductionCompactSupportComparison m hm hmn s
      ((P.compositionExceptional s).obj (P.finiteReductionOrientationInput S)))
    (P.smoothExceptionalCounit s (P.finiteReductionOrientationInput S))
    (Q.smoothExceptionalCounit s
      ((P.finiteReduction m hm hmn T).obj (P.finiteReductionOrientationInput S)))
    (Q.smoothExceptionalCounit s (Q.finiteReductionOrientationInput S))
    (finiteReduction_counit_bijective Q s _
      (P.finiteReduction_preserves_ctf m hm hmn S _ hu) _ hsmall).1
    (affineReductionSupport_naturality P m hm hmn s (P.finiteReductionOrientation S))
    (affineSmoothCounit_naturality Q s hlarge hsmall
      (P.finiteReductionOrientationInputComparison m hm hmn S).hom)
    (P.existsUnique_finiteReductionOrientationExceptionalComparison m hm hmn S).choose_spec.1
    hclass

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
