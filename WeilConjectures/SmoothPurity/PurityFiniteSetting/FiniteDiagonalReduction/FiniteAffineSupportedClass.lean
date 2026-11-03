/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionAffineOrientation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionLineInputConstructible

/-! # The supported class underlying the affine orientation

Source: blueprint finite reduction of purity, Step 4;
lem-route-affine-orientation-reduction, proof Step 2.
(blueprint: lem-pur-affine-supported-class-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction

/-- The ordinary coefficient unit is a single sheaf in degree zero.
Source: blueprint finite reduction, bounded affine input
(blueprint: lem-pur-affine-supported-class-presentation).
Proof: its degree-zero single complex is bounded below by zero. -/
theorem affineCoefficientUnit_plus (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :
    _root_.DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit P.Coefficient S) := by
  exact ⟨0, inferInstance⟩

variable (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
variable [S.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
variable [QuasiCompact (S ↘ Spec (.of P.field.k))]
variable [IsSeparated (S ↘ Spec (.of P.field.k))]

/-- The actual ordinary supported boundary before exceptional adjunction.
Source: blueprint finite reduction Step 4, Kummer boundary
(blueprint: lem-pur-affine-supported-class-presentation). -/
def ordinaryAffineSupportedClass :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).obj
        (Etale.ordinaryFiniteUnit P.Coefficient S) ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates (AffineSpace (ULift.{u} (Fin 1)) S))⟦(2 : ℤ)⟧ :=
  ((Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} P.Coefficient)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).app
      (Etale.ordinaryFiniteUnit P.Coefficient S)).hom ≫
    Etale.supportedExactDerivedMap
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S))
      (Etale.ordinaryFiniteConstant P.Coefficient S)
      (Scheme.finiteEtaleTateLine (AffineSpace (ULift.{u} (Fin 1)) S)
        P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates)
      (P.existsUnique_finiteReductionOrientationClass S).choose

/-- Compact support of the intrinsic unit in the ordinary supported presentation.
Source: blueprint finite reduction Step 4, canonical site and support comparisons
(blueprint: lem-pur-affine-supported-class-presentation). -/
def affineSupportedSourceIso :
    (P.smoothCompactSupport (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).obj
        (P.coefficientUnit S) ≅
      (Scheme.sfIntrinsicDerivedEquivalence
        (AffineSpace (ULift.{u} (Fin 1)) S) P.Ring).functor.obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace (ULift.{u} (Fin 1)) S)).mapDerivedCategory.obj
          ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
            (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).obj
            (Etale.ordinaryFiniteUnit P.Coefficient S))) := by
  let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) S
  letI := hasCompactification_of_finiteType_over_field P.field.k S
    (AffineSpace (ULift.{u} (Fin 1)) S) s
  exact (ProEtale.sfIntrinsicCompactSupportComparison P.Ring
      (HasCompactification.compactification s)).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) S).mapDerivedCategory.obj
            (Etale.ordinaryFiniteUnit P.Coefficient S)) ≪≫
    (Scheme.sfIntrinsicDerivedEquivalence
      (AffineSpace (ULift.{u} (Fin 1)) S) P.Ring).functor.mapIso
      ((ProEtale.rightDerivedLowerShriekComparisonIso
        (ModuleCat.{u + 1} P.Coefficient) s).app
          ⟨Etale.ordinaryFiniteUnit P.Coefficient S, affineCoefficientUnit_plus P S⟩)

/-- The intrinsic supported class, using the actual ordinary Kummer class and
canonical support/site comparisons, before any exceptional adjunction.
Source: blueprint finite reduction Step 4
(blueprint: lem-pur-affine-supported-class-presentation). -/
def intrinsicAffineSupportedClass :
    (P.smoothCompactSupport (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).obj
        (P.coefficientUnit S) ⟶ P.finiteReductionOrientationInput S :=
  (affineSupportedSourceIso P S).hom ≫
    (Scheme.sfIntrinsicDerivedEquivalence
      (AffineSpace (ULift.{u} (Fin 1)) S) P.Ring).functor.map
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace (ULift.{u} (Fin 1)) S)).mapDerivedCategory.map
        (ordinaryAffineSupportedClass P S))

/-- Transposing the affine orientation returns its constructed supported class.
Source: blueprint finite reduction Step 4, exceptional adjunction
(blueprint: lem-pur-affine-supported-class-presentation).
Proof: naturality of the intrinsic compact-support comparison moves the realized
adjunct through that comparison. The site compact-support comparison and the
ordinary exceptional Hom adjunction identify its counit transpose with the image
of the ordinary supported boundary. The site unit/counit triangle cancels the
inserted site unit, and the realization unit/counit triangle cancels the inserted
realization unit. The remaining composite is precisely intrinsicAffineSupportedClass. -/
theorem affineOrientation_counit :
    (P.smoothCompactSupport (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).map
        (P.finiteReductionOrientation S) ≫
      P.smoothExceptionalCounit (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
        (P.finiteReductionOrientationInput S) = intrinsicAffineSupportedClass P S  := by
  let T := AffineSpace (ULift.{u} (Fin 1)) S
  let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) S
  let := hasCompactification_of_finiteType_over_field P.field.k S T s
  let := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (.of P.field.k))
  let := isNoetherian_of_locallyOfFiniteType (S ↘ Spec (.of P.field.k))
  let E := Scheme.sfIntrinsicDerivedEquivalence S P.Ring
  let H := Scheme.sfIntrinsicDerivedEquivalence T P.Ring
  let V := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) S).mapDerivedCategory
  let W := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory
  let R := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) T).rightDerivedFunctor
  let U := Etale.ordinaryFiniteUnit P.Coefficient S
  let L := (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧
  let a := Etale.rightDerivedUpperShriekAdjunction P.Coefficient s
  let b := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T
  let c := ordinaryAffineSupportedClass P S
  let t := b.unit.app L ≫ R.map (H.unitIso.hom.app (W.obj L))
  let h := a.homEquiv U L c ≫ (Etale.rightDerivedUpperShriek P.Coefficient s).map t
  have hK : _root_.DerivedCategory.TStructure.t.plus
      (H.inverse.obj (P.finiteReductionOrientationInput S)) :=
    (P.compositionInput_bounded (P.finiteReductionOrientationInput S)
    (P.finiteReductionLineInput_constructible T)).plusEtaleOrigin.plus
  have hp := ProEtale.rightDerivedLowerShriek_map_mapDerivedCategory_map_comp_counit
    s (affineCoefficientUnit_plus P S) hK h
  have ho : P.finiteReductionOrientation S = E.functor.map (V.map h) := by
    change E.functor.map (V.map (a.homEquiv U L c) ≫
      V.map ((Etale.rightDerivedUpperShriek P.Coefficient s).map t) ≫ 𝟙 _) = _
    simp only [h, Functor.map_comp, Category.comp_id]
  have ht : (b.homEquiv _ _).symm ((a.homEquiv _ _).symm h) =
      W.map c ≫ H.unitIso.hom.app (W.obj L) := by
    dsimp only [h]
    rw [a.homEquiv_naturality_right_symm, Equiv.symm_apply_apply]
    dsimp only [t]
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [b.counit_naturality]
    simp only [b.left_triangle_components_assoc]
    rfl
  let α := ProEtale.sfIntrinsicCompactSupportComparison P.Ring
    (HasCompactification.compactification s)
  have hn := α.hom.naturality (V.map h)
  change (P.smoothCompactSupport s).map (E.functor.map (V.map h)) ≫ _ =
    α.hom.app (V.obj U) ≫ H.functor.map
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) s).map
        (V.map h)) at hn
  rw [ho]
  unfold smoothExceptionalCounit
  dsimp only
  split_ifs with hh
  · change (P.smoothCompactSupport s).map (E.functor.map (V.map h)) ≫
        (α.hom.app _ ≫ H.functor.map
          (ProEtale.rightDerivedUpperShriekCounit s _ hh) ≫
          H.counitIso.hom.app (H.functor.obj (W.obj L))) = _
    rw [← Category.assoc, ← Category.assoc]
    erw [hn]
    simp only [Category.assoc]
    erw [← H.functor.map_comp_assoc, hp, ht]
    simp only [Functor.map_comp, Category.assoc]
    rw [H.functor_unitIso_comp, Category.comp_id]
    simp only [intrinsicAffineSupportedClass, affineSupportedSourceIso,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    rfl
  · exact False.elim (hh hK)

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
