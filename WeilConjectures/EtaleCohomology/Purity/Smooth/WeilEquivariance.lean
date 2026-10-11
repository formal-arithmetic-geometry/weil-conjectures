/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# Weil equivariance of smooth purity and of the smooth trace
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Naturality

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}

/-- The twist reassociation `M(m)[2m] ≅ M ⊗ Λ_X(m)[2m]` is natural in `M`. -/
lemma twistShiftObjIso_hom_naturality (m : ℤ) {M M' : DerivedCategoryModule Λ X}
    (v : M ⟶ M') :
    (twistShift Λ X m).map v ≫ (twistShiftObjIso Λ X m M').hom =
      (twistShiftObjIso Λ X m M).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).map v).app
          ((twistShift Λ X m).obj (constantComplex Λ X)) := by
  have h := (derivedTensorRightShiftIso (ModuleCat.{u + 1} Λ) (tateObject Λ X m)
    (2 * m)).inv.naturality v
  dsimp [derivedTensorRightShiftIso, derivedTensorRight] at h
  simp only [twistShiftObjIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Category.assoc]
  erw [reassoc_of% h]
  rw [NatTrans.naturality]
  rfl

end Naturality

section Purity

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {d : ℕ} (f : X ⟶ Y) [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]
  [HasInvertibleExponent Λ X]
  (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅ (twistShift Λ X d).obj (constantComplex Λ X))
  (Φ : L((f)^*[ModuleCat.{u + 1} Λ]) ⋙
      (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
    R(f)^![ModuleCat.{u + 1} Λ])

omit [IsSeparated f] [SmoothOfRelativeDimension d f] [HasInvertibleExponent Λ X] in
/-- The smooth purity map `γ_{f,K}` built from a tensor formula `Φ` natural in `K` is natural
in `K`. -/
lemma smoothPurityIso_hom_naturality {K K' : DerivedCategoryModule Λ Y} (v : K ⟶ K') :
    (twistShift Λ X d).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map v) ≫
        (smoothPurityIso Λ f K' θ (Φ.app K')).hom =
      (smoothPurityIso Λ f K θ (Φ.app K)).hom ≫ (R(f)^![ModuleCat.{u + 1} Λ]).map v := by
  have h := Φ.hom.naturality v
  dsimp at h
  simp only [smoothPurityIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Category.assoc]
  rw [twistShiftObjIso_hom_naturality_assoc, ← NatTrans.naturality_assoc]
  erw [h]
  rfl

variable {gX : X ⟶ X} {gY : Y ⟶ Y}

variable {Λ} in
/-- Blueprint `def-pur-tate-datum`: the Tate datum `τ_m : Lg^* Λ_X(m) ≅ Λ_X(m)`, the
pullback identification of the Tate twist datum (`AlgebraicGeometry.Etale.HasTateTwist`). -/
noncomputable def tateWeilDatum (g : X ⟶ X) (m : ℤ) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X m) ⟶ tateObject Λ X m :=
  (leftDerivedUpperStarTateObjectIso g m).hom

/-- Blueprint `def-pur-tate-datum`: the datum `φ^pur_{f,K}` on the source of smooth purity. -/
noncomputable def purityWeilDatum (sq : CommSq gX f f gY) {K : DerivedCategoryModule Λ Y}
    (φK : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (L((gX)^*[ModuleCat.{u + 1} Λ])).obj
        ((twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ⟶
      (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  (leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq K).hom ≫
    (twistShift Λ X d).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map φK)

/-- Blueprint `def-pur-tate-datum`: the datum `φ^!_{f,K}` on the exceptional inverse image. -/
noncomputable def upperShriekWeilDatum (sq : IsPullback gX f f gY) {K : DerivedCategoryModule Λ Y}
    (φK : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (L((gX)^*[ModuleCat.{u + 1} Λ])).obj ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) ⟶
      (R(f)^![ModuleCat.{u + 1} Λ]).obj K :=
  (smoothPullbackExchange Λ f sq K θ (Φ.app K) θ (Φ.app _)).hom ≫
    (R(f)^![ModuleCat.{u + 1} Λ]).map φK

/-- Blueprint `thm-pur-weil-equivariance-of-purity-and-trace`: the purity square. -/
theorem isWeilMorphism_smoothPurityIso_hom (sq : IsPullback gX f f gY)
    {K : DerivedCategoryModule Λ Y} (φK : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    IsWeilMorphism gX (purityWeilDatum Λ f sq.toCommSq φK) (upperShriekWeilDatum Λ f θ Φ sq φK)
      (smoothPurityIso Λ f K θ (Φ.app K)).hom := by
  unfold IsWeilMorphism purityWeilDatum upperShriekWeilDatum
  rw [reassoc_of% (leftDerivedUpperStar_map_comp_smoothPullbackExchange_hom Λ f sq K θ (Φ.app K)
    θ (Φ.app _)), ← smoothPurityIso_hom_naturality, Category.assoc]

/-- Blueprint `def-pur-smooth-trace`: the coefficient-valued smooth trace. -/
noncomputable def smoothCoefficientTrace (K : DerivedCategoryModule Λ Y)
    (φ : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) :
    (R(f)_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ⟶ K :=
  (R(f)_![ModuleCat.{u + 1} Λ]).map (smoothPurityIso Λ f K θ φ).hom ≫
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K

variable [QuasiCompact f]

omit [IsSeparated f] [SmoothOfRelativeDimension d f] [HasInvertibleExponent Λ X] in
/-- Blueprint `thm-pur-weil-equivariance-of-purity-and-trace`: the counit square. -/
theorem isWeilMorphism_counit (sq : IsPullback gX f f gY)
    {K : DerivedCategoryModule Λ Y} (φK : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (hEx : (rightDerivedLowerShriekBaseChangeMap Λ sq).app ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) ≫
        (R(f)_![ModuleCat.{u + 1} Λ]).map
          (smoothPullbackExchange Λ f sq K θ (Φ.app K) θ (Φ.app _)).hom ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).counit.app _ =
      (L((gY)^*[ModuleCat.{u + 1} Λ])).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K)) :
    IsWeilMorphism gY (lowerShriekWeilDatum sq (upperShriekWeilDatum Λ f θ Φ sq φK)) φK
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  unfold IsWeilMorphism lowerShriekWeilDatum upperShriekWeilDatum
  rw [← hEx]
  have := (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).counit.naturality φK
  dsimp at this
  simp only [Functor.map_comp, Category.assoc, this]

omit [IsSeparated f] [SmoothOfRelativeDimension d f] [HasInvertibleExponent Λ X] in
/-- Blueprint `thm-pur-weil-equivariance-of-purity-and-trace`: the trace square. -/
theorem isWeilMorphism_smoothCoefficientTrace (sq : IsPullback gX f f gY)
    {K : DerivedCategoryModule Λ Y} (φK : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (hEx : (rightDerivedLowerShriekBaseChangeMap Λ sq).app ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) ≫
        (R(f)_![ModuleCat.{u + 1} Λ]).map
          (smoothPullbackExchange Λ f sq K θ (Φ.app K) θ (Φ.app _)).hom ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).counit.app _ =
      (L((gY)^*[ModuleCat.{u + 1} Λ])).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K)) :
    IsWeilMorphism gY (lowerShriekWeilDatum sq (purityWeilDatum Λ f sq.toCommSq φK)) φK
      (smoothCoefficientTrace Λ f θ K (Φ.app K)) :=
  ((isWeilMorphism_smoothPurityIso_hom Λ f θ Φ sq φK).rightDerivedLowerShriek_map sq).comp
    (isWeilMorphism_counit Λ f θ Φ sq φK hEx)

end Purity

section SchemeFrobenius

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} {F g : X ⟶ X}

/-- Blueprint `def-pur-compact-support-transport`: the scheme-Frobenius form
`u_N = φ_N ∘ κ_N : LΦ^* N ⟶ N` of a Weil datum `φ_N : Lg^* N ⟶ N`, for a comparison
`κ : LΦ^* ⟶ Lg^*` of the pullbacks along the scheme Frobenius `Φ` and the geometric-Galois
automorphism `g`. -/
noncomputable def schemeFrobeniusWeilDatum
    (κ : L((F)^*[ModuleCat.{u + 1} Λ]) ⟶ L((g)^*[ModuleCat.{u + 1} Λ]))
    {N : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N) :
    (L((F)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N :=
  κ.app N ≫ φ

/-- A morphism of Weil objects for the geometric-Galois data is one for their scheme-Frobenius
forms (`AlgebraicGeometry.Etale.schemeFrobeniusWeilDatum`). -/
lemma IsWeilMorphism.schemeFrobeniusWeilDatum
    (κ : L((F)^*[ModuleCat.{u + 1} Λ]) ⟶ L((g)^*[ModuleCat.{u + 1} Λ]))
    {M N : DerivedCategoryModule Λ X} {φM : (L((g)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M}
    {φN : (L((g)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N} {v : M ⟶ N}
    (hv : IsWeilMorphism g φM φN v) :
    IsWeilMorphism F (schemeFrobeniusWeilDatum κ φM) (schemeFrobeniusWeilDatum κ φN) v := by
  unfold IsWeilMorphism Etale.schemeFrobeniusWeilDatum at *
  rw [← Category.assoc, ← κ.naturality, Category.assoc, hv, Category.assoc]

end SchemeFrobenius

end Etale

end AlgebraicGeometry
