/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRationalRealizationData
import all WeilConjectures.AlgebraicGeometry.CompletedPullbackReductionCoherence
import all WeilConjectures.AlgebraicGeometry.PbcScalarComposition

/-! # Normalized continuous tensor coherence

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-per-continuous-integral-scalar-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (F : Type u) [Field F] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] F]

variable (G : Type u) [Field G] [Algebra ℚ_[l] G]
  [FiniteDimensional ℚ_[l] G]

/-- The scalar associator equation on an integral representative.
Source: BS 6.8.14(2), Remark 6.8.15; Stacks 0D6D
(blueprint: lem-per-continuous-integral-scalar-tower).

Proof: substitute the three integral_normalization equations, solving for each
comparison component by the inverse integral comparison and inverse reduction
normalization. Naturality moves the intermediate integral comparison past derived
scalar extension; its inverse cancels. The prescribed raw scalar associator on
an integral representative is the rationalization of the integral scalar tensor
associator. Naturality of the integral comparison replaces its realized image by
that integral associator. The remaining diagram consists only of the canonical
reduction normalizations. On flat-term K-flat resolutions both routes flatten
three tensors to their ordered product; associativity of multiplication gives
equality, which descends through the computation counits. This proves the equation
without any assertion of naturality on arbitrary raw fraction morphisms. -/
theorem continuousIntegralScalarTower (i : E →ₐ[ℚ_[l]] F) (j : F →ₐ[ℚ_[l]] G)
    (X : Base.{u} l) (aE : At l E X) (aF : At l F X) (aG : At l G X)
    (bEF : FieldChange l E F i X aE aF) (bFG : FieldChange l F G j X aF aG)
    (bEG : FieldChange l E G (j.comp i) X aE aG)
    (hc : bEF.coefficient ≫ bFG.coefficient = bEG.coefficient)
    (K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) :
    aG.J.map (pbcRationalScalarCompComponent l E F G i j X.scheme
        X.dimension X.prime_unit
        ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K)).hom ≫
      bEG.comparison.hom.app
        ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
    bFG.comparison.hom.app
        ((pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit).obj
          ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K)) ≫
      (pbcDerivedExtend bFG.coefficient).map (bEF.comparison.hom.app
        ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K)) ≫
      (pbcReductionNormalization bEF.coefficient bFG.coefficient bEG.coefficient
        hc (aE.J.obj
          ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K))).hom :=
  by
    let iEF := pbcScalarCoefficientMap l E F i X.scheme
    let iFG := pbcScalarCoefficientMap l F G j X.scheme
    let iEG := pbcScalarCoefficientMap l E G (j.comp i) X.scheme
    let eE := aE.integralIso.hom ≫ aE.inclusion
    let eF := aF.integralIso.hom ≫ aF.inclusion
    let eG := aG.integralIso.hom ≫ aG.inclusion
    let f := bEF.coefficient
    let g := bFG.coefficient
    let h := bEG.coefficient
    let EF := eE ≫ f
    let FG := eF ≫ g
    let EG := eE ≫ h
    have hInt : iEF ≫ iFG = iEG := pbcScalarCoefficientMap_comp l E F G i j X.scheme
    have hEF : iEF ≫ eF = EF := bEF.square
    have hFG : iFG ≫ eG = FG := bFG.square
    have hEG : iEG ≫ eG = EG := bEG.square
    have hEFG : EF ≫ g = EG := by
      dsimp only [EF, EG]
      rw [Category.assoc, hc]
    have hiFG : iEF ≫ FG = EG := by
      dsimp only [FG]
      rw [← Category.assoc, hEF, hEFG]
    have h₁ := norm_assoc iEF iFG eG iEG FG EG hInt hFG hiFG hEG K.obj
    have h₂ := norm_assoc iEF eF g EF FG EG hEF rfl hiFG hEFG K.obj
    have h₃ := norm_assoc eE f g EF h EG rfl hc rfl hEFG K.obj
    let Q := pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)
    let K₀ := Q.obj K
    let IE : aE.J.obj K₀ ⟶ (pbcDerivedExtend eE).obj K.obj := aE.integral.hom.app K
    let u := (pbcDerivedExtend h).map IE ≫
      (pbcReductionNormalization eE h EG rfl K.obj).hom
    have hu : (pbcReductionNormalization f g h hc (aE.J.obj K₀)).hom ≫ u =
        (pbcDerivedExtend g).map
          ((pbcDerivedExtend f).map IE ≫
            (pbcReductionNormalization eE f EF rfl K.obj).hom) ≫
          (pbcReductionNormalization EF g EG hEFG K.obj).hom := by
      dsimp only [u]
      rw [← Category.assoc, ← norm_natural f g h hc IE, Category.assoc, ← h₃,
        ← Category.assoc, ← Functor.map_comp]
    let KF := (pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj K
    let KFG := (pbcEmbeddingIntegralTensor l F G j X.scheme X.dimension X.prime_unit).obj KF
    let KG := (pbcEmbeddingIntegralTensor l E G (j.comp i) X.scheme
      X.dimension X.prime_unit).obj K
    let L := (pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit).obj K₀
    let rInt := ObjectProperty.isoMk
      (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l G))
      (X := KFG) (Y := KG)
      ((pbcAmbientScalarComp l E F G i j X.scheme).app K.obj)
    have hR : (pbcRationalScalarCompComponent l E F G i j X.scheme
        X.dimension X.prime_unit K₀).hom =
        (pbcRationalization X.scheme (pbcIntegralDatum l G) (pbcUniformizer l G)).map
          rInt.hom := by
      unfold pbcRationalScalarCompComponent
      rfl
    have hRI : rInt.hom.hom =
        (pbcReductionNormalization iEF iFG iEG hInt K.obj).hom := by
      unfold rInt pbcAmbientScalarComp
      rfl
    have hJ := aG.integral.hom.naturality rInt.hom
    dsimp only [Functor.comp_map, ObjectProperty.ι_map] at hJ
    rw [hRI] at hJ
    apply (cancel_mono u).1
    change (aG.J.map (pbcRationalScalarCompComponent l E F G i j X.scheme
      X.dimension X.prime_unit K₀).hom ≫ bEG.comparison.hom.app K₀) ≫ u =
      (bFG.comparison.hom.app L ≫ (pbcDerivedExtend g).map
        (bEF.comparison.hom.app K₀) ≫
          (pbcReductionNormalization f g h hc (aE.J.obj K₀)).hom) ≫ u
    calc
      _ = aG.integral.hom.app KFG ≫
          (pbcDerivedExtend eG).map
            (pbcReductionNormalization iEF iFG iEG hInt K.obj).hom ≫
            (pbcReductionNormalization iEG eG EG hEG K.obj).hom := by
        rw [Category.assoc]
        change aG.J.map (pbcRationalScalarCompComponent l E F G i j X.scheme
          X.dimension X.prime_unit K₀).hom ≫
          (bEG.comparison.hom.app K₀ ≫ (pbcDerivedExtend h).map IE ≫
            (pbcReductionNormalization eE h EG rfl K.obj).hom) = _
        have hn := congrArg (fun z ↦ aG.J.map
          (pbcRationalScalarCompComponent l E F G i j X.scheme
            X.dimension X.prime_unit K₀).hom ≫ z) (bEG.integral_normalization K)
        calc
          _ = aG.J.map (pbcRationalScalarCompComponent l E F G i j X.scheme
                X.dimension X.prime_unit K₀).hom ≫
              (aG.integral.hom.app KG ≫
                (pbcReductionNormalization iEG eG EG hEG K.obj).hom) := by
            exact hn
          _ = _ := by rw [hR, ← Category.assoc, hJ, Category.assoc]
      _ = aG.integral.hom.app KFG ≫
          (pbcReductionNormalization iFG eG FG hFG
            ((pbcDerivedExtend iEF).obj K.obj)).hom ≫
          (pbcReductionNormalization iEF FG EG hiFG K.obj).hom := by
        rw [h₁]
      _ = bFG.comparison.hom.app L ≫ (pbcDerivedExtend g).map
          (aF.integral.hom.app
            ((pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj K)) ≫
          (pbcReductionNormalization eF g FG rfl
            ((pbcDerivedExtend iEF).obj K.obj)).hom ≫
          (pbcReductionNormalization iEF FG EG hiFG K.obj).hom := by
        have hn := bFG.integral_normalization
          ((pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj K)
        have hn' := congrArg (fun z ↦ z ≫
          (pbcReductionNormalization iEF FG EG hiFG K.obj).hom) hn.symm
        simp only [Category.assoc] at hn' ⊢
        exact hn'
      _ = bFG.comparison.hom.app L ≫ (pbcDerivedExtend g).map
          (aF.integral.hom.app
            ((pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj K)) ≫
          (pbcDerivedExtend g).map
            ((pbcReductionNormalization iEF eF EF hEF K.obj).hom) ≫
          (pbcReductionNormalization EF g EG hEFG K.obj).hom := by
        rw [← h₂]
      _ = bFG.comparison.hom.app L ≫ (pbcDerivedExtend g).map
          (bEF.comparison.hom.app K₀) ≫ (pbcDerivedExtend g).map
          ((pbcDerivedExtend f).map IE ≫
            (pbcReductionNormalization eE f EF rfl K.obj).hom) ≫
          (pbcReductionNormalization EF g EG hEFG K.obj).hom := by
        have hn := congrArg ((pbcDerivedExtend g).map) (bEF.integral_normalization K)
        have hn' := congrArg (fun z ↦ bFG.comparison.hom.app
          ((pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit).obj K₀) ≫
            z ≫ (pbcReductionNormalization EF g EG hEFG K.obj).hom) hn.symm
        simp only [Functor.map_comp, Category.assoc] at hn' ⊢
        exact hn'
      _ = _ := by
        simp only [Category.assoc]
        rw [hu]

end AlgebraicGeometry.Scheme.ContinuousRational
