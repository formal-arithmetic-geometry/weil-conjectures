/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionSpecializationScalar

/-! # Coefficient reduction of the normalized diagonal DNC factor

(blueprint: lem-pur-finite-diagonal-dnc-reduction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Etale.upperStar ProEtale.upperStar
  Etale.rightDerivedUpperShriek

private theorem transportSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (S : C ⥤ D) (T : E ⥤ F) (R : C ⥤ E) (Q : D ⥤ F)
    (ξ : S ⋙ Q ≅ R ⋙ T)
    {C₁ C₂ : C} {E₁ E₂ : E} {D₁ D₂ : D} {F₁ F₂ : F}
    (a : D₁ ≅ S.obj C₁) (b : D₂ ≅ S.obj C₂)
    (a' : F₁ ≅ T.obj E₁) (b' : F₂ ≅ T.obj E₂)
    (δ : C₁ ⟶ C₂) (δ' : E₁ ⟶ E₂)
    (qC : R.obj C₁ ⟶ E₁) (qH : R.obj C₂ ⟶ E₂)
    (h : R.map δ ≫ qH = qC ≫ δ') :
    Q.map (a.hom ≫ S.map δ ≫ b.inv) ≫
        (Q.map b.hom ≫ (ξ.hom.app C₂ ≫ T.map qH) ≫ b'.inv) =
      (Q.map a.hom ≫ (ξ.hom.app C₁ ≫ T.map qC) ≫ a'.inv) ≫
        (a'.hom ≫ T.map δ' ≫ b'.inv) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Q.map_comp_assoc b.inv b.hom, b.inv_hom_id, Q.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_assoc]
  have hn := ξ.hom.naturality δ
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← T.map_comp_assoc, h, T.map_comp]
  simp only [Category.assoc]

private theorem presentedSquare {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {C H : Etale.DerivedCategoryModule A T} {C' H' : Etale.DerivedCategoryModule B T}
    {K L : proCategory A T} {K' L' : proCategory B T}
    (a : K ≅ (comparison A T).obj C) (b : L ≅ (comparison A T).obj H)
    (a' : K' ≅ (comparison B T).obj C') (b' : L' ≅ (comparison B T).obj H')
    (δ : C ⟶ H) (δ' : C' ⟶ H')
    (qC : (ordinaryScalar φ T).obj C ⟶ C')
    (qH : (ordinaryScalar φ T).obj H ⟶ H')
    (h : (ordinaryScalar φ T).map δ ≫ qH = qC ≫ δ') :
    (proScalar φ T).map (a.hom ≫ (comparison A T).map δ ≫ b.inv) ≫
        presented φ T b b' qH =
      presented φ T a a' qC ≫ (a'.hom ≫ (comparison B T).map δ' ≫ b'.inv) := by
  unfold presented realize
  exact transportSquare (comparison A T) (comparison B T)
    (ordinaryScalar φ T) (proScalar φ T) (ProEtale.pbcComparisonReduction T φ)
    a b a' b' δ δ' qC qH h

private theorem dncPresentation (P : PurityFiniteSetting.{u})
    {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    [LocallyOfFiniteType g]
    (aS : S ⟶ Spec (.of P.field.k)) [IsSeparated aS]
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (κ : Dnc.familyEtale P d g aS s hs ≅
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (Dnc.sourceEtale P d g aS s))
    (hκ : letI := Dnc.compactifiable P g aS
      letI := P.noetherian aS
      letI := Scheme.Hom.hasCompactification_deformationSpaceProj g s d hs
      Etale.NoetherianSectionSpecialization.Normalized P.Coefficient g s hs κ) :
    letI := Dnc.compactifiable P g aS
    letI := P.noetherian aS
    letI := Scheme.Hom.hasCompactification_deformationSpaceProj g s d hs
    letI := Dnc.normalCompactifiable P d g aS s hs
    letI := Dnc.normalQuasiCompact d g s hs
    ((Dnc.existsUnique_dncInvariance P d g aS s hs).exists.choose).hom =
      (Dnc.sourceComparison P d g aS s).hom ≫
        (comparison P.Coefficient S).map
          (Etale.NoetherianSectionSpecialization.specialization P.Coefficient g s κ) ≫
        (Dnc.normalComparison P d g aS s hs).inv := by
  classical
  have := P.noetherian aS
  have := Dnc.compactifiable P g aS
  have := Scheme.Hom.hasCompactification_deformationSpaceProj g s d hs
  have := Dnc.normalCompactifiable P d g aS s hs
  have := Dnc.normalQuasiCompact d g s hs
  let A := ModuleCat.{u + 1} P.Coefficient
  let a := (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  let i₁ := AffineSpace.oneSection (ULift.{u} (Fin 1)) S
  let i₀ := AffineSpace.zeroSection (ULift.{u} (Fin 1)) S
  let C := Dnc.sourceEtale P d g aS s
  let θ₁ := (Etale.upperStar A i₁).leftDerivedFunctor.mapIso κ ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso A i₁ a
      (AffineSpace.oneSection_comp_over _ S)).app C
  let θ₀ := (Etale.upperStar A i₀).leftDerivedFunctor.mapIso κ ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso A i₀ a
      (AffineSpace.zeroSection_comp_over _ S)).app C
  have h₁ : θ₁ = Dnc.fibreOne P d g aS s hs := by
    apply Iso.ext
    exact hκ
  let δ := θ₀.symm ≪≫ Dnc.fibreZero P d g aS s hs
  have hδ : δ.hom =
      Etale.NoetherianSectionSpecialization.specialization P.Coefficient g s κ := by
    unfold δ θ₀ Etale.NoetherianSectionSpecialization.specialization
      Dnc.fibreZero Dnc.sectionBaseChange Etale.NoetherianSectionSpecialization.atZero
      Etale.NoetherianSectionSpecialization.sectionMap
    dsimp only [Iso.trans, Iso.symm, Functor.mapIso, Iso.app, asIso]
    exact Category.assoc _ _ _
  let b := 𝟙 S
  let v := AffineSpace.map (ULift.{u} (Fin 1)) b
  let e := (Etale.upperStar A v).leftDerivedFunctor.mapIso κ ≪≫
    ((Etale.leftDerivedUpperStarComp A v a).app C).symm ≪≫
      (Etale.leftDerivedUpperStarComp A a b (v ≫ a)
        (AffineSpace.map_over b)).app C
  have r₁ := Etale.sectionRestrictionIso_restrict A b v
    (AffineSpace.oneSection_comp_map b) (AffineSpace.oneSection_comp_over _ S)
    (AffineSpace.map_over b) (AffineSpace.oneSection_comp_over _ S) κ
  have r₀ := Etale.sectionRestrictionIso_restrict A b v
    (AffineSpace.zeroSection_comp_map b) (AffineSpace.zeroSection_comp_over _ S)
    (AffineSpace.map_over b) (AffineSpace.zeroSection_comp_over _ S) κ
  change Etale.sectionRestrictionIso A b v _ _ θ₁ e = Iso.refl _ at r₁
  change Etale.sectionRestrictionIso A b v _ _ θ₀ e = Iso.refl _ at r₀
  rw [h₁] at r₁
  have hz : Dnc.fibreZero P d g aS s hs = θ₀ ≪≫ δ := by simp [δ]
  let α := (Dnc.existsUnique_dncInvariance P d g aS s hs).exists.choose
  have h := (Dnc.existsUnique_dncInvariance P d g aS s hs).exists.choose_spec
    S aS b (Category.id_comp aS) _ e
  change (ProEtale.upperStar A b).leftDerivedFunctor.mapIso α = _ at h
  rw [r₁, hz, Etale.sectionRestrictionIso_trans_left, r₀] at h
  simp only [Functor.mapIso_symm] at h
  let β := Dnc.sourceComparison P d g aS s ≪≫
    (comparison P.Coefficient S).mapIso δ ≪≫ (Dnc.normalComparison P d g aS s hs).symm
  let ν := comparison P.Coefficient S
  let Lb := (ProEtale.upperStar A b).leftDerivedFunctor
  let η : ν ⋙ Lb ≅ (Etale.upperStar A b).leftDerivedFunctor ⋙ ν :=
    Functor.isoWhiskerLeft ν (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A b) ≪≫
      ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso A b ≪≫
        Functor.isoWhiskerRight
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory A b).symm ν
  have hν := η.hom.naturality δ.hom
  change Lb.map (ν.map δ.hom) ≫ (Dnc.pullComparison P b _).hom =
    (Dnc.pullComparison P b _).hom ≫
      ν.map ((Etale.upperStar A b).leftDerivedFunctor.map δ.hom) at hν
  have hmap : (ProEtale.upperStar A b).leftDerivedFunctor.map α.hom =
      (ProEtale.upperStar A b).leftDerivedFunctor.map β.hom := by
    have hh := congrArg Iso.hom h
    dsimp only [Iso.trans, Iso.symm, Functor.mapIso, Iso.refl] at hh
    erw [Category.id_comp, Category.id_comp] at hh
    erw [← Category.assoc (Dnc.pullComparison P b C).hom
      (ν.map ((Etale.upperStar A b).leftDerivedFunctor.map δ.hom)), ← hν,
      Category.assoc, Iso.hom_inv_id_assoc] at hh
    dsimp only [β, Iso.trans, Iso.symm, Functor.mapIso]
    erw [Lb.map_comp (Dnc.sourceComparison P d g aS s).hom
        ((comparison P.Coefficient S).map δ.hom ≫ (Dnc.normalComparison P d g aS s hs).inv),
      Lb.map_comp ((comparison P.Coefficient S).map δ.hom)
        (Dnc.normalComparison P d g aS s hs).inv]
    exact hh
  have nα := (ProEtale.leftDerivedUpperStarId A S).hom.naturality α.hom
  have nβ := (ProEtale.leftDerivedUpperStarId A S).hom.naturality β.hom
  simp only [Functor.id_map] at nα nβ
  rw [hmap] at nα
  have heq := (cancel_epi ((ProEtale.leftDerivedUpperStarId A S).hom.app _)).mp
    (nα.symm.trans nβ)
  dsimp only [β, Iso.trans, Iso.symm, Functor.mapIso] at heq
  rw [hδ] at heq
  exact heq

section Diagonal
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- Source: blueprint/latest, thm-pur-finite-reduction-of-purity proof Steps 3--4;
parent node proof Steps 6--7.
Proof: use centred etale coordinates near the diagonal. The support-restriction
and normal-coordinate maps are exceptional mates and hence commute with scalar
extension by pullback balancing and reduced-counit compatibility. The normal frame
maps the coefficient-independent class of y_i-x_i to d x_i. In every such chart,
conjugating the reduced DNC map by its two section coefficient comparisons has
identity standard reading: the original DNC map does, and both coordinate squares
commute. Coordinate normalization and uniqueness of DNC invariance therefore give
the DNC map at the reduced level. Etale locality glues the equality globally.
The empty coordinate frame gives the same argument when d=0.
(blueprint: lem-pur-finite-diagonal-dnc-reduction). -/
theorem diagonalDncReduction :
      (proScalar (quotient P m hm hmn) X).map (P.chartDiagonalDelta d f aY).hom ≫
        normalSectionMap P m hm hmn d f aY =
      diagonalSectionMap P m hm hmn d f aY ≫
        ((P.finiteReductionSetting m hm).chartDiagonalDelta d f aY).hom := by
  classical
  let Q := P.finiteReductionSetting m hm
  let φ := quotient P m hm hmn
  let g := pullback.fst f f
  let s := pullback.diagonal f
  have hs : s ≫ g = 𝟙 X := pullback.diagonal_fst f
  have := P.noetherian (f ≫ aY)
  have := Dnc.compactifiable P g (f ≫ aY)
  have := Etale.FiniteRingSectionDeformation.geometry d g s hs
  have := Dnc.invertibleExponent P (f ≫ aY)
  obtain ⟨N, hN, hP, hX⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := P.Coefficient) (X := X)
  have hQ : (N : Q.Coefficient) = 0 := by
    rw [← map_natCast φ, hP, map_zero]
  obtain ⟨κ, hκ, _⟩ := Etale.FiniteRingSectionDeformation.existsUnique_normalized
    N hN P.Coefficient hP hX d g s hs
  obtain ⟨κ', hκ', _⟩ := Etale.FiniteRingSectionDeformation.existsUnique_normalized
    N hN Q.Coefficient hQ hX d g s hs
  have hA := dncPresentation P d g (f ≫ aY) s hs κ hκ
  have hB := dncPresentation Q d g (f ≫ aY) s hs κ' hκ'
  have hscalar := finiteSectionSpecialization_scalar φ N hN hP d g s hs hX κ κ' hκ hκ'
  change (proScalar φ X).map _ ≫ _ = _ ≫ _
  change (P.chartDiagonalDelta d f aY).hom = _ at hA
  change (Q.chartDiagonalDelta d f aY).hom = _ at hB
  rw [hA, hB]
  unfold normalSectionMap diagonalSectionMap
  exact presentedSquare φ X
    (Dnc.sourceComparison P d g (f ≫ aY) s)
    (Dnc.normalComparison P d g (f ≫ aY) s hs)
    (Dnc.sourceComparison Q d g (f ≫ aY) s)
    (Dnc.normalComparison Q d g (f ≫ aY) s hs) _ _ _ _ hscalar

end Diagonal
end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
