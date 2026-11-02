/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteBundleSectionAdjointScalar
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalNormalBundlePresentationScalar
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalVectorPresentationNormalization

/-! Transport of the ordinary bundle-section square through the published
pro-etale presentations.

The ordinary equation is the output of finite bundle-section scalar compatibility;
this statement packages the remaining presentation, counit and naturality paste.
(blueprint: lem-pur-finite-diagonal-vector-reduction-presentation-transport). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

private theorem fdpt_inverseSquare {C D : Type*} [Category C] [Category D]
    (S : C ⥤ D) {L H : C} {L' H' : D} (a : L ≅ H) (a' : L' ≅ H')
    (q : S.obj H ⟶ H') (t : S.obj L ⟶ L')
    (h : S.map a.hom ≫ q = t ≫ a'.hom) :
    S.map a.inv ≫ t = q ≫ a'.inv := by
  calc
    S.map a.inv ≫ t = S.map a.inv ≫ (t ≫ a'.hom) ≫ a'.inv := by
      simp only [Category.assoc, a'.hom_inv_id, Category.comp_id]
    _ = S.map a.inv ≫ (S.map a.hom ≫ q) ≫ a'.inv := by rw [h]
    _ = q ≫ a'.inv := by
      simpa only [Category.assoc, Functor.mapIso_inv, Functor.mapIso_hom] using
        congrArg (fun k ↦ k ≫ a'.inv) ((S.mapIso a).inv_hom_id_assoc q)

private theorem fdpt_realizeSquare {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {C H : Etale.DerivedCategoryModule A T}
    {C' H' : Etale.DerivedCategoryModule B T}
    (δ : C ⟶ H) (δ' : C' ⟶ H')
    (qC : (ordinaryScalar φ T).obj C ⟶ C')
    (qH : (ordinaryScalar φ T).obj H ⟶ H')
    (h : (ordinaryScalar φ T).map δ ≫ qH = qC ≫ δ') :
    (proScalar φ T).map ((comparison A T).map δ) ≫ realize φ T qH =
      realize φ T qC ≫ (comparison B T).map δ' := by
  unfold realize
  dsimp only [proScalar, comparison, ordinaryScalar] at *
  have hn := (ProEtale.pbcComparisonReduction T φ).hom.naturality δ
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, h,
    Functor.map_comp, Category.assoc]

private theorem fdpt_presentSourceSquare {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {C H : Etale.DerivedCategoryModule A T}
    {C' H' : Etale.DerivedCategoryModule B T}
    {K : proCategory A T} {K' : proCategory B T}
    (a : K ≅ (comparison A T).obj C) (a' : K' ≅ (comparison B T).obj C')
    (δ : C ⟶ H) (δ' : C' ⟶ H')
    (qC : (ordinaryScalar φ T).obj C ⟶ C')
    (qH : (ordinaryScalar φ T).obj H ⟶ H')
    (h : (ordinaryScalar φ T).map δ ≫ qH = qC ≫ δ') :
    (proScalar φ T).map (a.hom ≫ (comparison A T).map δ) ≫ realize φ T qH =
      presented φ T a a' qC ≫ (a'.hom ≫ (comparison B T).map δ') := by
  unfold presented
  rw [Functor.map_comp, Category.assoc, fdpt_realizeSquare φ T δ δ' qC qH h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The ordinary bundle-section scalar equation yields the displayed pro-etale
diagonal vector reduction after expanding the canonical presentations.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity proof Steps 2--4.
Proof: by `finiteDiagonalVectorPresentationNormalization` at both coefficient rings,
`vectorFactor` is `normalBundleComparison` followed by the comparison image of the
inverse zero-section integration adjunct `a_R⁻¹`. The adjuncts `a_A`, `a_B` are
isomorphisms (`bundleAdjoint_isIso`); cancelling them in `hcore` gives
`Q(a_A⁻¹) ≫ r_d = q ≫ a_B⁻¹` with `r_d = (e.tensorPower d).hom`, and naturality of
`pbcComparisonReduction` carries this square through `realize`. The ordinary
normal-cone-to-bundle square `finiteDiagonalNormalBundlePresentationScalar`, carried
through `pbcComparisonReduction` and the inverse `normalComparison` pair of
`presented`, identifies `normalSectionMap` followed by the `B`-level normal-bundle
comparison with the scalar image of the `A`-level one followed by `realize q`.
Pasting the two squares and reassociating gives the displayed equation; `d = 0` and
`m = n` are included.
(blueprint: lem-pur-finite-diagonal-vector-reduction-presentation-transport). -/
theorem finiteDiagonalPresentationTransport
    (e : CoefficientLineComparison (quotient P m hm hmn)
      P.diagonalExponent (P.finiteReductionSetting m hm).diagonalExponent
      P.diagonalExponent_annihilates
      (P.finiteReductionSetting m hm).diagonalExponent_annihilates X)
    : letI := P.noetherian (f ≫ aY)
      letI := (chartDiagonalNormalBundle d f).1
      (hcore :
      (ordinaryScalar (quotient P m hm hmn) X).map
          (Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
            P.diagonalExponent (by
              dsimp only [PurityFiniteSetting.diagonalExponent]
              exact pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
            P.diagonalExponent_annihilates X
            (P.diagonalExponent_isUnit (f ≫ aY)) d
            (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)) ≫
        DncCoefficientTransport.sectionMap (quotient P m hm hmn)
          (VectorBundleZeroSection.π X d
            (ConormalGradedAlgebra.piece (pullback.diagonal f) 1))
          (VectorBundleZeroSection.zero X d
            (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)) =
      (e.tensorPower d).hom ≫
        Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
          (P.finiteReductionSetting m hm).diagonalExponent (by
            dsimp only [PurityFiniteSetting.diagonalExponent]
            exact pow_pos P.coefficients.prime.out.pos m)
          (P.finiteReductionSetting m hm).Coefficient
          (P.finiteReductionSetting m hm).diagonalExponent_annihilates X
          ((P.finiteReductionSetting m hm).diagonalExponent_isUnit (f ≫ aY)) d
          (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)) →
      (proScalar (quotient P m hm hmn) X).map (vectorFactor P d f aY).hom ≫
        proTwistMap d e =
      normalSectionMap P m hm hmn d f aY ≫
        (vectorFactor (P.finiteReductionSetting m hm) d f aY).hom := by
  let _ := P.noetherian (f ≫ aY)
  let _ := (chartDiagonalNormalBundle d f).1
  intro hcore
  let Q := P.finiteReductionSetting m hm
  let φ := quotient P m hm hmn
  let E := ConormalGradedAlgebra.piece (pullback.diagonal f) 1
  let b : Etale.affineLinearBaseCoefficient P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates X d ⟶
      Etale.sectionInvariant P.Coefficient (VectorBundleZeroSection.π X d E)
        (VectorBundleZeroSection.zero X d E) :=
    Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
    P.diagonalExponent (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit (f ≫ aY)) d E
  let b' : Etale.affineLinearBaseCoefficient Q.Coefficient Q.diagonalExponent
      Q.diagonalExponent_annihilates X d ⟶
      Etale.sectionInvariant Q.Coefficient (VectorBundleZeroSection.π X d E)
        (VectorBundleZeroSection.zero X d E) :=
    Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
    Q.diagonalExponent (pow_pos Q.coefficients.prime.out.pos Q.level) Q.Coefficient
    Q.diagonalExponent_annihilates X (Q.diagonalExponent_isUnit (f ≫ aY)) d E
  let q := DncCoefficientTransport.sectionMap φ
    (VectorBundleZeroSection.π X d E) (VectorBundleZeroSection.zero X d E)
  let τ : (ordinaryScalar φ X).obj
      (Etale.affineLinearBaseCoefficient P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates X d) ⟶
      Etale.affineLinearBaseCoefficient Q.Coefficient Q.diagonalExponent
        Q.diagonalExponent_annihilates X d := (e.tensorPower d).hom
  let S := ordinaryScalar φ X
  have hb : IsIso b := (Etale.FiniteRingSectionDeformation.bundleAdjoint_isIso
    P.diagonalExponent (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit (f ≫ aY)) d E).2
  have hb' : IsIso b' := (Etale.FiniteRingSectionDeformation.bundleAdjoint_isIso
    Q.diagonalExponent (pow_pos Q.coefficients.prime.out.pos Q.level) Q.Coefficient
    Q.diagonalExponent_annihilates X (Q.diagonalExponent_isUnit (f ≫ aY)) d E).2
  let eb := @asIso _ _ _ _ b hb
  let eb' := @asIso _ _ _ _ b' hb'
  have hc : S.map eb.hom ≫ q = τ ≫ eb'.hom := hcore
  have hi : S.map eb.inv ≫ τ = q ≫ eb'.inv :=
    fdpt_inverseSquare S eb eb' q τ hc
  have hp := fdpt_realizeSquare φ X (eb.inv) (eb'.inv) q τ hi
  have ho := finiteDiagonalNormalBundlePresentationScalar P m hm hmn d f aY
  have hn : (proScalar φ X).map
      (ChartFactors.normalBundleComparison P d f aY
        (Etale.canonicalEtaleCompactSupportNormalization P.Coefficient)).hom ≫
      realize φ X q =
    normalSectionMap P m hm hmn d f aY ≫
      (ChartFactors.normalBundleComparison Q d f aY
        (Etale.canonicalEtaleCompactSupportNormalization Q.Coefficient)).hom := by
    unfold ChartFactors.normalBundleComparison normalSectionMap
    exact fdpt_presentSourceSquare φ X
        (Dnc.normalComparison P d (pullback.fst f f) (f ≫ aY)
          (pullback.diagonal f) (pullback.diagonal_fst f))
        (Dnc.normalComparison Q d (pullback.fst f f) (f ≫ aY)
          (pullback.diagonal f) (pullback.diagonal_fst f)) _ _ _ _ ho
  rw [finiteDiagonalVectorPresentationNormalization P d f aY,
    finiteDiagonalVectorPresentationNormalization Q d f aY]
  unfold realize at hp hn
  change (proScalar φ X).map
      ((ChartFactors.normalBundleComparison P d f aY _).hom ≫
        (comparison P.Coefficient X).map (eb.inv)) ≫
      (ProEtale.pbcComparisonReduction X φ).hom.app _ ≫
        (comparison Q.Coefficient X).map τ =
    normalSectionMap P m hm hmn d f aY ≫
      (ChartFactors.normalBundleComparison Q d f aY _).hom ≫
        (comparison Q.Coefficient X).map (eb'.inv)
  rw [Functor.map_comp, Category.assoc, hp, ← Category.assoc]
  erw [hn]
  exact Category.assoc _ _ _

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
