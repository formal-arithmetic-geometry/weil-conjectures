/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteBundleSectionAdjointBaseChange

/-! # Normal-cone integration and arbitrary base change

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-purity-bc,
sk-prop-sp-purity-bc-factors.proof.md, proof (1).
(blueprint: lem-sp-finite-section-integrated-specialization-integration-factor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] CategoryTheory.catToReflQuiver Scheme.instCategory
  Scheme.Modules
  ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
attribute [local instance 20002] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
-- Use the localization instances already cached by the ordinary inverse image.
set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13
attribute [local irreducible] upperStar lowerStar etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory
  VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  leftDerivedUpperStarComp leftDerivedUpperStarCompSectionIso
  rightDerivedLowerShriek rightDerivedUpperShriek rightDerivedUpperShriekAdjunction
  vectorBundleIntegration

end AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem section_map_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    (f : X ⟶ Y) (f' : X' ⟶ Y') (f'' : X'' ⟶ Y'')
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (v : Y' ⟶ Y) (w : Y'' ⟶ Y') (z : Y'' ⟶ Y) (hz : z = w ≫ v)
    (r : X' ⟶ X) (r' : X'' ⟶ X') (r'' : X'' ⟶ X) (hr : r'' = r' ≫ r)
    (sq : IsPullback r f' f v) (sq' : IsPullback r' f'' f' w)
    (sq'' : IsPullback r'' f'' f z)
    (s : Y ⟶ X) (s' : Y' ⟶ X') (s'' : Y'' ⟶ X'')
    (h : s' ≫ r = v ≫ s) (h' : s'' ≫ r' = w ≫ s')
    (h'' : s'' ≫ r'' = z ≫ s) :
    NoetherianSectionSpecialization.sectionMap A f f'' z r'' sq'' s s'' h'' =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v z hz).hom.app
        (sectionInvariant A f s) ≫
      (ordinaryFinitePullback A w).map
        (NoetherianSectionSpecialization.sectionMap A f f' v r sq s s' h) ≫
      NoetherianSectionSpecialization.sectionMap A f' f'' w r' sq' s' s'' h' := by
  subst z
  subst r''
  have hd := dualizing_base_comp A sq sq'
  have hp := section_pullback_comp A v w s s' s'' r r' h.symm h'.symm h''.symm
    (dualizingComplex A f)
  unfold NoetherianSectionSpecialization.sectionMap sectionInvariant
  rw [hd]
  simp only [sectionCoherencePullbackIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom] at hp
  simp only [Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv]
  erw [reassoc_of% hp]
  have hn := ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w s').symm ≪≫
    leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s'' r'
      (w ≫ s') h'.symm).hom.naturality (dualizingComplexBaseChangeMap A sq)
  simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc] at hn
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hn]
  rfl

private theorem invert_section_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y L : C} {X' Y' L' : D}
    (n : X ⟶ Y) (n' : X' ⟶ Y') [IsIso n] [IsIso n']
    (o : X ≅ L) (o' : X' ≅ L')
    (v : F.obj X ⟶ X') (w : F.obj Y ⟶ Y') (c : F.obj L ⟶ L')
    (hn : F.map n ≫ w = v ≫ n')
    (ho : F.map o.inv ≫ v = c ≫ o'.inv) :
    F.map (inv n ≫ o.hom) ≫ c = w ≫ inv n' ≫ o'.hom := by
  apply (cancel_epi (F.map n)).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc, IsIso.hom_inv_id, F.map_id, Category.id_comp]
  rw [reassoc_of% hn, IsIso.hom_inv_id_assoc]
  apply (cancel_epi (F.map o.inv)).1
  rw [← F.map_comp_assoc, o.inv_hom_id, F.map_id, Category.id_comp]
  rw [reassoc_of% ho, o'.inv_hom_id, Category.comp_id]

/-- The inverse-normal-bundle integration square for the normal exchange.
Source: Kummer-normalized vector integration trace base-change.
(blueprint: lem-sp-finite-section-integrated-specialization-integration-factor).

Transpose the scalar trace square and restrict to zero. Conjugate the given normal
exchange by the two cone-to-bundle isomorphisms. Section exchange transitivity and
pullback unit coherence identify its two factorizations. Cancel the normal section
maps and the integration adjuncts to obtain the inverse-orientation square. -/
theorem normalExchange_integration
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S V' S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (d : ℕ) (g : V ⟶ S) (g' : V' ⟶ S')
    [SmoothOfRelativeDimension d g] [SmoothOfRelativeDimension d g']
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    [IsSeparated g'] [QuasiCompact g'] [HasCompactification g']
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    [FiniteRingSectionDeformation.Geometry d g s]
    [FiniteRingSectionDeformation.Geometry d g' s']
    (hs : s ≫ g = 𝟙 S) (hs' : s' ≫ g' = 𝟙 S')
    (b : S' ⟶ S) (q : V' ⟶ V) (cart : IsPullback q g' g b)
    (hsec : s' ≫ q = b ≫ s)
    (sq : IsPullback
      ((reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s).hom)
      (Scheme.Hom.normalConeProj g s)
      (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)) (𝟙 S))
    (sq' : IsPullback
      ((reesConeComparison s' ≪≫ FiniteRingSectionDeformation.coneBundleIso d g' s').hom)
      (Scheme.Hom.normalConeProj g' s')
      (VectorBundleZeroSection.π S' d (ConormalGradedAlgebra.piece s' 1)) (𝟙 S'))
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤)))
    (ν : s'.ker.normalCone ⟶ s.ker.normalCone)
    (sqν : IsPullback ν (Scheme.Hom.normalConeProj g' s')
      (Scheme.Hom.normalConeProj g s) b)
    (hzero : (Scheme.Hom.normalConeZeroSection s') ≫ ν = b ≫ (Scheme.Hom.normalConeZeroSection s))
    (hn : IsIso (normalSectionMap A d g s hs sq))
    (hn' : IsIso (normalSectionMap A d g' s' hs' sq')) :
    (ordinaryFinitePullback A b).map
        ((@inv _ _ _ _ (normalSectionMap A d g s hs sq) hn) ≫
          (FiniteRingSectionDeformation.bundleOrientation N hN A hA S hS d
            (ConormalGradedAlgebra.piece s 1)).hom) ≫
        (vectorIntegrationBaseCoefficientPullback A N hA
          (WeilConjectures.PurityFiniteSetting.purityTwistTransport A N hN hA) b hS d).hom =
      NoetherianSectionSpecialization.sectionMap A
        (Scheme.Hom.normalConeProj g s) (Scheme.Hom.normalConeProj g' s') b ν sqν
        (Scheme.Hom.normalConeZeroSection s) (Scheme.Hom.normalConeZeroSection s') hzero ≫
        (@inv _ _ _ _ (normalSectionMap A d g' s' hs' sq') hn') ≫
        (FiniteRingSectionDeformation.bundleOrientation N hN A hA S' hS' d
          (ConormalGradedAlgebra.piece s' 1)).hom := by
  have _ := cart
  have _ := hsec
  let M := ConormalGradedAlgebra.piece s 1
  let M' := ConormalGradedAlgebra.piece s' 1
  let π := VectorBundleZeroSection.π S d M
  let π' := VectorBundleZeroSection.π S' d M'
  let z := VectorBundleZeroSection.zero S d M
  let z' := VectorBundleZeroSection.zero S' d M'
  let p := Scheme.Hom.normalConeProj g s
  let p' := Scheme.Hom.normalConeProj g' s'
  let e := reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s
  let e' := reesConeComparison s' ≪≫ FiniteRingSectionDeformation.coneBundleIso d g' s'
  have he : e.hom ≫ π = p := by simpa only [Category.comp_id] using sq.w
  have he' : e'.hom ≫ π' = p' := by simpa only [Category.comp_id] using sq'.w
  have hz : (Scheme.Hom.normalConeZeroSection s) ≫ e.hom = z := by
    dsimp only [e, Iso.trans_hom]
    rw [← Category.assoc, (reesConeComparison_spec s).2.1,
      (FiniteRingSectionDeformation.coneBundleIso_spec d g s hs).2]
  have hz' : (Scheme.Hom.normalConeZeroSection s') ≫ e'.hom = z' := by
    dsimp only [e', Iso.trans_hom]
    rw [← Category.assoc, (reesConeComparison_spec s').2.1,
      (FiniteRingSectionDeformation.coneBundleIso_spec d g' s' hs').2]
  let v := e'.inv ≫ ν ≫ e.hom
  have hv : e'.hom ≫ v = ν ≫ e.hom := by simp only [v, Iso.hom_inv_id_assoc]
  have sqv : IsPullback v π' π b := by
    apply sqν.of_iso e' e (Iso.refl _) (Iso.refl _)
    · exact hv.symm
    · simpa only [Iso.refl_hom, Category.comp_id] using he'.symm
    · simpa only [Iso.refl_hom, Category.comp_id] using he.symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  have hzv : z' ≫ v = b ≫ z := by
    rw [← hz', Category.assoc, hv, ← Category.assoc, hzero, Category.assoc, hz]
  have houter : (Scheme.Hom.normalConeZeroSection s') ≫ (ν ≫ e.hom) = b ≫ z := by
    rw [← Category.assoc, hzero, Category.assoc, hz]
  have sqouter : IsPullback (ν ≫ e.hom) p' π b := by
    simpa only [Category.comp_id] using sqν.paste_horiz sq
  let n := normalSectionMap A d g s hs sq
  let n' := normalSectionMap A d g' s' hs' sq'
  let mv := NoetherianSectionSpecialization.sectionMap A π π' b v sqv z z' hzv
  let mν := NoetherianSectionSpecialization.sectionMap A p p' b ν sqν
    (Scheme.Hom.normalConeZeroSection s) (Scheme.Hom.normalConeZeroSection s') hzero
  have hcomp₁ := section_map_comp A π p p' (𝟙 S) b b
    (Category.comp_id b).symm e.hom ν (ν ≫ e.hom) rfl sq sqν sqouter
    z (Scheme.Hom.normalConeZeroSection s) (Scheme.Hom.normalConeZeroSection s')
    (hz.trans (Category.id_comp z).symm) hzero houter
  have hcomp₂ := section_map_comp A π π' p' b (𝟙 S') b
    (Category.id_comp b).symm v e'.hom (ν ≫ e.hom) hv.symm sqv sq' sqouter
    z z' (Scheme.Hom.normalConeZeroSection s') hzv
    (hz'.trans (Category.id_comp z').symm) houter
  have hu₁ : (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b (𝟙 S) b
      (Category.comp_id b).symm).hom.app (sectionInvariant A π z) =
      (ordinaryFinitePullback A b).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app
          (sectionInvariant A π z)) := by
    apply (cancel_mono ((ordinaryFinitePullback A b).map
      ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app _))).1
    dsimp only [ordinaryFinitePullback]
    erw [leftDerivedUpperStarComp_id_right_hom_app]
    erw [← Functor.map_comp, Iso.inv_hom_id_app]
    exact ((ordinaryFinitePullback A b).map_id _).symm
  have hu₂ : (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 S') b b
      (Category.id_comp b).symm).hom.app (sectionInvariant A π z) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S').inv.app
        ((ordinaryFinitePullback A b).obj (sectionInvariant A π z)) := by
    apply (cancel_mono ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S').hom.app _)).1
    dsimp only [ordinaryFinitePullback]
    erw [leftDerivedUpperStarComp_id_left_hom_app]
    erw [Iso.inv_hom_id_app]
    rfl
  have hnormal : (ordinaryFinitePullback A b).map n ≫ mν = mv ≫ n' := by
    rw [hu₁] at hcomp₁
    rw [hu₂] at hcomp₂
    have hi := (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S').inv.naturality mv
    dsimp only [Functor.id_map] at hi
    dsimp only [ordinaryFinitePullback] at hcomp₂ hi
    erw [← reassoc_of% hi] at hcomp₂
    dsimp only [n, n', normalSectionMap, sectionInvariant, dualizingComplex,
      FiniteRingSectionDeformation.bundleRight, ordinaryFinitePullback,
      M, M', π, π', z, z', p, p', e, e', mv, mν] at hcomp₁ hcomp₂ ⊢
    simp only [Functor.map_comp, Category.assoc] at hcomp₁ hcomp₂ ⊢
    exact hcomp₁.symm.trans hcomp₂
  let o := FiniteRingSectionDeformation.bundleOrientation N hN A hA S hS d M
  let o' := FiniteRingSectionDeformation.bundleOrientation N hN A hA S' hS' d M'
  have hb := FiniteRingSectionDeformation.bundleSectionAdjoint_baseChange
    A N hN hA hS hS' d M M' b v sqv hzv
  have ho : (ordinaryFinitePullback A b).map o.inv ≫ mv =
      (vectorIntegrationBaseCoefficientPullback A N hA
        (WeilConjectures.PurityFiniteSetting.purityTwistTransport A N hN hA) b hS d).hom ≫
      o'.inv := by
    exact hb
  let : IsIso n := hn
  let : IsIso n' := hn'
  exact invert_section_square (ordinaryFinitePullback A b) n n' o o' mv mν _ hnormal ho

end AlgebraicGeometry.Etale.FiniteSmoothPurity
