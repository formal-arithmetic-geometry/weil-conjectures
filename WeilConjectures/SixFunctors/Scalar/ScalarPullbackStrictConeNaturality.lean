/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Scalar.ScalarPullbackStrictConeData
import WeilConjectures.SixFunctors.Scalar.ScalarPullbackStrictTowerConstruction
import WeilConjectures.SixFunctors.Finite.FiniteFreeScalarCochainProperties
import WeilConjectures.SixFunctors.Scalar.ScalarPullbackStrictCoherence
import WeilConjectures.SixFunctors.Scalar.ScalarPullbackUniqueDerivedDescent
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Assembly and derived descent of the normalized strict scalar pullback map -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
attribute [local implicit_reducible] integralOperationsRoos integralOperationsRoosFunctor
  integralOperationsPullbackComplexFunctor integralOperationsGoodLocalization
  integralOperationsPullbackOnGood
  Functor.mapHomologicalComplex CochainComplex.mappingCocone
  completedOrdinaryScalarComplex scalarPullbackSourceTower scalarPullbackRoosEnd
attribute [local instance 5000] integralTowerHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} W.ProEt :=
  essentiallySmallSelf.{u, t, t + 1} _

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} W

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} W

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

section ProductComparison
universe a b c d e f
open CochainComplex
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]

private noncomputable def coconeCoordinates {K L : CochainComplex A ℤ}
    (φ : K ⟶ L) (i : ℤ) :
    (mappingCocone φ).X i ≅ K.X i ⊞ L.X (i - 1) where
  hom := biprod.lift ((mappingCocone.fst φ).f i)
    ((mappingCocone.snd φ).v i (i - 1) (by omega))
  inv := biprod.desc ((mappingCocone.inl φ).v i i (by omega))
    ((mappingCocone.inr φ).1.v (i - 1) i (by omega))
  hom_inv_id := by simpa using mappingCocone.id_X φ i (i - 1) (by omega)
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

private theorem product_roos_isIso (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) : IsIso (scalarRoosMap F C) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let pc := piComparison G (fun n : ℕ ↦ C.obj (op n))
  have hpc : IsIso pc := by dsimp only [pc]; infer_instance
  obtain ⟨hf, hs⟩ := scalarRoosCoordinates F C
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hpcf (i : ℤ) : IsIso (pc.f i) := inferInstance
  have hi (i : ℤ) : IsIso ((scalarRoosMap F C).f i) := by
    let f : F.obj ((mappingCocone (scalarRoosBoundary C)).X i) ⟶
        (mappingCocone (scalarRoosBoundary (C ⋙ G))).X i := (scalarRoosMap F C).f i
    let : IsIso (pc.f i) := hpcf i
    let : IsIso (pc.f (i - 1)) := hpcf (i - 1)
    let eY := coconeCoordinates (scalarRoosBoundary C) i
    let eX := coconeCoordinates (scalarRoosBoundary (C ⋙ G)) i
    have he : F.map eY.hom ≫
        (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom =
        biprod.lift (F.map ((mappingCocone.fst (scalarRoosBoundary C)).f i))
          (F.map ((mappingCocone.snd (scalarRoosBoundary C)).v
            i (i - 1) (by omega))) :=
      biprod.map_lift_mapBiprod F _ _ _ _
    have hm : f ≫ eX.hom =
        F.map eY.hom ≫ (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
            ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom ≫
          biprod.map (pc.f i) (pc.f (i - 1)) := by
      rw [← Category.assoc, he]
      apply biprod.hom_ext
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
        simpa only [f, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
          using congrArg (fun z ↦ z.f i) hf
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
        exact hs i
    have : IsIso (f ≫ eX.hom) := by
      rw [hm]
      change IsIso (((F.mapIso eY) ≪≫
        F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1)) ≪≫
        biprod.mapIso (@asIso _ _ _ _ (pc.f i) (hpcf i))
          (@asIso _ _ _ _ (pc.f (i - 1)) (hpcf (i - 1)))).hom)
      infer_instance
    change IsIso f
    let : IsIso eX.hom := eX.isIso_hom
    exact IsIso.of_isIso_comp_right f eX.hom
  exact HomologicalComplex.Hom.isIso_of_components _

private def ProductRoosCoordinates {C : Type e} [Category.{f} C]
    (F : A ⥤ B) [F.Additive] (T : C ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ))
    (κ : (T ⋙ integralOperationsRoosFunctor) ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (T ⋙ (Functor.whiskeringRight _ _ _).obj (F.mapHomologicalComplex (.up ℤ))) ⋙
        integralOperationsRoosFunctor) : Prop :=
  ∀ (P : C) (i : ℤ),
    ((κ.hom.app P).f i ≫ (mappingCocone.fst
        (scalarRoosBoundary (T.obj P ⋙ F.mapHomologicalComplex (.up ℤ)))).f i =
      F.map ((mappingCocone.fst (scalarRoosBoundary (T.obj P))).f i) ≫
        (piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ (T.obj P).obj (op n))).f i) ∧
    ((κ.hom.app P).f i ≫ (mappingCocone.snd
        (scalarRoosBoundary (T.obj P ⋙ F.mapHomologicalComplex (.up ℤ)))).v
          i (i - 1) (by omega) =
      F.map ((mappingCocone.snd (scalarRoosBoundary (T.obj P))).v
          i (i - 1) (by omega)) ≫
        (piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ (T.obj P).obj (op n))).f (i - 1))

private theorem productRoosComparison_existsUnique {C : Type e} [Category.{f} C]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (T : C ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ)) :
    ∃! κ : (T ⋙ integralOperationsRoosFunctor) ⋙ F.mapHomologicalComplex (.up ℤ) ≅
        (T ⋙ (Functor.whiskeringRight _ _ _).obj (F.mapHomologicalComplex (.up ℤ))) ⋙
          integralOperationsRoosFunctor,
      ProductRoosCoordinates F T κ := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let κ : (T ⋙ integralOperationsRoosFunctor) ⋙ G ≅
      (T ⋙ (Functor.whiskeringRight _ _ _).obj G) ⋙ integralOperationsRoosFunctor :=
    NatIso.ofComponents (fun P ↦ by
      let := product_roos_isIso F (T.obj P)
      exact asIso (scalarRoosMap F (T.obj P))) (by
        intro P P' f
        exact scalarRoosNaturality F (T.map f))
  have hκ : ProductRoosCoordinates F T κ := by
    intro P i
    obtain ⟨hf, hs⟩ := scalarRoosCoordinates F (T.obj P)
    constructor
    · change (scalarRoosMap F (T.obj P)).f i ≫ _ = _
      simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
        using congrArg (fun f ↦ f.f i) hf
    · exact hs i
  refine ⟨κ, hκ, ?_⟩
  intro κ' hκ'
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  have hf := (hκ' P i).1.trans (hκ P i).1.symm
  have hs := (hκ' P i).2.trans (hκ P i).2.symm
  let φ := scalarRoosBoundary (T.obj P ⋙ G)
  let α : F.obj ((mappingCocone (scalarRoosBoundary (T.obj P))).X i) ⟶
      (mappingCocone φ).X i := (κ'.hom.app P).f i
  let β : F.obj ((mappingCocone (scalarRoosBoundary (T.obj P))).X i) ⟶
      (mappingCocone φ).X i := (κ.hom.app P).f i
  change α ≫ (mappingCocone.fst φ).f i = β ≫ (mappingCocone.fst φ).f i at hf
  change α ≫ (mappingCocone.snd φ).v i (i - 1) _ =
    β ≫ (mappingCocone.snd φ).v i (i - 1) _ at hs
  have hid := mappingCocone.id_X φ i (i - 1) (by omega)
  have h₁ := congrArg (fun z ↦ α ≫ z) hid
  have h₂ := congrArg (fun z ↦ β ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc, Category.comp_id] at h₁ h₂
  rw [hf, hs] at h₁
  exact h₁.symm.trans h₂
end ProductComparison

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory in
private theorem scalarPullbackCone_existsUnique
    {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    [PreservesLimitsOfShape (Discrete ℕ) (completedOrdinaryScalarExtension l E L ι X)] :
    ∃! κ : integralOperationsPullbackComplexFunctor l E g ⋙
        completedOrdinaryScalarComplex l E L ι X ≅
      scalarPullbackSourceTower l E L ι g ⋙ integralOperationsRoosFunctor,
      ScalarPullbackConeFormula l E L ι g κ := by
  let F := completedOrdinaryScalarExtension l E L ι X
  let T := integralOperationsPullbackTowerFunctor l E g
  obtain ⟨κ, hκ, hκu⟩ := productRoosComparison_existsUnique F T
  have hformula (κ' : integralOperationsPullbackComplexFunctor l E g ⋙
      completedOrdinaryScalarComplex l E L ι X ≅
      scalarPullbackSourceTower l E L ι g ⋙ integralOperationsRoosFunctor) :
      ScalarPullbackConeFormula l E L ι g κ' ↔ ProductRoosCoordinates F T κ' := by
    constructor <;> intro h P i <;> exact h P i
  refine ⟨κ, (hformula κ).2 hκ, ?_⟩
  intro κ' hκ'
  exact hκu κ' ((hformula κ').1 hκ')

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory in
/-- Strict scalar/pullback cone naturality, with unique normalized witnesses.
Source: Bhatt--Scholze 3.4.10, 3.5.1 and 6.5.9(4); Stacks 03EK, 014E, 06YS,
06YT, 0G7E and 04VG
(blueprint: lem-weil-scalar-pullback-strict-cone-naturality).
Proof:
1. The balanced strict-tower construction gives the unique level map with its
prescribed local generator equation, including both coefficient scalars.
2. Finite freeness gives countable-product preservation and exact ordinary scalar
extension. The universal derived scalar counit is therefore invertible on every
complex, including the pullback Roos complex without a K-flatness assumption on it.
3. Independent-universe change of rings preserves K-flatness and flat terms,
so ordinary scalar extension preserves the good representative subcategory.
4. Apply the additive Roos map to the pullback tower. In degree i its two cone
coordinates are the product comparison in degrees i and i-1. Both are invertible;
the binary-biproduct coordinate calculation makes the Roos map invertible.
Naturality assembles these maps into the normalized cone isomorphism.
5. The two coordinates jointly determine a cone map by mappingCocone.id_X.
Consequently the normalized cone isomorphism is unique.
6. Good complexes localize to the derived category. Compose the E-pullback
comparison, the X scalar counit and the localized strict cone map to obtain a.
The invertible Y scalar counit and L-pullback comparison form an isomorphism b.
Fully faithful precomposition with this localization descends a followed by b
inverse uniquely. Its component equation is exactly the asserted descent formula.
7. Assemble the level, cone and derived maps. Their three uniqueness properties,
together with proof irrelevance for the normalization fields, make the data a
subsingleton.
8. The strict tensor association and unit calculation on supplied normalized data
gives the final two assertions. It uses their generator and both cone-coordinate
formulas, with no additional choice of comparison maps. -/
theorem scalarPullbackStrictConeNaturality
    {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hY : ∀ y : Y, IsUnit (l : Y.residueField y)) :
    (∀ K : ℕ → CochainComplex (integralTowerModules l E X) ℤ,
      IsIso (scalarPullbackProductMap l E L ι X K)) ∧
    (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      integralOperationsGoodComplex l L Y
        ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)) ∧
    (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      IsIso (completedScalarCounit l E L ι X
        ((integralOperationsPullbackComplexFunctor l E g).obj P.obj))) ∧
    Nonempty (ScalarPullbackStrictConeData l E L ι g) ∧
    Subsingleton (ScalarPullbackStrictConeData l E L ι g) ∧
    (∀ D : ScalarPullbackStrictConeData l E L ι g,
      ScalarPullbackCompositionFormula l E L ι g D) ∧
    (∀ D : ScalarPullbackStrictConeData l E E (AlgHom.id ℚ_[l] E) g,
      ScalarPullbackUnitFormula l E g D) := by
  obtain ⟨hprod, _hgoodX, hεX⟩ := finiteFreeScalarCochainProperties l E L ι X
  obtain ⟨_, hgood, hεY⟩ := finiteFreeScalarCochainProperties l E L ι Y
  let := hprod
  obtain ⟨d, hd, hdu⟩ := scalarPullbackStrictTower_existsUnique l E L ι g
  obtain ⟨κ, hκ, hκu⟩ := scalarPullbackCone_existsUnique l E L ι g
  obtain ⟨τ, hτ, _hτu⟩ := scalarPullbackDescent_existsUnique l E L ι g hgood hεY
    (scalarPullbackConeMap l E L ι g d κ)
  let D : ScalarPullbackStrictConeData l E L ι g :=
    ⟨d, hd, κ, hκ, τ, hτ⟩
  have hsub : Subsingleton (ScalarPullbackStrictConeData l E L ι g) := by
    refine ⟨?_⟩
    intro A B
    have h₁ : A.level = B.level := (hdu _ A.generator).trans (hdu _ B.generator).symm
    have h₂ : A.cone = B.cone := (hκu _ A.coordinates).trans (hκu _ B.coordinates).symm
    cases A with
    | mk da hda ca hca ta hta =>
      cases B with
      | mk db hdb cb hcb tb htb =>
        dsimp only at h₁ h₂
        subst db
        subst cb
        have ht := scalarPullbackDescent_existsUnique l E L ι g hgood hεY
          (scalarPullbackConeMap l E L ι g da ca)
        have h₃ : ta = tb := ht.unique hta htb
        subst tb
        rfl
  obtain ⟨hcomp, hunit⟩ := scalarPullbackStrictCoherence l E L ι g
  refine ⟨?_, hgood, fun P ↦ hεX _, ⟨D⟩, hsub, hcomp, hunit⟩
  intro K
  change IsIso (piComparison
    ((completedOrdinaryScalarExtension l E L ι X).mapHomologicalComplex (.up ℤ)) K)
  infer_instance

end WeilConjectures
