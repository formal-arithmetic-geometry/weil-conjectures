/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.AlgebraicClosureStage
public import WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# Direct images and the transition functors of the `ℚ̄_ℓ` coefficient stage

For a morphism `f : Z ⟶ X`, the derived direct image `Rf_*` commutes with the transition functors
`K ↦ K ⊗_E L` of the `ℚ̄_ℓ` coefficient stage (`AlgebraicGeometry.Etale.derivedLowerStarTransitionIso`),
and these isomorphisms are compatible with the composition isomorphisms of the transition functors
(`AlgebraicGeometry.Etale.derivedLowerStarTransitionIso_hexagon`). This is what makes `Rf_*`
induce a functor on the `2`-colimit defining the `ℚ̄_ℓ` stage.

The compatibility is deduced from the cocycle condition for the composition isomorphisms of
right derived functors (`CategoryTheory.Functor.rightDerivedFunctorCompIso'_cocycle`) through the
formal `CategoryTheory.Functor.hexagon_of_cocycles`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Category A₁] [Category A₂] [Category A₃] [Category B₁]
  [Category B₂] [Category B₃]
  {i₁ : A₁ ⥤ B₁} {i₂ : A₂ ⥤ B₂} {i₃ : A₃ ⥤ B₃} {T₁ : A₁ ⥤ A₂} {T₂ : A₂ ⥤ A₃} {T₁₂ : A₁ ⥤ A₃}
  {S₁ : B₁ ⥤ B₂} {S₂ : B₂ ⥤ B₃} {S₁₂ : B₁ ⥤ B₃} {P₁ : A₁ ⥤ B₂} {P₂ : A₂ ⥤ B₃} {P₁₂ : A₁ ⥤ B₃}

/-- A formal consequence of three cocycle conditions: for isomorphisms `κ = a ≪≫ b.symm`
comparing `i ⋙ S` and `T ⋙ i` through a common functor `P`, the compatibility of the `κ` with
composition isomorphisms `c^X : S₁ ⋙ S₂ ≅ S₁₂` and `c^Z : T₁ ⋙ T₂ ≅ T₁₂`. -/
lemma hexagon_of_cocycles (a₁ : i₁ ⋙ S₁ ≅ P₁) (b₁ : T₁ ⋙ i₂ ≅ P₁) (a₂ : i₂ ⋙ S₂ ≅ P₂)
    (b₂ : T₂ ⋙ i₃ ≅ P₂) (a₁₂ : i₁ ⋙ S₁₂ ≅ P₁₂) (b₁₂ : T₁₂ ⋙ i₃ ≅ P₁₂) (cX : S₁ ⋙ S₂ ≅ S₁₂)
    (cZ : T₁ ⋙ T₂ ≅ T₁₂) (d : P₁ ⋙ S₂ ≅ P₁₂) (d' : T₁ ⋙ P₂ ≅ P₁₂)
    (c₁ : whiskerRight a₁.hom S₂ ≫ d.hom = whiskerLeft i₁ cX.hom ≫ a₁₂.hom)
    (c₂ : whiskerRight cZ.hom i₃ ≫ b₁₂.hom = whiskerLeft T₁ b₂.hom ≫ d'.hom)
    (c₃ : whiskerRight b₁.hom S₂ ≫ d.hom = whiskerLeft T₁ a₂.hom ≫ d'.hom) :
    whiskerLeft i₁ cX.hom ≫ (a₁₂ ≪≫ b₁₂.symm).hom =
      whiskerRight (a₁ ≪≫ b₁.symm).hom S₂ ≫ whiskerLeft T₁ (a₂ ≪≫ b₂.symm).hom ≫
        whiskerRight cZ.hom i₃ := by
  have hc₂ : whiskerRight cZ.hom i₃ = whiskerLeft T₁ b₂.hom ≫ d'.hom ≫ b₁₂.inv := by
    rw [← reassoc_of% c₂, Iso.hom_inv_id, Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRight_comp, whiskerLeft_comp, Category.assoc,
    hc₂, ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id', Category.id_comp]
  rw [← reassoc_of% c₃, ← reassoc_of% c₁]
  simp [← whiskerRight_comp_assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open PadicAlgCl PadicAlgCl.FiniteSubext

variable {l : ℕ} [Fact l.Prime] {Z X : Scheme.{u}} (f : Z ⟶ X)

/-- The derived direct image along `f` on étale sheaves of `𝒪_E`-modules. -/
noncomputable abbrev stageLowerStar (E : FiniteSubext l) :
    Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l E.field))) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l E.field))) :=
  Etale.lowerStar (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l E.field))) f

/-- `Rf_*` commutes with the derived transition functors. -/
noncomputable def derivedLowerStarTransitionIso {E L : FiniteSubext l} (h : E ≤ L) :
    (stageLowerStar f E).rightDerivedFunctor ⋙ derivedStageTransition X h ≅
      derivedStageTransition Z h ⋙ (stageLowerStar f L).rightDerivedFunctor :=
  rightDerivedLowerStarCompCoextendScalarsIso
    (integersShrinkMap.{0, u} l (incl h) (incl_compat h)) f

set_option maxHeartbeats 1600000 in
-- The derived functors over the rings of integers are expensive to unify.
/-- The compatibility of the isomorphisms `Rf_* ⋙ T ≅ T ⋙ Rf_*` with the composition
isomorphisms of the transition functors. -/
lemma derivedLowerStarTransitionIso_hexagon {E L L' : FiniteSubext l} (h : E ≤ L)
    (h' : L ≤ L') :
    Functor.whiskerLeft (stageLowerStar f E).rightDerivedFunctor
        (derivedStageTransitionComp X h h').hom ≫
      (derivedLowerStarTransitionIso f (h.trans h')).hom =
    Functor.whiskerRight (derivedLowerStarTransitionIso f h).hom (derivedStageTransition X h') ≫
      Functor.whiskerLeft (derivedStageTransition Z h) (derivedLowerStarTransitionIso f h').hom ≫
        Functor.whiskerRight (derivedStageTransitionComp Z h h').hom
          (stageLowerStar f L').rightDerivedFunctor := by
  let φ₁ := integersShrinkMap.{0, u} l (incl h) (incl_compat h)
  let φ₂ := integersShrinkMap.{0, u} l (incl h') (incl_compat h')
  let φ₁₂ := integersShrinkMap.{0, u} l (incl (h.trans h')) (incl_compat (h.trans h'))
  let αX := sheafStageTransitionComp X h h'
  let e : (sheafStageTransition Z h ⋙ stageLowerStar f L) ⋙ sheafStageTransition X h' ≅
      sheafStageTransition Z (h.trans h') ⋙ stageLowerStar f L' :=
    Functor.isoWhiskerLeft (stageLowerStar f E) αX
  let e' : sheafStageTransition Z h ⋙ (sheafStageTransition Z h' ⋙ stageLowerStar f L') ≅
      sheafStageTransition Z (h.trans h') ⋙ stageLowerStar f L' :=
    Functor.isoWhiskerLeft (stageLowerStar f E) αX
  exact Functor.hexagon_of_cocycles
    (Functor.rightDerivedFunctorCompIso' _ _ (lowerStarCompCoextendScalarsIso φ₁ f))
    (Functor.rightDerivedFunctorCompIso' (sheafStageTransition Z h) (stageLowerStar f L)
      (Iso.refl _))
    (Functor.rightDerivedFunctorCompIso' _ _ (lowerStarCompCoextendScalarsIso φ₂ f))
    (Functor.rightDerivedFunctorCompIso' (sheafStageTransition Z h') (stageLowerStar f L')
      (Iso.refl _))
    (Functor.rightDerivedFunctorCompIso' _ _ (lowerStarCompCoextendScalarsIso φ₁₂ f))
    (Functor.rightDerivedFunctorCompIso' (sheafStageTransition Z (h.trans h'))
      (stageLowerStar f L') (Iso.refl _))
    (derivedStageTransitionComp X h h') (derivedStageTransitionComp Z h h')
    (Functor.rightDerivedFunctorCompIso' _ _ e) (Functor.rightDerivedFunctorCompIso' _ _ e')
    (Functor.rightDerivedFunctorCompIso'_cocycle _ _ _ _ (by
      simp only [lowerStarCompCoextendScalarsIso, Iso.refl_hom, Functor.whiskerRight_id',
        Category.id_comp, Category.comp_id]; rfl))
    (Functor.rightDerivedFunctorCompIso'_cocycle _ _ _ _ (by
      simp only [Iso.refl_hom, Functor.whiskerLeft_id', Category.id_comp, Category.comp_id]
      rfl))
    (Functor.rightDerivedFunctorCompIso'_cocycle _ _ _ _ (by
      simp only [lowerStarCompCoextendScalarsIso, Iso.refl_hom, Functor.whiskerRight_id',
        Functor.whiskerLeft_id', Category.id_comp]; rfl))

section Integral

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- The direct image `Rf_* : D_comp(Z_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)` at the integral stage `E`. -/
noncomputable def integralStageLowerStar (E : FiniteSubext l) :
    DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E.field ⥤
      DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E.field :=
  (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E.field).lift
    ((DerivedCategory.derivedCompleteIntegral Z.smallEtaleTopology l E.field).ι ⋙
      (stageLowerStar f E).rightDerivedFunctor)
    (fun K ↦ derivedCompleteIntegral_rightDerivedLowerStar l E.field f _ K.property)

/-- `Rf_*` commutes with the integral transition functors. -/
noncomputable def integralLowerStarTransitionIso {E L : FiniteSubext l} (h : E ≤ L) :
    integralStageLowerStar f E ⋙ integralStageTransition X h ≅
      integralStageTransition Z h ⋙ integralStageLowerStar f L :=
  NatIso.ofComponents
    (fun K ↦ (ObjectProperty.fullyFaithfulι _).preimageIso
      ((derivedLowerStarTransitionIso f h).app
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E.field).obj K)))
    (fun g ↦ (ObjectProperty.fullyFaithfulι _).map_injective
      ((derivedLowerStarTransitionIso f h).hom.naturality
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E.field).map g)))

/-- The hexagon for the integral compatibility isomorphisms. -/
lemma integralLowerStarTransitionIso_hexagon {E L L' : FiniteSubext l} (h : E ≤ L)
    (h' : L ≤ L') :
    Functor.whiskerLeft (integralStageLowerStar f E) (integralStageTransitionComp X h h').hom ≫
      (integralLowerStarTransitionIso f (h.trans h')).hom =
    Functor.whiskerRight (integralLowerStarTransitionIso f h).hom (integralStageTransition X h') ≫
      Functor.whiskerLeft (integralStageTransition Z h) (integralLowerStarTransitionIso f h').hom ≫
        Functor.whiskerRight (integralStageTransitionComp Z h h').hom
          (integralStageLowerStar f L') := by
  ext K
  apply (ObjectProperty.fullyFaithfulι _).map_injective
  exact congr_app (derivedLowerStarTransitionIso_hexagon f h h')
    ((DerivedCategoryDerivedCompleteIntegral.ι _ l E.field).obj K)

noncomputable instance (E : FiniteSubext l) : (integralStageLowerStar f E).CommShift ℤ :=
  inferInstanceAs (((DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E.field).lift
    ((DerivedCategory.derivedCompleteIntegral Z.smallEtaleTopology l E.field).ι ⋙
      (stageLowerStar f E).rightDerivedFunctor) _).CommShift ℤ)

instance (E : FiniteSubext l) : (integralStageLowerStar f E).IsTriangulated :=
  inferInstanceAs (((DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E.field).lift
    ((DerivedCategory.derivedCompleteIntegral Z.smallEtaleTopology l E.field).ι ⋙
      (stageLowerStar f E).rightDerivedFunctor) _).IsTriangulated)

-- The instance arguments of the derived complete categories are expensive to unify.
set_option maxHeartbeats 1600000 in
/-- The integral direct image carries torsion objects to torsion objects, being linear. -/
lemma torsion_integralStageLowerStar_obj (E : FiniteSubext l)
    (K : DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E.field)
    (hK : Rationalization.torsion (nonZeroDivisors (Shrink.{u + 1} (integers l E.field)))
      (DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E.field) K) :
    Rationalization.torsion (nonZeroDivisors (Shrink.{u + 1} (integers l E.field)))
      (DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E.field)
      ((integralStageLowerStar f E).obj K) := by
  obtain ⟨m, hm, hK⟩ := hK
  refine ⟨m, hm, ?_⟩
  have h0 : (stageLowerStar f E).rightDerivedFunctor.map
      ((DerivedCategoryDerivedCompleteIntegral.ι _ l E.field).map (m • 𝟙 K)) = 0 := by
    rw [hK]
    exact Functor.map_zero (stageLowerStar f E).rightDerivedFunctor _ _
  have h1 : (stageLowerStar f E).rightDerivedFunctor.map
      (m • 𝟙 ((DerivedCategoryDerivedCompleteIntegral.ι _ l E.field).obj K)) =
        m • 𝟙 _ := by
    have := Etale.linear_rightDerivedLowerStar
      (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l E.field))) f
      (Shrink.{u + 1} (integers l E.field))
    exact (Functor.Linear.map_smul (𝟙 _) m).trans
      (congrArg (m • ·) (CategoryTheory.Functor.map_id _ _))
  exact (ObjectProperty.fullyFaithfulι _).map_injective (h1.symm.trans (by exact h0))

/-- The direct image `Rf_* : D_comp(Z_ét, E) ⥤ D_comp(X_ét, E)` at the rational stage `E`. -/
noncomputable abbrev rationalStageLowerStar (E : FiniteSubext l) :
    DerivedCategoryDerivedCompleteRational Z.smallEtaleTopology l E.field ⥤
      DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E.field :=
  Rationalization.mapOfTorsion _ _ (integralStageLowerStar f E)
    (torsion_integralStageLowerStar_obj f E)

lemma torsion_integralLowerStarTransition {E L : FiniteSubext l} (h : E ≤ L)
    (K : DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E.field)
    (hK : Rationalization.torsion (nonZeroDivisors (Shrink.{u + 1} (integers l E.field)))
      (DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E.field) K) :
    Rationalization.torsion (nonZeroDivisors (Shrink.{u + 1} (integers l L.field)))
      (DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l L.field)
      ((integralStageTransition Z h ⋙ integralStageLowerStar f L).obj K) :=
  torsion_integralStageLowerStar_obj f L _ (torsion_integralStageTransition_obj Z h K hK)

/-- `Rf_*` commutes with the rational transition functors. -/
noncomputable def rationalLowerStarTransitionIso {E L : FiniteSubext l} (h : E ≤ L) :
    rationalStageLowerStar f E ⋙ rationalStageTransition X h ≅
      rationalStageTransition Z h ⋙ rationalStageLowerStar f L :=
  Rationalization.mapOfTorsionCompIso _ _ (torsion_integralLowerStarTransition f h)
      (integralLowerStarTransitionIso f h) ≪≫
    (Rationalization.mapOfTorsionCompIso _ _ (torsion_integralLowerStarTransition f h)
      (Iso.refl _)).symm

end Integral

end AlgebraicGeometry.Etale
