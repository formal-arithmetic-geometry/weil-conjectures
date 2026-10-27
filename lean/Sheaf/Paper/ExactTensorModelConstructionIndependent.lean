/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearSystemModels
import all Sheaf.SixFunctors.OpenOperationModels
import Sheaf.Algebra.Homology.CochainTensorModelRigidity

/-! # Normalized tensor comparison for varying-ring inverse image

Source: Stacks Project, Tags 06YS, 06YU and 07A4.
(blueprint: lem-sf-exact-tensor-model-construction-independent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections
open CategoryTheory.MonoidalCategory

namespace WeilConjectures.IndependentTensorModel

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

private noncomputable def resolvingQQ_fullyFaithful
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})
    (E : Type ((max c v r) + 1)) [Category.{(max c v r) + 1} E] :
    let P : ObjectProperty (CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) :=
      fun P ↦ P.IsKFlatIndependentCoefficients ∧ flatTerms.{c, v, r} J R P
    (((Functor.whiskeringLeft _ _ E).obj
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)))).FullyFaithful := by
  let W := (Functor.whiskeringLeft _ _ E).obj
    (((SheafOfModules.cochainTensorFlatRepresentatives J R).ι ⋙ DerivedCategory.Q).prod
      ((SheafOfModules.cochainTensorFlatRepresentatives J R).ι ⋙ DerivedCategory.Q))
  have h := (SheafOfModules.cochain_tensor_model_rigidity J R).choose_spec.2.2
  exact ((Functor.FullyFaithful.nonempty_iff_map_bijective W).2
    (h E inferInstance)).some


section IsoCancellation
universe v₀ u₀
private theorem inverseChain
    {E : Type u₀} [Category.{v₀} E] {X₀ X₁ X₂ X₃ X₄ X₅ : E}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) (d : X₃ ≅ X₄)
    (q : X₄ ⟶ X₅) (w : X₀ ⟶ X₅)
    (h : a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ q = w) :
    d.inv ≫ c.inv ≫ b.inv ≫ a.inv ≫ w = q := by
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]
end IsoCancellation

section Model
attribute [local irreducible] SheafOfModules.monoidalCategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Totalize a natural ordinary tensor isomorphism and descend it uniquely along
flat-term K-flat representatives. Source: Stacks 06YS, 06YU and 07A4
(blueprint: lem-sf-exact-tensor-model-construction-independent).
Proof: totalize the inverse ordinary comparison on every direct-sum summand.
Naturality verifies the signed differential, and the adjunction preserves the
coproducts, so the chain map is invertible. Restriction to flat-term K-flat
representatives is fully faithful by cochain tensor rigidity. The representative
comparisons of the supplied tensor models therefore descend this chain
isomorphism to the displayed derived comparison. Cancelling its four invertible
factors gives precisely the representative equation of TensorComparisonModel. -/
theorem modelOfOrdinary
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf K CommRingCat.{max c v r})
    (F : SemilinearSections.Mod.{c, v, max c v r} J R ⥤
      SemilinearSections.Mod.{c, v, max c v r} K S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : SemilinearSections.Mod.{c, v, max c v r} K S ⥤
      SemilinearSections.Mod.{c, v, max c v r} J R) (adj : F ⊣ G)
    (A : SemilinearSections.Closed.{c, v, r} J R)
    (B : SemilinearSections.Closed.{c, v, r} K S)
    (TA : Models.{c, v, r} J R A)
    (TB : Models.{c, v, r} K S B)
    (e : ∀ M N : SemilinearSections.Mod.{c, v, max c v r} J R,
      F.obj (ordinaryTensor.{c, v, r} J R M N) ≅
        ordinaryTensor.{c, v, r} K S (F.obj M) (F.obj N))
    (he : ∀ {M M' N N' : SemilinearSections.Mod.{c, v, max c v r} J R} (a : M ⟶ M') (b : N ⟶ N'),
      F.map (ordinaryTensorHom.{c, v, r} J R a b) ≫ (e M' N').hom =
        (e M N).hom ≫ ordinaryTensorHom.{c, v, r} K S (F.map a) (F.map b))
    (hk : ∀ P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      flatTerms.{c, v, r} J R P →
      CochainComplex.IsKFlatIndependentCoefficients (J := K) (R := S)
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃ mu : A.tensor ⋙ F.mapDerivedCategory ≅
        (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ B.tensor,
      ∃ model : TensorComparisonModel.{c, v, r} J K R S F A B TA TB mu,
        model.ordinary = e ∧ ∀ P Q, IsIso (model.chain P Q) := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let P : ObjectProperty (CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) :=
    fun P ↦ P.IsKFlatIndependentCoefficients ∧ flatTerms.{c, v, r} J R P
  let Q : ObjectProperty (CochainComplex (SemilinearSections.Mod.{c, v, max c v r} K S) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
  let i : P.FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)) :=
    ObjectProperty.ιOfLE (fun _ h ↦ h.1)
  let r := Functor.isoWhiskerLeft (i.prod i) TA.comparison
  let H := F.mapHomologicalComplex (.up ℤ)
  have hH : ∀ X, P X → Q (H.obj X) := fun X h ↦ hk X h.1 h.2
  have hn {M M' N N' : SemilinearSections.Mod.{c, v, max c v r} J R}
      (b : M ⟶ M') (d : N ⟶ N') :
      F.map (b ⊗ₘ d) ≫ (e M' N').hom =
        (e M N).hom ≫ (F.map b ⊗ₘ F.map d) := he b d
  let beta := SheafOfModules.OpenTensorNormalization.exactTensorTotalIso F e hn G adj
  obtain ⟨mu, hmu⟩ := SheafOfModules.OpenTensorNormalization.tensorDescentNormalized
    DerivedCategory.Q DerivedCategory.Q H F.mapDerivedCategory
    (Functor.mapDerivedCategoryFactors F).hom P Q hH
    (resolvingQQ_fullyFaithful.{c, v, r} J R (DerivedCategory
      (SemilinearSections.Mod.{c, v, max c v r} K S)))
    (totalTensor.{c, v, r} J R) (totalTensor.{c, v, r} K S)
    A.tensor B.tensor r TB.comparison beta
    (fun _ _ ↦ by infer_instance) (fun _ _ _ _ ↦ by infer_instance)
  refine ⟨mu, {
    ordinary := e
    chain := fun X Y ↦ beta.hom.app (X, Y)
    summand := ?_
    kflat := hk
    derived := ?_
  }, rfl, ?_⟩
  · intro X Y p q k h
    rw [SheafOfModules.OpenTensorNormalization.exactTensorTotalIso_hom_app]
    dsimp only [tensorPullbackTotal, tensorPullbackTotalComponent, tensorSummand]
    exact HomologicalComplex.ι_mapBifunctorDesc _ p q h
  · intro X Y hx hy hfx hfy
    have hpx : P X :=
      ⟨hx, hfx⟩
    have hpy : P Y :=
      ⟨hy, hfy⟩
    have hm := hmu X Y hpx hpy
    change F.mapDerivedCategory.map (tensorModelIso.{c, v, r} J R A TA X Y hx hy).hom ≫
      mu.hom.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) ≫
      B.tensor.map (Prod.mkHom ((Functor.mapDerivedCategoryFactors F).hom.app X)
        ((Functor.mapDerivedCategoryFactors F).hom.app Y)) ≫
      (tensorModelIso.{c, v, r} K S B TB (H.obj X) (H.obj Y)
        (hH X hpx) (hH Y hpy)).inv ≫
      DerivedCategory.Q.map (beta.hom.app (X, Y)) =
        (Functor.mapDerivedCategoryFactors F).hom.app
          ((totalTensor.{c, v, r} J R).obj (X, Y)) at hm
    have h := inverseChain
      (F.mapDerivedCategory.mapIso
        (tensorModelIso.{c, v, r} J R A TA X Y hx hy))
      (mu.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y))
      (B.tensor.mapIso (Iso.prod ((Functor.mapDerivedCategoryFactors F).app X)
        ((Functor.mapDerivedCategoryFactors F).app Y)))
      (tensorModelIso.{c, v, r} K S B TB (H.obj X) (H.obj Y)
        (hH X hpx) (hH Y hpy)).symm
      (DerivedCategory.Q.map (beta.hom.app (X, Y)))
      ((Functor.mapDerivedCategoryFactors F).hom.app
        ((totalTensor.{c, v, r} J R).obj (X, Y)))
      (by simpa only [Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom,
        Iso.symm_hom] using hm)
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    simpa only [H, Functor.mapIso_inv, Iso.prod_inv, Iso.app_inv, Iso.symm_inv] using h
  · intro P Q
    change IsIso (beta.hom.app (P, Q))
    infer_instance

end Model
end WeilConjectures.IndependentTensorModel
