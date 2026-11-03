/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import all WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ExactDerivedMonoidalConstruction
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived

/-! Normalized chain and derived cup of an exact strong monoidal functor.
Source: Stacks 07A4, 0FPQ and 0FPT.
(blueprint: lem-pod-exact-monoidal-sections-cup)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Category CategoryTheory.Functor
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
namespace CategoryTheory.CondensedPointCupConstruction
private theorem monoidal_localization_square
    {B E F H : Type*} [Category* B] [Category* E] [Category* F] [Category* H]
    [MonoidalCategory B] [MonoidalCategory E] [MonoidalCategory F] [MonoidalCategory H]
    (Q : B ⥤ F) (L : E ⥤ H) (G : B ⥤ E) (V : F ⥤ H)
    [Q.LaxMonoidal] [L.LaxMonoidal] [G.Monoidal]
    (e : Q ⋙ V ≅ G ⋙ L) (W : MorphismProperty B) (S : ObjectProperty B)
    [W.ContainsIdentities] [W.RespectsIso] [Q.IsLocalization W]
    [(property_localizer W S).IsLeftDerivabilityStructure]
    [IsIso (ε Q)] [IsIso (ε L)]
    (hmodels : ∀ X : F, ∃ P, S P ∧ Nonempty (Q.obj P ≅ X))
    (hQ : ∀ P R, S R → IsIso (μ Q P R))
    (hL : ∀ (X : E) R, S R → IsIso (μ L X (G.obj R))) :
    ∃ m : V.Monoidal, letI := m
      NatTrans.IsMonoidal e.hom := by
  let T := (((whiskeringLeft₂ H).obj V).obj V).obj (curriedTensor H)
  let U := (postcompose₂.obj V).obj (curriedTensor F)
  let a : (((whiskeringLeft₂ H).obj Q).obj Q).obj T ⟶
      (((whiskeringLeft₂ H).obj G).obj G).obj
        ((postcompose₂.obj L).obj (curriedTensor E)) :=
    (((whiskeringLeft₂ H).map e.hom).app (Q ⋙ V)).app (curriedTensor H) ≫
      (((whiskeringLeft₂ H).obj (G ⋙ L)).map e.hom).app (curriedTensor H) ≫
      (((whiskeringLeft₂ H).obj G).obj G).map (μNatTrans L)
  have ha P R : (a.app P).app R =
      (e.hom.app P ⊗ₘ e.hom.app R) ≫ μ L (G.obj P) (G.obj R) := by
    dsimp [a]
    rw [MonoidalCategory.tensorHom_def, Category.assoc]
    rfl
  let b : (((whiskeringLeft₂ H).obj Q).obj Q).obj U ⟶
      (((whiskeringLeft₂ H).obj G).obj G).obj
        ((postcompose₂.obj L).obj (curriedTensor E)) :=
    (postcompose₂.obj V).map (μNatTrans Q) ≫
      (postcompose₂.map e.hom).app (curriedTensor B) ≫
      postcompose₂MapWhiskeringLeft₂ (δNatTrans G) L
  have hb P R : (b.app P).app R =
      V.map (μ Q P R) ≫ e.hom.app (P ⊗ R) ≫ L.map (δ G P R) := rfl
  have : T.IsLeftDerivedFunctor₂ a W W := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (LocalizerMorphism.id W) (property_localizer W S) a
    intro P R
    have := hL (G.obj P) R.obj R.property
    change IsIso ((a.app P).app R.obj)
    rw [ha]
    infer_instance
  have : U.IsLeftDerivedFunctor₂ b W W := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (LocalizerMorphism.id W) (property_localizer W S) b
    intro P R
    have := hQ P R.obj R.property
    change IsIso (V.map (μ Q P R.obj) ≫ e.hom.app (P ⊗ R.obj) ≫
      L.map (δ G P R.obj))
    infer_instance
  let t : U ≅ T := leftDerived₂NatIso T a W W U b (Iso.refl _)
  have ht P R : (t.hom.app (Q.obj P)).app (Q.obj R) ≫
      (e.hom.app P ⊗ₘ e.hom.app R) ≫ μ L (G.obj P) (G.obj R) =
      V.map (μ Q P R) ≫ e.hom.app (P ⊗ R) ≫ L.map (δ G P R) := by
    have h := leftDerived₂NatTrans_app_app T a W W U b (𝟙 _) P R
    rw [ha, hb] at h
    exact h.trans (Category.comp_id _)
  let : V.OplaxMonoidal := .ofLaxSquare t.hom (fun P ↦ e.hom.app P)
    (fun _ _ f ↦ e.hom.naturality f) ht S hmodels hL
  have (X Y : F) : IsIso (δ V X Y) :=
    inferInstanceAs (IsIso ((t.hom.app X).app Y))
  have : IsIso (η V) := by
    change IsIso (V.map (ε Q) ≫ e.hom.app _ ≫ L.map (η G) ≫ inv (ε L))
    infer_instance
  letI : V.Monoidal := .ofOplaxMonoidal V
  exact ⟨inferInstance,
    ExactMonoidalEquivalenceDerived.square_monoidal Q L G V e.hom rfl ht⟩

universe a ha wa wb r
variable {B : Type a} [Category.{ha} B] [Abelian B]
  [IsGrothendieckAbelian.{ha} B] [HasColimitsOfSize.{0, 0} B]
  [MonoidalCategory B] [MonoidalClosed B] [MonoidalPreadditive B] [BraidedCategory B]
  [Abelian.HasFunctorialFlatResolution B] [HasDerivedCategory.{wa} B]
  {Rcoeff : Type r} [CommRing Rcoeff]
  [HasDerivedCategory.{wb} (ModuleCat.{r} Rcoeff)]

/-- An exact cocontinuous flat-preserving strong monoidal functor has cup data
with precisely its given ordinary lax structure. Source: Stacks 07A4, 0FPQ and 0FPT.
Proof: choose flat-term functorial K-flat resolutions whose images remain K-flat.
The source and target tensor bifunctors have invertible localization comparisons on
these representatives. Their universal comparison supplies the derived monoidal
structure. Retain the monoidal factorization square, which is exactly the tensor and
unit normalization required by the cup. The ordinary summand and degree-zero unit
formulas follow from the existing complex monoidal comparison.
(blueprint: lem-pod-exact-monoidal-sections-cup) -/
theorem exact_monoidal_sections_cup
    (G : B ⥤ ModuleCat.{r} Rcoeff) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesColimitsOfSize.{0, 0} G] [G.PreservesFlat] (m : G.Monoidal) :
    ∃ d : ExactSectionsDerivedCup G, d.ordinary = m.toLaxMonoidal := by
  letI := m
  letI : (G.mapHomologicalComplex (.up ℤ)).Monoidal := G.mapCochainComplexMonoidal
  letI : (G.mapHomologicalComplex (.up ℤ)).LaxMonoidal :=
    (G.mapCochainComplexMonoidal).toLaxMonoidal
  letI : (G.mapHomologicalComplex (.up ℤ)).OplaxMonoidal :=
    (G.mapCochainComplexMonoidal).toOplaxMonoidal
  have hμ (K L : CochainComplex B ℤ) :
      μ (G.mapHomologicalComplex (.up ℤ)) K L = (G.mapCochainComplexμIso K L).hom := by
    rfl
  have hε : ε (G.mapHomologicalComplex (.up ℤ)) = G.mapCochainComplexεIso.hom := by
    rfl
  let W := HomologicalComplex.quasiIso B (.up ℤ)
  let S : ObjectProperty (CochainComplex B ℤ) := W.kFlat ⊓
    (HomologicalComplex.quasiIso (ModuleCat.{r} Rcoeff) (.up ℤ)).kFlat.inverseImage
      (G.mapHomologicalComplex (.up ℤ))
  let Φ := property_localizer W S
  have : HasExactColimitsOfShape ℤ B := by
    have := AB5OfSize_of_univLE.{0, 0, ha, ha} B
    infer_instance
  have : HasExactColimitsOfShape ℤ (ModuleCat.{r} Rcoeff) := by
    have := AB5OfSize_of_univLE.{0, 0, r, r} (ModuleCat.{r} Rcoeff)
    infer_instance
  have (X : ModuleCat.{r} Rcoeff) :
      PreservesColimitsOfShape ℤ ((curriedTensor (ModuleCat.{r} Rcoeff)).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution B).some.reduced
  have hρ (P : CochainComplex B ℤ) : S (Λ.resolutionFunctor.obj P) :=
    ⟨Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le P,
      G.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
        ObjectProperty.flat.essImage_ι_le P⟩
  have : Φ.functor.Full := inferInstanceAs S.ι.Full
  have : Φ.functor.Faithful := inferInstanceAs S.ι.Faithful
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.IsLeftDerivabilityStructure :=
    Φ.isLeftDerivabilityStructure_of_functorial_resolutions
      (ρ := ObjectProperty.lift S Λ.resolutionFunctor hρ) Λ.resolutionNatTrans
      (fun P ↦ by
        change HomologicalComplex.quasiIso B (.up ℤ) _
        rw [HomologicalComplex.mem_quasiIso_iff]
        exact Λ.quasiIso_resolutionNatTrans_app P) rfl
  have : IsIso (ε (DerivedCategory.Q (C := B))) :=
    RingedDerivedNative.localization_isIso_ε
  have : IsIso (ε (DerivedCategory.Q (C := (ModuleCat.{r} Rcoeff)))) :=
    RingedDerivedNative.localization_isIso_ε
  have hmodels (X : DerivedCategory B) :
      ∃ P, S P ∧ Nonempty (DerivedCategory.Q.obj P ≅ X) := by
    let P := DerivedCategory.Q.objPreimage X
    have : QuasiIso (Λ.resolutionNatTrans.app P) := Λ.quasiIso_resolutionNatTrans_app P
    exact ⟨Λ.resolutionFunctor.obj P, hρ P,
      ⟨asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app P)) ≪≫
        DerivedCategory.Q.objObjPreimageIso X⟩⟩
  obtain ⟨n, hn⟩ := monoidal_localization_square DerivedCategory.Q DerivedCategory.Q
    (G.mapHomologicalComplex (.up ℤ)) G.mapDerivedCategory G.mapDerivedCategoryFactors W S
    hmodels (fun P R hR ↦ ConstantModuleDerivedProjection.tensor_localization_iso P R hR.1)
    (fun X R hR ↦ ConstantModuleDerivedProjection.tensor_localization_iso X _ hR.2)
  letI := n
  refine ⟨{
    ordinary := m.toLaxMonoidal
    derived := n.toLaxMonoidal
    chain := fun K L ↦ (G.mapCochainComplexμIso K L).hom
    chain_summand := G.ιTensorObj_mapCochainComplexμIso_hom_f
    chainUnit := G.mapCochainComplexεIso.hom
    chainUnit_zero := G.mapCochainComplexεIso_hom_f_zero
    tensor_normalization := ?_
    unit_normalization := ?_
  }, rfl⟩
  · intro K L
    simpa only [Functor.LaxMonoidal.comp_μ, Category.assoc, hμ] using hn.tensor K L
  · simpa only [Functor.LaxMonoidal.comp_ε, Category.assoc, hε] using hn.unit

end CategoryTheory.CondensedPointCupConstruction
