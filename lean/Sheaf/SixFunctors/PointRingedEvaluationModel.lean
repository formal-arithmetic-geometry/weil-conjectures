/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module
public import Sheaf.SixFunctors.PointEvaluationTensorCoherence
public import Sheaf.SixFunctors.PointEvaluationDerivedTensor
public import Sheaf.SixFunctors.PointEvaluationScalarCoherence
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion
import Sheaf.Algebra.Homology.RingedSitePointFlat
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import all Sheaf.Algebra.Homology.RingedSitePointTensor
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all Sheaf.Paper.ResolvingRepresentativeWhiskering
import Sheaf.Paper.TensorPullbackRepresentativeDescent
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import all Sheaf.Algebra.Category.ModuleCat.Sheaf.LineEvaluationInversePair
import all Sheaf.Algebra.Homology.TorAmplitudePrincipalCover
import Sheaf.Paper.KFlatRingedToposPullback
import Mathlib.RingTheory.Flat.Stability
import all Sheaf.SecSmoothPurity.ModuleTensorExtensionEquation
import all Sheaf.SecSmoothPurity.CochainComparisonMonoidalEquations
import all Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.SixFunctors.PointEvaluationChainModels

/-! Source: Stacks 0991, 03EL, 07A4
(blueprint: lem-sf-point-ringed-evaluation-model). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false

set_option genInjectivity false
set_option genSizeOfSpec false
-- These instances fix the data in dependent monoidal comparisons.
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
open scoped TensorProduct ChangeOfRings
attribute [local instance 3000] ModuleCat.monoidalCategory
section GenericBraiding
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.Monoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
private theorem total_map_tensor {P Q P' Q' : CochainComplex C ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (Functor.uncurry.obj ((curriedTensor C).map₂CochainComplex)).map
      (Prod.mkHom f g) = f ⊗ₘ g := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := P) (K₂ := Q) (F := curriedTensor C)
  intro i j h
  change _ = HomologicalComplex.ιMapBifunctor P Q (curriedTensor C) (.up ℤ) i j n h ≫
    (HomologicalComplex.mapBifunctorMap f g (curriedTensor C) (.up ℤ)).f n
  simp only [Functor.uncurry_obj_map, Functor.map₂CochainComplex,
    Functor.map₂HomologicalComplex, HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f]
  simp

end GenericBraiding

private theorem descent_normalized {C D E : Type*}
    [Category* C] [Category* D] [Category* E] (q : C ⥤ D) (F G : D ⥤ E)
    (ff : ((Functor.whiskeringLeft C D E).obj q).FullyFaithful)
    (R : C ⥤ E) (a : q ⋙ F ≅ R) (b : q ⋙ G ≅ R) :
    ∃! δ : F ≅ G, ∀ X : C,
      a.hom.app X = δ.hom.app (q.obj X) ≫ b.hom.app X := by
  let e := a ≪≫ b.symm
  let δ := ff.preimageIso (X := F) (Y := G) e
  have hδ (X : C) : δ.hom.app (q.obj X) = e.hom.app X :=
    congrArg (fun t ↦ t.app X) (ff.map_preimage (X := F) (Y := G) e.hom)
  have h (X : C) : a.hom.app X = δ.hom.app (q.obj X) ≫ b.hom.app X := by
    rw [hδ]
    simp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  refine ⟨δ, h, ?_⟩
  intro δ' h'
  apply Iso.ext
  apply ff.map_injective
  ext X
  apply (cancel_mono (b.hom.app X)).1
  exact (h' X).symm.trans (h X)

namespace AlgebraicGeometry.ProEtale.PointEvaluation
variable {k : Type u} [Field k]
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
@[reducible] private def sections : ModuleSheaves B ⥤ ModuleCat.{u + 1} (sectionRing k B) :=
  pointModuleSections k B

private instance : (sections B).Additive := inferInstanceAs ((pointModuleSections k B).Additive)


/-- The lift in a pointed neighbourhood, as an arrow of the small site.
Full faithfulness changes only its category packaging.
Source: Stacks 0991 (blueprint: lem-sf-point-ringed-evaluation-model). -/
def pointedLift [IsAlgClosed k]
    (n : ProEtaleGeometricNeighbourhood (𝟙 (Spec (.of k)))) : finalObject k ⟶ n.right :=
  (Scheme.ProEt.forgetFullyFaithful (Spec (.of k))).preimage n.hom

private def restrictionCocone [IsAlgClosed k]
    (F : Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))) :
    Cocone (proEtaleGeometricStalkDiagram (𝟙 (Spec (.of k))) F) where
  pt := F.obj.obj (op (finalObject k))
  ι := {
    app := fun n ↦ F.obj.map (pointedLift n.unop).op
    naturality := by
      intro n m f
      change F.obj.map f.unop.right.op ≫ F.obj.map (pointedLift m.unop).op =
        F.obj.map (pointedLift n.unop).op ≫ 𝟙 _
      rw [Category.comp_id, ← F.obj.map_comp, ← op_comp]
      congr 2
      apply (Scheme.ProEt.forgetFullyFaithful (Spec (.of k))).map_injective
      simpa only [Functor.map_comp, pointedLift, Functor.FullyFaithful.map_preimage]
        using f.unop.w }

private def finalNeighbourhood [IsAlgClosed k] :
    ProEtaleGeometricNeighbourhood (𝟙 (Spec (.of k))) :=
  StructuredArrow.mk (Y := finalObject k) (𝟙 (Over.mk (𝟙 (Spec (.of k)))))

private def finalNeighbourhoodArrow [IsAlgClosed k]
    (n : ProEtaleGeometricNeighbourhood (𝟙 (Spec (.of k)))) :
    finalNeighbourhood (k := k) ⟶ n :=
  StructuredArrow.homMk (pointedLift n) (by
    change 𝟙 _ ≫ (Scheme.ProEt.forget (Spec (.of k))).map (pointedLift n) = n.hom
    rw [Category.id_comp]
    exact (Scheme.ProEt.forgetFullyFaithful (Spec (.of k))).map_preimage
      (X := finalObject k) (Y := n.right) n.hom)

private def stalkSectionsIso [IsAlgClosed k] :
    proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k))) ≅
      (sheafSections (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))).obj
        (op (finalObject k)) := by
  refine NatIso.ofComponents (fun F ↦ ?_) ?_
  · refine ⟨colimit.desc _ (restrictionCocone F),
      colimit.ι (proEtaleGeometricStalkDiagram (𝟙 (Spec (.of k))) F)
        (op (finalNeighbourhood (k := k))), ?_, ?_⟩
    · apply colimit.hom_ext
      intro n
      change colimit.ι (proEtaleGeometricStalkDiagram (𝟙 (Spec (.of k))) F) n ≫
        colimit.desc _ (restrictionCocone F) ≫
        colimit.ι (proEtaleGeometricStalkDiagram (𝟙 (Spec (.of k))) F)
          (op (finalNeighbourhood (k := k))) = _
      rw [colimit.ι_desc_assoc]
      exact colimit.w (proEtaleGeometricStalkDiagram (𝟙 (Spec (.of k))) F)
        (finalNeighbourhoodArrow n.unop).op
    · rw [colimit.ι_desc]
      change F.obj.map (pointedLift (finalNeighbourhood (k := k))).op = 𝟙 _
      have h : pointedLift (finalNeighbourhood (k := k)) = 𝟙 (finalObject k) := by
        apply (Scheme.ProEt.forgetFullyFaithful (Spec (.of k))).map_injective
        change (Scheme.ProEt.forget (Spec (.of k))).map
          ((Scheme.ProEt.forgetFullyFaithful (Spec (.of k))).preimage
            (𝟙 ((Scheme.ProEt.forget (Spec (.of k))).obj (finalObject k)))) = _
        rw [Functor.FullyFaithful.map_preimage]
        exact ((Scheme.ProEt.forget (Spec (.of k))).map_id (finalObject k)).symm
      rw [h]
      exact F.obj.map_id _
  · intro F G f
    apply colimit.hom_ext
    intro n
    change colimit.ι (proEtaleGeometricStalkDiagram (𝟙 (Spec (.of k))) F) n ≫
        colim.map _ ≫ colimit.desc _ (restrictionCocone G) = _
    change _ = colimit.ι (proEtaleGeometricStalkDiagram (𝟙 (Spec (.of k))) F) n ≫
      colimit.desc _ (restrictionCocone F) ≫ f.hom.app (op (finalObject k))
    rw [colimit.ι_map_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
    exact (f.hom.naturality (pointedLift n.unop).op).symm

/-- The actual ringed point, including the normalization of its ring and module inverse images.
The coefficient map is the identity because the point ring is the inverse-image ring itself.
Source: Stacks 0991, 03D2 (blueprint: lem-sf-point-ringed-evaluation-model). -/
def PointIdentification [IsAlgClosed k]
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) : Prop :=
  ∃ e : proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k))) ≅
      (sheafSections (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))).obj
        (op (finalObject k)),
    (∀ (F : Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1)))
      (n : ProEtaleGeometricNeighbourhood (𝟙 (Spec (.of k)))) (x : F.obj.obj (op n.right)),
      e.hom.app F (colimit.ι (proEtaleGeometricStalkDiagram (𝟙 (Spec (.of k))) F) (op n) x) =
        F.obj.map (pointedLift n).op x) ∧
    ∃ p : GeometricMorphism (Type (u + 1))
        (Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))),
      p.inverse = proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k))) ∧
      ∃ s : RingedSitePoint B p,
        s.ring = CommRingCat.of (sectionRing k B) ∧
        HEq s.ringUnderlying
          (e.app ((sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1})).obj B)) ∧
        HEq s.modules (pointModuleSections k B) ∧
        ∀ M : ModuleSheaves B,
          HEq (s.moduleUnderlying.hom.app M)
            (e.inv.app ((SheafOfModules.toSheaf _ ⋙
              sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M))

private theorem stalkSections_naturality [IsAlgClosed k]
    {F G : Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))}
    (f : F ⟶ G) (x : (proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k)))).obj F) :
    (stalkSectionsIso (k := k)).hom.app G
        ((proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k)))).map f x) =
      f.hom.app (op (finalObject k)) ((stalkSectionsIso (k := k)).hom.app F x) :=
  NatTrans.naturality_apply (stalkSectionsIso (k := k)).hom f x

private def evaluationRingedPoint [IsAlgClosed k]
    (R : Type (u + 1) ⥤
      Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1)))
    (adj : proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k))) ⊣ R)
    (hlim : PreservesFiniteLimits
      (proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k))))) :
    RingedSitePoint B
      (GeometricMorphism.mk
        (proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k)))) R adj hlim) := by
  let e := stalkSectionsIso (k := k)
  exact {
    ring := CommRingCat.of (sectionRing k B)
    ringUnderlying := e.app ((sheafCompose _ (forget CommRingCat.{u + 1})).obj B)
    ringAdd := by
      intro T a b t h x
      exact (stalkSections_naturality t x).trans
        ((h _ _).trans ((congrArg₂ (fun x y : sectionRing k B ↦ x + y)
          (stalkSections_naturality a x)
          (stalkSections_naturality b x)).symm))
    ringMul := by
      intro T a b t h x
      exact (stalkSections_naturality t x).trans
        ((h _ _).trans ((congrArg₂ (fun x y : sectionRing k B ↦ x * y)
          (stalkSections_naturality a x)
          (stalkSections_naturality b x)).symm))
    ringZero := by
      intro T a h x
      exact (stalkSections_naturality a x).trans (h _ _)
    ringOne := by
      intro T a h x
      exact (stalkSections_naturality a x).trans (h _ _)
    modules := pointModuleSections k B
    moduleUnderlying := Functor.isoWhiskerLeft
      (SheafOfModules.toSheaf _ ⋙ sheafCompose _ (forget AddCommGrpCat.{u + 1})) e.symm
    moduleAdd := by
      intro M T a b t h x
      exact (stalkSections_naturality t x).trans
        ((h _ _).trans ((congrArg₂ (fun x y : M.val.obj (op (finalObject k)) ↦ x + y)
          (stalkSections_naturality a x)
          (stalkSections_naturality b x)).symm))
    moduleZero := by
      intro M T a h x
      exact (stalkSections_naturality a x).trans (h _ _)
    moduleSMul := by
      intro M T a b t h x
      exact (stalkSections_naturality t x).trans
        ((h _ _).trans ((congrArg₂ (fun (x : sectionRing k B)
          (y : M.val.obj (op (finalObject k))) ↦ x • y) (stalkSections_naturality a x)
          (stalkSections_naturality b x)).symm))
    modules_additive := { map_add := by intros; rfl } }

private theorem pointIdentification [IsAlgClosed k] : PointIdentification B := by
  let e := stalkSectionsIso (k := k)
  obtain ⟨R, _, ⟨adj⟩, hlim⟩ := (geometricStalkToposPoint (𝟙 (Spec (.of k)))).2
  let p : GeometricMorphism (Type (u + 1))
      (Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))) :=
    ⟨proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k))), R, adj, hlim⟩
  let s := evaluationRingedPoint B R adj hlim
  refine ⟨e, ?_, p, rfl, s, rfl, HEq.rfl, HEq.rfl, fun _ ↦ HEq.rfl⟩
  intro F n x
  exact ConcreteCategory.congr_hom (colimit.ι_desc (restrictionCocone F) (op n)) x

universe e

/-- The specified constant-section ring map, using only the unit of sheafification.
The ULift is the recorded coefficient-size transport and has inverse `down`.
Source: blueprint order 1455 (blueprint: lem-sf-point-ringed-evaluation-model). -/
def constantSection (k : Type u) [Field k] (A : Type e) [CommRing A] :
    A →+* (((constantSheaf (Scheme.ProEt.topology (Spec (.of k)))
      CommRingCat.{max e (u + 1)}).obj (CommRingCat.of (ULift.{u + 1} A))).obj.obj
        (op (finalObject k))) :=
  ((toSheafify (Scheme.ProEt.topology (Spec (.of k)))
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} A)))).app (op (finalObject k))).hom.comp
    (ULift.ringEquiv.symm.toRingHom)

/-- Integral constants followed by the actual map to the inverse-limit ring sheaf.
Source: blueprint order 1455 (blueprint: lem-sf-point-ringed-evaluation-model). -/
def integralSection (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : Type e) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Padic.coefficientExtensionIntegers l E →+*
      (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))).obj.obj
        (op (finalObject k)) :=
  (((WeilConjectures.integralConstantToCompletionOfUniverses l E (Spec (.of k))).hom.app
    (op (finalObject k))).hom).comp (constantSection k (Padic.coefficientExtensionIntegers l E))

/-- Finite and completed section identifications are the specified constant and quotient maps.
The natural index n represents exponent n+1; no exponent zero is silently included.
Source: blueprint order 1455 and Bhatt--Scholze Lemma 4.2.12
(blueprint: lem-sf-point-ringed-evaluation-model). -/
def CoefficientsIdentified (k : Type u) [Field k] : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E : Type e) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E],
    (∀ n : ℕ, Function.Bijective (constantSection k (Padic.coefficientExtensionRing l E (n + 1)))) ∧
    Function.Bijective (integralSection k l E) ∧
    (∀ (n : ℕ) (a : Padic.coefficientExtensionIntegers l E),
      ((limit.π (WeilConjectures.integralCoefficientSheafSystem l E (Spec (.of k))) (op n)).hom.app
        (op (finalObject k))) (integralSection k l E a) =
      constantSection k (Padic.coefficientExtensionRing l E (n + 1))
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a)) ∧
    (∀ (n : ℕ) (a : Padic.coefficientExtensionRing l E (n + 2)),
      ((WeilConjectures.integralCoefficientSheafTransition l E (Spec (.of k)) n).hom.app
        (op (finalObject k))) (constantSection k (Padic.coefficientExtensionRing l E (n + 2)) a) =
      constantSection k (Padic.coefficientExtensionRing l E (n + 1))
        (Padic.coefficientExtensionTransition l E (n + 1) a))


private theorem constantSection_bijective (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type e) [CommRing A] : Function.Bijective (constantSection k A) := by
  let J := Scheme.ProEt.topology (Spec (.of k))
  let := (Scheme.proEtaleConstantRingUnit_locallyBijectiveOfUniverses
    (Spec (.of k)) A).1
  let := (Scheme.proEtaleConstantRingUnit_locallyBijectiveOfUniverses
    (Spec (.of k)) A).2
  let P := (Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
    (CommRingCat.of (ULift.{u + 1} A))
  have h : Function.Bijective ((toSheafify J P).app (op (finalObject k))) := by
    constructor
    · intro x y hxy
      have hh := Scheme.ProEt.id_mem_of_mem_topology_of_iso (Iso.refl _)
        (Presheaf.equalizerSieve_mem J
          (Functor.whiskerRight (toSheafify J P) (forget₂ CommRingCat RingCat)) x y hxy)
      change P.map (𝟙 _) x = P.map (𝟙 _) y at hh
      simpa only [P.map_id, ConcreteCategory.id_apply] using hh
    · intro x
      obtain ⟨y, hy⟩ := Scheme.ProEt.id_mem_of_mem_topology_of_iso (Iso.refl _)
        (Presheaf.imageSieve_mem J
          (Functor.whiskerRight (toSheafify J P) (forget₂ CommRingCat RingCat)) x)
      change (toSheafify J P).app _ y = (sheafify J P).map (𝟙 _) x at hy
      rw [(sheafify J P).map_id] at hy
      exact ⟨y, hy⟩
  exact h.comp ULift.ringEquiv.symm.bijective

private theorem integralSection_projection (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type e) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (a : Padic.coefficientExtensionIntegers l E) :
    ((limit.π (WeilConjectures.integralCoefficientSheafSystem l E (Spec (.of k)))
      (op n)).hom.app (op (finalObject k))) (integralSection k l E a) =
      constantSection k (Padic.coefficientExtensionRing l E (n + 1))
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a) := by
  let : EssentiallySmall.{max e (u + 1)} (Spec (.of k)).ProEt := essentiallySmallSelf _
  let : (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
      CommRingCat.{max e (u + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let U := op (finalObject k)
  have h := congrArg (fun f ↦ f.hom.app U)
    (limit.lift_π (WeilConjectures.integralConstantConeOfUniverses l E (Spec (.of k))) (op n))
  have h' := ConcreteCategory.congr_hom h
    (constantSection k (Padic.coefficientExtensionIntegers l E) a)
  change ((limit.π (WeilConjectures.integralCoefficientSheafSystem l E
    (Spec (.of k))) (op n)).hom.app U) (integralSection k l E a) = _ at h'
  refine h'.trans ?_
  let R := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
  let S := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let f : R ⟶ S := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
        (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Scheme.ProEt.topology (Spec (.of k)))
      ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).map f)) U) (ULift.up a)).symm

private theorem constantSection_transition (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type e) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 2)) :
    ((WeilConjectures.integralCoefficientSheafTransition l E (Spec (.of k)) n).hom.app
      (op (finalObject k))) (constantSection k (Padic.coefficientExtensionRing l E (n + 2)) a) =
      constantSection k (Padic.coefficientExtensionRing l E (n + 1))
        (Padic.coefficientExtensionTransition l E (n + 1) a) := by
  let : EssentiallySmall.{max e (u + 1)} (Spec (.of k)).ProEt := essentiallySmallSelf _
  let : (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
      CommRingCat.{max e (u + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let R := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 2)))
  let S := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let f : R ⟶ S := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (n + 1)).comp
        (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Scheme.ProEt.topology (Spec (.of k)))
      ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).map f)) (op (finalObject k)))
    (ULift.up a)).symm

private theorem compatibleCoordinates_bijective
    {A X : Type*} {R S : ℕ → Type*}
    (q : A → ∀ n, R n) (p : X → ∀ n, S n)
    (tr : ∀ n, R (n + 1) → R n) (ts : ∀ n, S (n + 1) → S n)
    (c : ∀ n, R n → S n) (f : A → X)
    (hq : Function.Injective q) (hp : Function.Injective p)
    (hcomplete : ∀ b : ∀ n, R n, (∀ n, tr n (b (n + 1)) = b n) →
      ∃ a, q a = b)
    (hc : ∀ n, Function.Bijective (c n))
    (htr : ∀ n x, ts n (c (n + 1) x) = c n (tr n x))
    (hcompat : ∀ x n, ts n (p x (n + 1)) = p x n)
    (hf : ∀ a n, p (f a) n = c n (q a n)) : Function.Bijective f := by
  classical
  constructor
  · intro a b hab
    apply hq
    funext n
    apply (hc n).1
    exact (hf a n).symm.trans ((congrArg (fun x ↦ p x n) hab).trans (hf b n))
  · intro x
    let b n := (Equiv.ofBijective (c n) (hc n)).symm (p x n)
    have hb n : c n (b n) = p x n := (Equiv.ofBijective (c n) (hc n)).apply_symm_apply _
    have ht n : tr n (b (n + 1)) = b n := by
      apply (hc n).1
      rw [← htr, hb, hb, hcompat]
    obtain ⟨a, ha⟩ := hcomplete b ht
    refine ⟨a, hp ?_⟩
    funext n
    rw [hf, ha]
    exact hb n

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem integralSection_bijective (k : Type u) [Field k] [IsAlgClosed k]
    (l : ℕ) [Fact l.Prime] (E : Type e) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] : Function.Bijective (integralSection k l E) := by
  classical
  obtain ⟨r, hr, _⟩ := (Padic.coefficientExtension_integers_profinite_tower.{e, 0} l E).1
  let D := WeilConjectures.integralCoefficientSheafSystem l E (Spec (.of k))
  let U := op (finalObject k)
  let ev := sheafToPresheaf (Scheme.ProEt.topology (Spec (.of k))) RingCat.{max e (u + 1)} ⋙
    (evaluation _ RingCat.{max e (u + 1)}).obj U
  let q (n : ℕ) := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
  let c (n : ℕ) := constantSection k (Padic.coefficientExtensionRing l E (n + 1))
  have hc (n : ℕ) : Function.Bijective (c n) := constantSection_bijective _ _
  let p : ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E
      (Spec (.of k))).obj.obj U) → ∀ n : ℕ,
        (((constantSheaf (Scheme.ProEt.topology (Spec (.of k)))
          CommRingCat.{max e (u + 1)}).obj
            (CommRingCat.of
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).obj.obj U) :=
    fun x n ↦ ((limit.π D (op n)).hom.app U) x
  apply compatibleCoordinates_bijective (fun a n ↦ q n a) p
    (fun n ↦ Padic.coefficientExtensionTransition l E (n + 1))
    (fun n x ↦ ((WeilConjectures.integralCoefficientSheafTransition l E
      (Spec (.of k)) n).hom.app U) x) (fun n ↦ c n) (integralSection k l E)
  · intro a b hab
    apply r.injective
    apply Subtype.ext
    funext n
    rw [hr, hr]
    exact congrFun hab n
  · intro x y hxy
    apply Concrete.isLimit_ext (D ⋙ ev) (isLimitOfPreserves ev (limit.isLimit D))
    intro n
    exact congrFun hxy n.unop
  · intro b hb
    let z : Padic.coefficientExtensionPositiveLimit l E := ⟨b, by
      simpa only [Padic.coefficientExtensionPositiveLimit, Subring.mem_iInf,
        RingHom.mem_eqLocus, RingHom.comp_apply, Pi.evalRingHom_apply] using hb⟩
    refine ⟨r.symm z, ?_⟩
    funext n
    rw [← hr]
    exact congrArg (fun t : Padic.coefficientExtensionPositiveLimit l E ↦ t.val n)
      (r.apply_symm_apply z)
  · exact hc
  · exact constantSection_transition k l E
  · intro x n
    have h := congrArg (fun f ↦ f.hom.app U) (limit.w D (homOfLE n.le_succ).op)
    simp only [D, WeilConjectures.integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ] at h
    exact ConcreteCategory.congr_hom h x
  · exact fun a n ↦ integralSection_projection k l E n a


private theorem coefficientsIdentified (k : Type u) [Field k] [IsAlgClosed k] :
    CoefficientsIdentified.{u, e} k := by
  intro l hl E hE hA hfin
  exact ⟨fun _ ↦ constantSection_bijective _ _, integralSection_bijective _ _ _,
    integralSection_projection _ _ _, constantSection_transition _ _ _⟩

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance (priority := 3000) :
    (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.KFlatTotalTensorModel.smallSiteWEqualsLocallyBijective.{u + 1, u, u + 1}

local instance (priority := 3000) :
    HasSheafify (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
  SheafOfModules.KFlatTotalTensorModel.smallSiteHasSheafify.{u + 1, u, u + 1}

local instance : CommRing
    (((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B).obj.obj
      (op (finalObject k))) :=
  inferInstanceAs (CommRing (sectionRing k B))

/-- The unit comparison is exactly the degree-zero lift of the identity on B(s).
Source: Stacks 03EL, 07A4 (blueprint: lem-sf-point-ringed-evaluation-model). -/
def UnitNormalized (T : TensorModel B)
    [(pointModuleSections k B).PreservesZeroMorphisms] : Prop :=
  HEq T.unit
    ((HomologicalComplex.singleMapHomologicalComplex (W₁ := ModuleSheaves B)
      (W₂ := ModuleCat.{u + 1} (sectionRing k B)) (pointModuleSections k B) (.up ℤ) 0).app
      (SheafOfModules.unit.{u, u + 1, u + 1}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) ≪≫
      (HomologicalComplex.single (ModuleCat.{u + 1} (sectionRing k B)) (.up ℤ) 0).mapIso
        T.moduleUnit)


-- Keep the localization implementations folded in the representative arguments.
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory.Q DerivedCategory.Qh

private theorem resolving_exists (X : HomotopyCategory (ModuleSheaves B) (.up ℤ)) :
    ∃ (Y : (show ObjectProperty (HomotopyCategory (ModuleSheaves B) (.up ℤ)) from
        fun Y ↦ resolving B Y.as).FullSubcategory) (f : Y.obj ⟶ X),
      HomotopyCategory.quasiIso (ModuleSheaves B) (.up ℤ) f := by
  obtain ⟨P, f, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u} (R := B) X.as
  have hflat : ∀ n, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (P.X n) := by
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso B (P.X n)).symm (hf n)
  refine ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj P, hp, hflat⟩,
    (HomotopyCategory.quotient _ (.up ℤ)).map f, ?_⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq

@[reducible] private def typedModuleTotal :
    (CochainComplex (ModuleCat.{u + 1} (sectionRing k B)) ℤ ×
      CochainComplex (ModuleCat.{u + 1} (sectionRing k B)) ℤ) ⥤
      CochainComplex (ModuleCat.{u + 1} (sectionRing k B)) ℤ := moduleTotal B

private theorem tensorModel_naturality (T : TensorModel B)
    {X Y : Complexes B × Complexes B} (f : X ⟶ Y) :
    (SheafOfModules.KFlatTotalTensorModel.total B ⋙ complexSections k B).map f ≫
        (T.b Y.1 Y.2).hom =
      (T.b X.1 X.2).hom ≫
        (typedModuleTotal B).map
        (X := ((complexSections k B).obj X.1, (complexSections k B).obj X.2))
        (Y := ((complexSections k B).obj Y.1, (complexSections k B).obj Y.2))
        (Prod.mkHom ((complexSections k B).map f.1) ((complexSections k B).map f.2)) := by
  have ht := total_map_tensor ((complexSections k B).map f.1)
    ((complexSections k B).map f.2)
  exact (T.naturality X.1 X.2 Y.1 Y.2 f.1 f.2).trans
    (congrArg (fun t ↦ (T.b X.1 X.2).hom ≫ t) ht.symm)

private theorem tensorModel_derived [IsAlgClosed k] (T : TensorModel B)
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [(pointModuleSections k B).Additive]
    [PreservesFiniteLimits (pointModuleSections k B)]
    [PreservesFiniteColimits (pointModuleSections k B)] :
    DerivedCompatible B T := by
  constructor
  · intro L e hL
    let := hL
    let : (derivedSections B).IsLeftDerivedFunctor (derivedSectionsFactors B).hom
        (HomologicalComplex.quasiIso (ModuleSheaves B) (.up ℤ)) :=
      Functor.isLeftDerivedFunctor_of_inverts _ _ (derivedSectionsFactors B)
    let c := Functor.leftDerivedUnique (derivedSections B) L e
      (derivedSectionsFactors B).hom (HomologicalComplex.quasiIso (ModuleSheaves B) (.up ℤ))
    refine ⟨c, ?_⟩
    ext X
    have h := Functor.leftDerivedNatTrans_app L (derivedSections B) e
      (derivedSectionsFactors B).hom (HomologicalComplex.quasiIso (ModuleSheaves B) (.up ℤ))
      (𝟙 _) X
    change c.hom.app _ ≫ (derivedSectionsFactors B).hom.app X = e.app X ≫ _ at h
    simpa only [NatTrans.id_app, Category.comp_id, NatTrans.comp_app,
      Functor.whiskerLeft_app] using h.symm
  · intro S rS U r
    let A := ModuleSheaves B
    let M := ModuleCat.{u + 1} (sectionRing k B)
    let PR := resolving B
    let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ PR X.as
    set_option backward.isDefEq.respectTransparency true in
      have hff := resolvingRepresentativesFullyFaithfulWhiskering
        (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
        (D := DerivedCategory A) (DerivedCategory M)
        (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
        (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H
        (fun _ ↦ Iff.rfl) (resolving_exists B)
    obtain ⟨ff⟩ := hff
    let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory M)).mapIso
      (NatIso.prod (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
        (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
    let b : SheafOfModules.KFlatTotalTensorModel.total B ⋙ complexSections k B ≅
        ((complexSections k B).prod (complexSections k B)) ⋙ moduleTotal B :=
      NatIso.ofComponents (fun X ↦ T.b X.1 X.2)
        (fun f ↦ tensorModel_naturality B T f)
    exact tensorComparisonDescent (K := CochainComplex A ℤ)
      (H := CochainComplex M ℤ) (D := DerivedCategory A) (E := DerivedCategory M)
      (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := M))
      (complexSections k B) (derivedSections B) (derivedSectionsFactors B).hom
      PR (moduleResolving B) T.preserves_resolving ff'
      (SheafOfModules.KFlatTotalTensorModel.total B) (moduleTotal B) S U rS r b
      (fun _ _ ↦ inferInstance) (fun _ _ _ _ ↦ inferInstance)

private def resolvingWhiskering
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    (E : Type (u + 2)) [Category.{u + 2} E] :
    ((Functor.whiskeringLeft (resolving B).FullSubcategory
      (DerivedCategory (ModuleSheaves B)) E).obj
        ((resolving B).ι ⋙ DerivedCategory.Q)).FullyFaithful := by
  let A := ModuleSheaves B
  let P := resolving B
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ P X.as
  let p := HomotopyCategory.quotient A (.up ℤ)
  let f := H.lift (P.ι ⋙ p) (fun X ↦ X.property)
  have : f.Full := ⟨by
    intro X Y g
    obtain ⟨g, hg⟩ := p.map_surjective g.hom
    refine ⟨ObjectProperty.homMk g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg⟩
  have : f.EssSurj := ⟨by
    intro X
    obtain ⟨Y, hy⟩ := HomotopyCategory.quotient_obj_surjective X.obj
    refine ⟨⟨Y, (show H ((HomotopyCategory.quotient A (.up ℤ)).obj Y) by
      rw [hy]; exact X.property)⟩, ?_⟩
    exact ⟨ObjectProperty.isoMk H (eqToIso hy)⟩⟩
  have : (H.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage H.ι) :=
    restriction_localization _ DerivedCategory.Qh H (resolving_exists B)
  let ff := Localization.fullyFaithfulWhiskeringLeft (H.ι ⋙ DerivedCategory.Qh)
    ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage H.ι) E
  let fg := fullyFaithfulWhiskeringOfFullEssSurj f E
  exact (ff.comp fg).ofIso ((Functor.whiskeringLeft _ _ E).mapIso
    (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A)))


set_option maxHeartbeats 300000 in
-- Normalize the composite comparison and cancel its two inverse pairs.
private theorem scalarModel_derived [IsAlgClosed k]
    {B' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}}
    (a : B ⟶ B') (T : TensorModel B) (T' : TensorModel B') (S : ScalarModel a T T')
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [HasDerivedCategory.{u + 2} (ModuleSheaves B')]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B'))]
    [(pointModuleSections k B).Additive] [(pointModuleSections k B').Additive]
    [PreservesFiniteLimits (pointModuleSections k B)]
    [PreservesFiniteColimits (pointModuleSections k B)]
    [PreservesFiniteLimits (pointModuleSections k B')]
    [PreservesFiniteColimits (pointModuleSections k B')] :
    ScalarDerivedCompatible B a T T' S := by
  intro LS LM eS eM
  let P := resolving B
  let f := (moduleResolving B).lift (P.ι ⋙ complexSections k B)
    (fun X ↦ T.preserves_resolving X.obj X.property)
  let ff := resolvingWhiskering B
    (DerivedCategory (ModuleCat.{u + 1} (sectionRing k B')))
  let R := P.ι ⋙ complexSections k B ⋙ moduleExtend B a ⋙
    DerivedCategory.Q (C := ModuleCat.{u + 1} (sectionRing k B'))
  let l : P.ι ⋙ DerivedCategory.Q ⋙ LS ⋙ derivedSections B' ≅ R :=
    Functor.isoWhiskerRight eS (derivedSections B') ≪≫
    Functor.isoWhiskerLeft (P.ι ⋙ extend.{u + 1, u + 1, u} a) (derivedSectionsFactors B') ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft P.ι S.κ)
      (DerivedCategory.Q (C := ModuleCat.{u + 1} (sectionRing k B')))
  let r : P.ι ⋙ DerivedCategory.Q ⋙ derivedSections B ⋙ LM ≅ R :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft P.ι (derivedSectionsFactors B)) LM ≪≫
    Functor.isoWhiskerLeft f eM
  obtain ⟨δ, hδ, huniq⟩ := descent_normalized (P.ι ⋙ DerivedCategory.Q)
    (LS ⋙ derivedSections B') (derivedSections B ⋙ LM) ff R l r
  have normalize (X : Complexes B) (hX : P X) :
      (derivedSections B').map (eS.hom.app ⟨X, hX⟩) ≫
          (derivedSectionsFactors B').hom.app ((extend.{u + 1, u + 1, u} a).obj X) ≫
          DerivedCategory.Q.map (S.κ.hom.app X) =
        δ.hom.app (DerivedCategory.Q.obj X) ≫
          LM.map ((derivedSectionsFactors B).hom.app X) ≫
          eM.hom.app ⟨(complexSections k B).obj X,
            T.preserves_resolving X hX⟩ := by
    simpa only [l, r, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app, Category.assoc, ObjectProperty.ι_obj, Functor.comp_obj,
      f, ObjectProperty.lift] using hδ ⟨X, hX⟩
  refine ⟨δ, normalize, ?_⟩
  intro δ' hδ'
  apply huniq δ'
  intro X
  simpa only [l, r, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Category.assoc, ObjectProperty.ι_obj, Functor.comp_obj,
    f, ObjectProperty.lift] using hδ' X.obj X.property


/-- Final-object evaluation realizes the actual ringed point and its signed derived tensor.
Source: Stacks 0991, 03EL, 03D2, 07A4; blueprint order 1455
(blueprint: lem-sf-point-ringed-evaluation-model).

Proof plan:
1. The pointed final neighbourhood is initial: its only arrow to (U,u) is u.
   Restriction along u computes the stalk colimit; use the geometric-stalk topos point.
2. Restriction preserves ring and module operations. Identity change of scalars therefore
   identifies the ringed module inverse image with final-object evaluation. Apply
   point_proEtale_sections_exact for exactness and the induced derived functor.
3. Specialize the canonical ringed tensor comparison. On each total summand its inverse
   is the section tensor; the cochain differential has the sign (-1)^i in its second term.
4. Pullback preserves flat terms and K-flatness. The representative square in 07A4
   identifies the localized comparison with the canonical derived comparison. Two-variable
   resolving localization gives uniqueness, naturality and independence of models.
5. On three pure generators reassociation preserves order; the unitors multiply scalars;
   exchanging degrees i,j contributes (-1)^(ij). Extend by the coproduct universal property.
6. For every coefficient morphism the tensor square is the balanced identity
   (a tensor x) tensor (b tensor y) maps to ab tensor (x tensor y). No flatness of the
   coefficient map is needed; this includes identity maps and composites.
7. Localize these equalities on flat-term K-flat representatives. The localization
   universal property gives the derived scalar square and all descended constraints.
8. Finite constant sections are constant functions on the singleton point. Evaluation
   identifies the specified constant-section and residue transition maps.
9. Sections commute with the residue-system limit. Completeness of the finite extension's
   integer ring identifies it with that limit, via its actual quotient maps. All tensors
   used above are the ordinary ambient tensor, before any completion. -/
theorem point_ringed_evaluation_model (k : Type u) [Field k] [IsAlgClosed k] :
    (∃ T : ∀ B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
        TensorModel B,
      (∀ B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
        PointIdentification B ∧ TensorCoherent B (T B) ∧
        (∀ [(pointModuleSections k B).PreservesZeroMorphisms], UnitNormalized B (T B)) ∧
        PreservesFiniteLimits (pointModuleSections k B) ∧
        PreservesFiniteColimits (pointModuleSections k B) ∧
        ∀ [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
          [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
          [(pointModuleSections k B).Additive]
          [PreservesFiniteLimits (pointModuleSections k B)]
          [PreservesFiniteColimits (pointModuleSections k B)],
          DerivedCompatible B (T B)) ∧
      (∀ (B B' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
        (a : B ⟶ B'), ∃ S : ScalarModel a (T B) (T B'), ScalarCoherent a (T B) (T B') S ∧
          ∀ [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
            [HasDerivedCategory.{u + 2} (ModuleSheaves B')]
            [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
            [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B'))]
            [(pointModuleSections k B).Additive] [(pointModuleSections k B').Additive]
            [PreservesFiniteLimits (pointModuleSections k B)]
            [PreservesFiniteColimits (pointModuleSections k B)]
            [PreservesFiniteLimits (pointModuleSections k B')]
            [PreservesFiniteColimits (pointModuleSections k B')],
            ScalarDerivedCompatible B a (T B) (T B') S)) ∧
    CoefficientsIdentified.{u, e} k := by
  obtain ⟨T, hT, hS⟩ := point_evaluation_chain_models k
  refine ⟨⟨T, ?_, ?_⟩, coefficientsIdentified k⟩
  · intro B
    obtain ⟨hlim, hcol, -⟩ := (point_proEtale_sections_exact.{u, u + 2, u + 2} k).2 B
    exact ⟨pointIdentification B, (hT B).1, (by intro inst; exact (hT B).2),
      hlim, hcol, tensorModel_derived B (T B)⟩
  · intro B B' a
    obtain ⟨S, hS⟩ := hS B B' a
    exact ⟨S, hS, scalarModel_derived B a (T B) (T B') S⟩

end AlgebraicGeometry.ProEtale.PointEvaluation
