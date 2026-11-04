/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.CategoryTheory.ExactMonoidalLocalization
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.FinitePresentation
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Connected.Separation
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.RingTheory.ProEtale.PullbackProfinite
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.WeakDimension
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.ProperBaseChange.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.AlgebraicGeometry.GeometricStalkToposPoint
import WeilConjectures.SixFunctors.RingedSitePoint
import all WeilConjectures.SmoothPurity.RingedSitePointTensor
import WeilConjectures.Algebra.Homology.RingedSitePointFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
set_option linter.all false
set_option warn.classDefReducibility false

/-! # Native tensor comparison for sections at a geometric point

Source: Stacks 0991, 07A4 and 06YT. Final-object covers split over an algebraically
closed field; the resulting exact strong monoidal sections functor descends through
K-flat tensor localization for the specified derived-category models.
(blueprint: lem-sf-finite-point-native-tensor-comparison).
-/

@[expose] public section

universe u

namespace PointDerivedWork
section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
set_option autoImplicit false
noncomputable section
variable (k : Type u) [Field k] [IsAlgClosed k]
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})

private theorem evaluation_sheafification_unit_iso
    (P : PresheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B).obj) :
    IsIso (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app P).app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective ((toSheafify (Scheme.ProEt.topology (Spec (.of k)))
    P.presheaf).app (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
  let T := op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))
  refine ⟨fun x y hxy ↦ ?_, fun s ↦ ?_⟩
  · have hh := geometricField_cover_id k
      (Presheaf.equalizerSieve_mem (Scheme.ProEt.topology (Spec (.of k)))
        (toSheafify _ P.presheaf) x y hxy)
    change P.presheaf.map (𝟙 T) x = P.presheaf.map (𝟙 T) y at hh
    simpa only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using hh
  · obtain ⟨t, ht⟩ := geometricField_cover_id k
      (Presheaf.imageSieve_mem (Scheme.ProEt.topology (Spec (.of k)))
        (toSheafify _ P.presheaf) s)
    change (toSheafify _ P.presheaf).app T t =
      (sheafify _ P.presheaf).map (𝟙 T) s at ht
    rw [CategoryTheory.Functor.map_id] at ht
    exact ⟨t, ht⟩

private def presheafEvaluationCore
    {C : Type*} [Category C] (R : Cᵒᵖ ⥤ CommRingCat.{u}) (T : Cᵒᵖ) :
    (PresheafOfModules.evaluation.{u} (R ⋙ forget₂ _ _) T).CoreMonoidal :=
  Functor.CoreMonoidal.mk' (Iso.refl _) (fun _ _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_inv, Category.id_comp, Category.comp_id]; rfl)
    (by intros; simp only [Iso.refl_inv, Category.id_comp, Category.comp_id]; rfl)
    (by
      intro X Y Z
      change (𝟙 ((X.obj T ⊗ Y.obj T) ⊗ Z.obj T)) ≫
          (𝟙 (X.obj T ⊗ Y.obj T) ▷ Z.obj T) ≫ (α_ _ _ _).hom =
        (α_ (X.obj T) (Y.obj T) (Z.obj T)).hom ≫
          𝟙 (X.obj T ⊗ (Y.obj T ⊗ Z.obj T)) ≫ (X.obj T ◁ 𝟙 (Y.obj T ⊗ Z.obj T))
      simp)
    (by intros; simp only [Iso.refl_inv, Category.comp_id,
      MonoidalCategory.id_whiskerRight]; rfl)
    (by intros; simp only [Iso.refl_inv, Category.comp_id,
      MonoidalCategory.whiskerLeft_id]; rfl)

private instance pointSmall : EssentiallySmall.{u + 1} (Spec (.of k)).ProEt :=
  CategoryTheory.essentiallySmallSelf.{0, u, u + 1} _
private instance pointSheafify : HasSheafify (Scheme.ProEt.topology (Spec (.of k)))
    AddCommGrpCat.{u + 1} := SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}
private instance pointLocalEquivalences :
    (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}

@[instance_reducible]
private def pointEvaluationLax :
    letI := SheafOfModules.cochainModulesMonoidal B
    (SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))).LaxMonoidal := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients B
  letI := SheafOfModules.monoidalCategory B
  let R := (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let T := op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))
  letI : (SheafOfModules.forget.{u + 1} R).LaxMonoidal :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 R.obj)).rightAdjointLaxMonoidal
  letI : (PresheafOfModules.evaluation.{u + 1} R.obj T).Monoidal :=
    (presheafEvaluationCore B.obj T).toMonoidal
  change (SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj T).LaxMonoidal
  exact Functor.LaxMonoidal.comp _ _

set_option maxHeartbeats 2000000 in
private theorem pointEvaluation_tensor_iso
    (M N : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) :
    letI := SheafOfModules.cochainModulesMonoidal B
    letI := pointEvaluationLax k B
    IsIso (Functor.LaxMonoidal.μ
      (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) M N) := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients B
  letI := SheafOfModules.monoidalCategory B
  let R := (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let T := op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 R.obj)
  let ev := PresheafOfModules.evaluation.{u + 1} R.obj T
  letI : (SheafOfModules.forget.{u + 1} R).LaxMonoidal := adj.rightAdjointLaxMonoidal
  letI : ev.Monoidal := (presheafEvaluationCore B.obj T).toMonoidal
  letI := pointEvaluationLax k B
  haveI := evaluation_sheafification_unit_iso k B (M.val ⊗ N.val)
  haveI : IsIso (Functor.OplaxMonoidal.δ
      (PresheafOfModules.sheafification.{u + 1} (𝟙 R.obj)) M.val N.val) := by
    infer_instance
  haveI : IsIso (adj.counit.app M) := by dsimp [adj]; infer_instance
  haveI : IsIso (adj.counit.app N) := by dsimp [adj]; infer_instance
  haveI : IsIso (ev.map (adj.unit.app (M.val ⊗ N.val))) :=
    evaluation_sheafification_unit_iso k B (M.val ⊗ N.val)
  change IsIso (𝟙 _ ≫ ev.map
    (adj.unit.app (M.val ⊗ N.val) ≫
      (SheafOfModules.forget R).map
        (Functor.OplaxMonoidal.δ
          (PresheafOfModules.sheafification.{u + 1} (𝟙 R.obj)) M.val N.val ≫
          (adj.counit.app M ⊗ₘ adj.counit.app N))))
  rw [Category.id_comp, ev.map_comp]
  infer_instance

private theorem pointEvaluation_unit_iso :
    letI := SheafOfModules.cochainModulesMonoidal B
    letI := pointEvaluationLax k B
    IsIso (Functor.LaxMonoidal.ε
      (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))) := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients B
  letI := SheafOfModules.monoidalCategory B
  let R := (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let T := op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 R.obj)
  let ev := PresheafOfModules.evaluation.{u + 1} R.obj T
  letI : (SheafOfModules.forget.{u + 1} R).LaxMonoidal := adj.rightAdjointLaxMonoidal
  letI : ev.Monoidal := (presheafEvaluationCore B.obj T).toMonoidal
  letI := pointEvaluationLax k B
  haveI : IsIso (ev.map (adj.unit.app (𝟙_ _))) :=
    evaluation_sheafification_unit_iso k B (𝟙_ _)
  change IsIso (𝟙 _ ≫ ev.map (adj.unit.app (𝟙_ _) ≫
    (SheafOfModules.forget R).map
      (Functor.OplaxMonoidal.η (PresheafOfModules.sheafification.{u + 1} (𝟙 R.obj)))))
  rw [Category.id_comp, ev.map_comp]
  infer_instance

@[instance_reducible]
private def pointEvaluationMonoidal :
    letI := SheafOfModules.cochainModulesMonoidal B
    (AlgebraicGeometry.ProEtale.pointModuleSections k B).Monoidal := by
  letI : (pointModuleSections k B).LaxMonoidal := pointEvaluationLax k B
  haveI : IsIso (Functor.LaxMonoidal.ε (pointModuleSections k B)) :=
    pointEvaluation_unit_iso k B
  haveI (M N : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) :
      IsIso (Functor.LaxMonoidal.μ (pointModuleSections k B) M N) :=
    pointEvaluation_tensor_iso k B M N
  exact Functor.Monoidal.ofLaxMonoidal _

private theorem pointEvaluation_tensor_formula
    (M N : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B))
    (x : M.val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
    (y : N.val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) :
    letI := SheafOfModules.cochainModulesMonoidal B
    letI := pointEvaluationMonoidal k B
    Functor.LaxMonoidal.μ (pointModuleSections k B) M N
        (x ⊗ₜ[B.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))] y) =
      (((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (𝟙 ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B).obj)).unit.app
          (M.val ⊗ N.val) ≫
        (SheafOfModules.tensorObjIsoSheafification (R := B) M N).inv.val).app
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
        (x ⊗ₜ[B.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))] y) := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients B
  letI := SheafOfModules.monoidalCategory B
  letI := pointEvaluationMonoidal k B
  dsimp only [pointEvaluationMonoidal, Functor.Monoidal.ofLaxMonoidal]
  simp only [Functor.LaxMonoidal.μ]
  rfl

private def pointEvaluationBraided :
    letI := SheafOfModules.cochainModulesMonoidal B
    letI := SheafOfModules.symmetricCategory B
    letI := pointEvaluationMonoidal k B
    (pointModuleSections k B).Braided := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients B
  letI := SheafOfModules.monoidalCategory B
  letI := SheafOfModules.symmetricCategory B
  let R := (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let T := op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 R.obj)
  let ev := PresheafOfModules.evaluation.{u + 1} R.obj T
  letI : (SheafOfModules.forget.{u + 1} R).LaxMonoidal := adj.rightAdjointLaxMonoidal
  letI : (PresheafOfModules.sheafification.{u + 1} (𝟙 R.obj)).Braided := inferInstance
  letI : (SheafOfModules.forget.{u + 1} R).LaxBraided := by
    letI : (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).LaxMonoidal :=
      adj.rightAdjointLaxMonoidal
    exact adj.rightAdjointLaxBraided
  letI : ev.Monoidal := (presheafEvaluationCore B.obj T).toMonoidal
  letI : ev.Braided := by
    refine { braided := ?_ }
    intro M N
    change (𝟙 _) ≫ _ = _ ≫ (𝟙 _)
    rw [Category.id_comp, Category.comp_id]
    rfl
  letI : (SheafOfModules.forget R ⋙ ev).LaxMonoidal := Functor.LaxMonoidal.comp _ _
  letI : (SheafOfModules.forget R ⋙ ev).LaxBraided := inferInstance
  letI := pointEvaluationMonoidal k B
  refine { braided := ?_ }
  intro M N
  exact Functor.LaxBraided.braided (F := SheafOfModules.forget R ⋙ ev) M N
end
end
end PointDerivedWork

namespace PointDerivedWork
section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
noncomputable section
set_option autoImplicit false
namespace AlgebraicGeometry.ProEtale
open _root_.AlgebraicGeometry.ProEtale
variable (k : Type u) [Field k] [IsAlgClosed k]

private def finalNeighbourhood : Scheme.ProEtaleGeometricNeighbourhood (𝟙 (Spec (.of k))) :=
  StructuredArrow.mk (Y := Scheme.ProEt.mk (𝟙 (Spec (.of k)))) (𝟙 _)

private def finalNeighbourhood_initial : IsInitial (finalNeighbourhood k) :=
  StructuredArrow.mkIdInitial

private def stalkEvaluationIso :
    Scheme.proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k))) ≅
      (sheafSections (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) := by
  let η : (sheafSections (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))).obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) ⟶
      Scheme.proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k))) :=
    { app F := colimit.ι (Scheme.proEtaleGeometricStalkDiagram (𝟙 _) F)
        (op (finalNeighbourhood k))
      naturality {F G} f := by
        exact (colimit.ι_map
          (Functor.whiskerLeft (Scheme.proEtaleGeometricNeighbourhoodForget (𝟙 _)).op f.hom)
          (op (finalNeighbourhood k))).symm }
  have hη (F) : IsIso (η.app F) :=
    isIso_ι_of_isTerminal (finalNeighbourhood_initial k).op _
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact (asIso η).symm

private def pointGeometricMorphism :
    GeometricMorphism (Type (u + 1))
      (Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))) where
  inverse := (sheafSections (Scheme.ProEt.topology (Spec (.of k)))
    (Type (u + 1))).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))
  direct := Scheme.proEtaleFunctionSheafFunctor (𝟙 (Spec (.of k)))
  adj := (Scheme.proEtaleFunctionAdjunction (𝟙 (Spec (.of k))))
    |>.ofNatIsoLeft (stalkEvaluationIso k)
  leftExact := by
    have : PreservesFiniteLimits
        (Scheme.proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k)))) := by
      dsimp [Scheme.proEtaleGeometricSetStalkFunctor]
      infer_instance
    exact preservesFiniteLimits_of_natIso (stalkEvaluationIso k)

private def pointPresentation
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :
    RingedSitePoint B (pointGeometricMorphism k) where
  ring := CommRingCat.of (B.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
  ringUnderlying := Iso.refl _
  ringAdd := by intro T a b t h x; exact h _ x
  ringMul := by intro T a b t h x; exact h _ x
  ringZero := by intro T a h x; exact h _ x
  ringOne := by intro T a h x; exact h _ x
  modules := pointModuleSections k B
  moduleUnderlying := Iso.refl _
  moduleAdd := by intro M T a b t h x; exact h _ x
  moduleZero := by intro M T a h x; exact h _ x
  moduleSMul := by intro M T a b t h x; exact h _ x
  modules_additive := by exact ⟨by intros; rfl⟩

private theorem pointSections_leftAdjoint
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :
    (pointModuleSections k B).IsLeftAdjoint := by
  let s := pointPresentation k B
  let p := pointGeometricMorphism k
  have : PreservesFiniteLimits p.inverse := p.leftExact
  have : (RingedSitePoint.constant (Type (u + 1))).IsEquivalence :=
    RingedSitePoint.setEquivalence.isEquivalence_inverse
  have : PreservesFiniteLimits
      (p.inverse ⋙ RingedSitePoint.constant (Type (u + 1))) :=
    comp_preservesFiniteLimits _ _
  let adj : (p.inverse ⋙ RingedSitePoint.constant (Type (u + 1))) ⊣
      (RingedSitePoint.setEquivalence.functor ⋙ p.direct) :=
    p.adj.comp RingedSitePoint.setEquivalence.symm.toAdjunction
  obtain ⟨V, ⟨hV⟩⟩ := SheafOfModules.CochainInversePairing.inverseImageModuleAdjunction_exists
    B (RingedSitePoint.pointRing s.ring) _ _ adj (RingedSitePoint.pointInverse s)
  have : (RingedSitePoint.pointInverse s).modules.IsLeftAdjoint := hV.isLeftAdjoint
  have : ((RingedSitePoint.pointInverse s).modules ⋙
      RingedSitePoint.moduleEval s.ring).IsLeftAdjoint := inferInstance
  exact inferInstanceAs (((RingedSitePoint.pointInverse s).modules ⋙
    RingedSitePoint.moduleEval s.ring).IsLeftAdjoint)

private theorem pointSections_preservesFlat
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients B
    letI := SheafOfModules.monoidalCategory B
    (pointModuleSections k B).PreservesFlat := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients B
  letI := SheafOfModules.monoidalCategory B
  refine ⟨fun {M} hM ↦ ?_⟩
  have hsite : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) M :=
    SheafOfModules.flatOnSite_of_categorical_adapted B M hM
  exact (ModuleCat.flat_iff_flat
    (R := B.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
    ((pointModuleSections k B).obj M)).2 ((pointPresentation k B).flat M hsite)

end AlgebraicGeometry.ProEtale
end
end
end PointDerivedWork

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
noncomputable section
variable (k : Type u) [Field k] [IsAlgClosed k]
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
namespace AlgebraicGeometry.ProEtale.FinitePointComparison
variable [∀ R : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
  HasDerivedCategory.{u + 1} (Modules k R)]

private def pointDerivedMonoidal : (sections k B).Monoidal := by
  let J := Scheme.ProEt.topology (Spec (.of k))
  letI := RingedDerivedNative.moduleMonoidal.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleSymmetric.{u + 1, u, 0} J B
  letI := RingedDerivedNative.modulePreadditive.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleClosed.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleGrothendieck.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleFlat.{u + 1, u, 0} J B
  letI := RingedDerivedNative.countableColimits.{u + 1, u, 0} J B
  letI := RingedDerivedNative.tensorLeftColimits.{u + 1, u, 0} J B
  letI := RingedDerivedNative.tensorRightColimits.{u + 1, u, 0} J B
  let F := pointModuleSections k B
  letI : F.Monoidal := PointDerivedWork.pointEvaluationMonoidal k B
  letI : F.PreservesFlat :=
    PointDerivedWork.AlgebraicGeometry.ProEtale.pointSections_preservesFlat k B
  letI : F.IsLeftAdjoint :=
    PointDerivedWork.AlgebraicGeometry.ProEtale.pointSections_leftAdjoint k B
  letI : F.Additive := ⟨by intros; rfl⟩
  exact F.specifiedModel_monoidal

private theorem pointDerived_braid (P Q : DerivedCategory.{u + 1} (Modules k B)) :
    letI := pointDerivedMonoidal k B
    Functor.OplaxMonoidal.δ (sections k B) P Q ≫ (β_ _ _).hom =
      (sections k B).map (β_ P Q).hom ≫
        Functor.OplaxMonoidal.δ (sections k B) Q P := by
  let J := Scheme.ProEt.topology (Spec (.of k))
  letI := RingedDerivedNative.moduleMonoidal.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleSymmetric.{u + 1, u, 0} J B
  letI := RingedDerivedNative.modulePreadditive.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleClosed.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleGrothendieck.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleFlat.{u + 1, u, 0} J B
  letI := RingedDerivedNative.countableColimits.{u + 1, u, 0} J B
  letI := RingedDerivedNative.tensorLeftColimits.{u + 1, u, 0} J B
  letI := RingedDerivedNative.tensorRightColimits.{u + 1, u, 0} J B
  let F := pointModuleSections k B
  letI : F.Monoidal := PointDerivedWork.pointEvaluationMonoidal k B
  letI : F.PreservesFlat :=
    PointDerivedWork.AlgebraicGeometry.ProEtale.pointSections_preservesFlat k B
  letI : F.IsLeftAdjoint :=
    PointDerivedWork.AlgebraicGeometry.ProEtale.pointSections_leftAdjoint k B
  letI : F.Additive := ⟨by intros; rfl⟩
  letI : F.Braided := PointDerivedWork.pointEvaluationBraided k B
  have hF : ∀ X Y : Modules k B,
      F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
        Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
    intro X Y
    simpa only [Functor.Monoidal.inv_μ] using
      (RingedDerivedNative.inverse_braiding F X Y).symm
  exact (F.specifiedModel_braid hF P Q).symm

-- Native sheaf tensor instances require several kernel normalization steps here.
set_option maxHeartbeats 2000000 in
private theorem pointDerived_representative :
    ∀ (P Q : CochainComplex (Modules k B) ℤ)
    (hP : ∃ b : ℤ, (DerivedCategory.Q.obj P).IsLE b)
    (hQ : ∃ b : ℤ, (DerivedCategory.Q.obj Q).IsLE b),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) P →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) Q →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (P.X i)) →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (Q.X i)) →
    ∃ b : ((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
        (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj P ⊗
          ((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj Q),
      (∀ (p q n : ℤ) (h : p + q = n)
        (x : (P.X p).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
        (y : (Q.X q).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))),
        (b.hom.f n)
          (WeilConjectures.coefficientTensorGenerator.{0, u + 1, u}
            (Scheme.ProEt.topology (Spec (.of k))) B P Q p q n h
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) x y) =
          (CochainComplex.ιMapBifunctor
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj P)
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj Q)
            (curriedTensor _) p q n h) (x ⊗ₜ[SectionRing k B] y)) ∧
      (sections k B).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          (pointModuleSections k B).mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
          DerivedCategory.Q.map b.hom =
        (pointDerivedMonoidal k B).δ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
          ((pointModuleSections k B).mapDerivedCategoryFactors.hom.app P ⊗ₘ
            (pointModuleSections k B).mapDerivedCategoryFactors.hom.app Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj P)
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj Q) := by
  intro P Q _ _ _ _ _ _
  let J := Scheme.ProEt.topology (Spec (.of k))
  letI := RingedDerivedNative.moduleMonoidal.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleSymmetric.{u + 1, u, 0} J B
  letI := RingedDerivedNative.modulePreadditive.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleClosed.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleGrothendieck.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleFlat.{u + 1, u, 0} J B
  letI := RingedDerivedNative.countableColimits.{u + 1, u, 0} J B
  letI := RingedDerivedNative.tensorLeftColimits.{u + 1, u, 0} J B
  letI := RingedDerivedNative.tensorRightColimits.{u + 1, u, 0} J B
  let F := pointModuleSections k B
  letI : F.Monoidal := PointDerivedWork.pointEvaluationMonoidal k B
  letI : F.PreservesFlat :=
    PointDerivedWork.AlgebraicGeometry.ProEtale.pointSections_preservesFlat k B
  letI : F.IsLeftAdjoint :=
    PointDerivedWork.AlgebraicGeometry.ProEtale.pointSections_leftAdjoint k B
  letI : F.Additive := ⟨by intros; rfl⟩
  let e := F.mapCochainComplexμIso P Q
  refine ⟨e.symm, ?_, ?_⟩
  · intro p q n h x y
    have hx := ConcreteCategory.congr_hom
      (F.ιTensorObj_mapCochainComplexμIso_hom_f P Q p q n h)
        (x ⊗ₜ[SectionRing k B] y)
    have hx' : (e.hom.f n)
        ((CochainComplex.ιMapBifunctor
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q)
          (curriedTensor _) p q n h) (x ⊗ₜ[SectionRing k B] y)) =
      WeilConjectures.coefficientTensorGenerator.{0, u + 1, u}
        (Scheme.ProEt.topology (Spec (.of k))) B P Q p q n h
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) x y := by
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hx
      dsimp only [e]
      erw [hx, PointDerivedWork.pointEvaluation_tensor_formula k B]
      rfl
    apply (ConcreteCategory.bijective_of_isIso (e.hom.f n)).1
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.f n) e.inv_hom_id)
      (WeilConjectures.coefficientTensorGenerator.{0, u + 1, u}
        (Scheme.ProEt.topology (Spec (.of k))) B P Q p q n h
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) x y)
    exact hi.trans hx'.symm
  · exact F.specifiedModel_comparison_cochain P Q

end AlgebraicGeometry.ProEtale.FinitePointComparison

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite
noncomputable section
namespace AlgebraicGeometry.ProEtale.FinitePointComparison
variable (k : Type u) [Field k] [IsAlgClosed k]
  [∀ R : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
    HasDerivedCategory.{u + 1} (Modules k R)]
variable (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})

private theorem bounded_sections (P : DerivedCategory.{u + 1} (Modules k B))
    (hP : ∃ b : ℤ, P.IsLE b) : ∃ b : ℤ, ((sections k B).obj P).IsLE b := by
  obtain ⟨b, hb⟩ := hP
  letI := hb
  exact ⟨b, Functor.isLE_mapDerivedCategory_obj (pointModuleSections k B) P b⟩

private theorem bounded_tensor (P Q : DerivedCategory.{u + 1} (Modules k B))
    (hP : ∃ b : ℤ, P.IsLE b) (hQ : ∃ b : ℤ, Q.IsLE b) :
    ∃ b : ℤ, (P ⊗ Q).IsLE b := by
  let J := Scheme.ProEt.topology (Spec (.of k))
  letI := RingedDerivedNative.moduleMonoidal.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleSymmetric.{u + 1, u, 0} J B
  letI := RingedDerivedNative.modulePreadditive.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleClosed.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleGrothendieck.{u + 1, u, 0} J B
  letI := RingedDerivedNative.moduleFlat.{u + 1, u, 0} J B
  letI := RingedDerivedNative.countableColimits.{u + 1, u, 0} J B
  letI := RingedDerivedNative.tensorLeftColimits.{u + 1, u, 0} J B
  letI := RingedDerivedNative.tensorRightColimits.{u + 1, u, 0} J B
  obtain ⟨b, hb⟩ := hP
  obtain ⟨c, hc⟩ := hQ
  letI := hb
  letI := hc
  exact ⟨b + c, DerivedCategory.isLE_tensor P Q b c⟩


private def tensorComparison_of_monoidal
    (e : (sections k B).Monoidal)
    (hβ : ∀ P Q : DerivedCategory.{u + 1} (Modules k B),
      e.δ P Q ≫ (β_ _ _).hom = (sections k B).map (β_ P Q).hom ≫ e.δ Q P)
    (hrep : ∀ (P Q : CochainComplex (Modules k B) ℤ)
    (hP : ∃ b : ℤ, (DerivedCategory.Q.obj P).IsLE b)
    (hQ : ∃ b : ℤ, (DerivedCategory.Q.obj Q).IsLE b),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) P →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) Q →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (P.X i)) →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (Q.X i)) →
    ∃ b : ((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
        (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj P ⊗
          ((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj Q),
      (∀ (p q n : ℤ) (h : p + q = n)
        (x : (P.X p).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
        (y : (Q.X q).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))),
        (b.hom.f n)
          (WeilConjectures.coefficientTensorGenerator.{0, u + 1, u}
            (Scheme.ProEt.topology (Spec (.of k))) B P Q p q n h
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) x y) =
          (CochainComplex.ιMapBifunctor
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj P)
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj Q)
            (curriedTensor _) p q n h) (x ⊗ₜ[SectionRing k B] y)) ∧
      (sections k B).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          (pointModuleSections k B).mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
          DerivedCategory.Q.map b.hom =
        e.δ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
          ((pointModuleSections k B).mapDerivedCategoryFactors.hom.app P ⊗ₘ
            (pointModuleSections k B).mapDerivedCategoryFactors.hom.app Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj P)
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj Q)
) : TensorComparison k B := by
  letI := e
  have hu : ∃ b : ℤ, (𝟙_ (DerivedCategory.{u + 1} (Modules k B))).IsLE b := by
    refine ⟨0, ?_⟩
    have hunit : (DerivedCategory.Q.{u + 1}.obj
        (𝟙_ (CochainComplex (Modules k B) ℤ))).IsLE 0 := by
      rw [DerivedCategory.isLE_Q_obj_iff]
      change CochainComplex.IsLE
        ((HomologicalComplex.single (Modules k B) (.up ℤ) 0).obj
          (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B))) 0
      infer_instance
    exact DerivedCategory.TStructure.t.isLE_of_iso
      (RingedDerivedNative.unitIso.{u + 1, u, 0, u + 1}
        (Scheme.ProEt.topology (Spec (.of k))) B).symm 0
  refine {
    tau := fun P Q _ _ ↦ (Functor.Monoidal.μIso (sections k B) P Q).symm
    unit := (Functor.Monoidal.εIso (sections k B)).symm
    naturality := ?_
    bounded_tensor := bounded_tensor k B
    bounded_sections := bounded_sections k B
    associativity := ?_
    symmetry := ?_
    bounded_unit := hu
    left_unit := ?_
    right_unit := ?_
    representative := ?_ }
  · intro P Q P' Q' _ _ _ _ f g
    exact (Functor.OplaxMonoidal.δ_natural (sections k B) f g).symm
  · intro P Q R _ _ _
    simpa only [Iso.symm_hom, Functor.Monoidal.μIso_inv, tensorHom_id, id_tensorHom] using
      (Functor.OplaxMonoidal.associativity (sections k B) P Q R)
  · intro P Q _ _
    exact hβ P Q
  · intro P _
    simpa only [Iso.symm_hom, Functor.Monoidal.μIso_inv,
      Functor.Monoidal.εIso_inv, Functor.Monoidal.inv_μ, Functor.Monoidal.inv_ε] using
      RingedDerivedNative.inverse_leftUnitor_tensor (sections k B) P
  · intro P _
    simpa only [Iso.symm_hom, Functor.Monoidal.μIso_inv,
      Functor.Monoidal.εIso_inv, Functor.Monoidal.inv_μ, Functor.Monoidal.inv_ε] using
      RingedDerivedNative.inverse_rightUnitor_tensor (sections k B) P
  · exact hrep

private def pointTensorComparison : TensorComparison k B :=
  tensorComparison_of_monoidal k B (pointDerivedMonoidal k B)
    (pointDerived_braid k B) (pointDerived_representative k B)

/-- Sections have the natural native derived tensor comparison, with its actual
cochain tensor formula, symmetry and both unit constraints.
Source: Stacks 07A4, 06YT and 0991
(blueprint: lem-sf-finite-point-native-tensor-comparison).

Proof: covers of the final pro-etale object contain the identity, so sheafification
is an isomorphism on final sections. Thus sections are strong symmetric monoidal.
The geometric point at the identity has initial pointed neighborhood the final
object, identifying its inverse image with final sections; its module functor is
therefore a left adjoint and preserves flat objects. The exact monoidal localization
construction gives the tensor comparison for the supplied derived-category model.
Its cochain square and summand formula give the required representative equation.
Exactness preserves the upper cohomological bound, native tensor adds bounds, and
the localization of the degree-zero regular module identifies the coefficient unit.
The oplax associativity, braiding and inverse-unitor equations give all constraints.
-/
theorem finitePointTensorComparison_exists : Nonempty (TensorComparison k B) :=
  ⟨pointTensorComparison k B⟩

end AlgebraicGeometry.ProEtale.FinitePointComparison
