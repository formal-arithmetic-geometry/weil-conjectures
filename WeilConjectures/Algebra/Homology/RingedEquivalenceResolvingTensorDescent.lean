/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIsoSupplement
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.CategoryTheory.Localization.Pi
import Mathlib.CategoryTheory.Monoidal.Braided.Transport

/-! # Resolving tensor descent across a ringed coefficient equivalence

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 0G7D, 06YT and 06YU;
the exact-equivalence transfer argument in the DAG
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent).

The source tensor and its specified model maps are parameters: `TensorModel` spells
out the ordinary K-flat tensor and its native constraints. The conclusion constructs
such a tensor on the target, with the prescribed comparison, independently of a
functorial choice of resolutions. Countable coproducts suffice throughout.

## Main definitions and statements

- `TensorModel`: ordinary K-flat representative comparisons and their coherence.
- `derivedEquivalence`: the existing exact-functor derived equivalence.
- `TransferSpec`: the normalized coherent comparison and independence of tensor presentation.
- `ringed_equivalence_resolving_tensor_descent`: transfer of localization and derived tensor.
-/

@[expose] public noncomputable section


set_option autoImplicit false
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v r a b wR wA

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.RingedEquivalenceTensorDescent

attribute [local instance 11000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [local instance 11000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restrict a strong monoidal functor to full monoidal subcategories. -/
private def coreLift {X Y : Type*} [Category* X] [Category* Y]
    [MonoidalCategory X] [MonoidalCategory Y]
    (P : ObjectProperty X) (Q : ObjectProperty Y) [P.IsMonoidal] [Q.IsMonoidal]
    (F : X ⥤ Y) (s : F.CoreMonoidal) (hF : ∀ Z : X, P Z → Q (F.obj Z)) :
    (Q.lift (P.ι ⋙ F) (fun Z ↦ hF Z.obj Z.property)).CoreMonoidal where
  εIso := Q.isoMk s.εIso
  μIso Z T := Q.isoMk (s.μIso Z.obj T.obj)
  μIso_hom_natural_left f T := by
    apply ObjectProperty.hom_ext
    exact s.μIso_hom_natural_left f.hom T.obj
  μIso_hom_natural_right Z f := by
    apply ObjectProperty.hom_ext
    exact s.μIso_hom_natural_right Z.obj f.hom
  associativity Z T U := by
    apply ObjectProperty.hom_ext
    exact s.associativity Z.obj T.obj U.obj
  left_unitality Z := by
    apply ObjectProperty.hom_ext
    exact s.left_unitality Z.obj
  right_unitality Z := by
    apply ObjectProperty.hom_ext
    exact s.right_unitality Z.obj

/-- Retain both halves of the specified monoidal isomorphisms literally. -/
@[implicit_reducible]
private def coreOfMonoidal {X Y : Type*} [Category* X] [Category* Y]
    [MonoidalCategory X] [MonoidalCategory Y] (F : X ⥤ Y) [F.Monoidal] :
    F.CoreMonoidal where
  εIso := Functor.Monoidal.εIso F
  μIso := Functor.Monoidal.μIso F
  μIso_hom_natural_left := Functor.LaxMonoidal.μ_natural_left F
  μIso_hom_natural_right := Functor.LaxMonoidal.μ_natural_right F
  associativity := Functor.LaxMonoidal.associativity F
  left_unitality := Functor.LaxMonoidal.left_unitality F
  right_unitality := Functor.LaxMonoidal.right_unitality F

/-- A natural braided equation can be checked on essentially surjective images. -/
private theorem braidedOfImages {X Y Z : Type*}
    [Category* X] [Category* Y] [Category* Z]
    [MonoidalCategory Y] [MonoidalCategory Z]
    [BraidedCategory Y] [BraidedCategory Z]
    (L : X ⥤ Y) [L.EssSurj] (G : Y ⥤ Z) [G.Monoidal]
    (h : ∀ U V : X,
      Functor.LaxMonoidal.μ G (L.obj U) (L.obj V) ≫
          G.map (β_ (L.obj U) (L.obj V)).hom =
        (β_ (G.obj (L.obj U)) (G.obj (L.obj V))).hom ≫
          Functor.LaxMonoidal.μ G (L.obj V) (L.obj U)) :
    ∀ U V, Functor.LaxMonoidal.μ G U V ≫ G.map (β_ U V).hom =
      (β_ (G.obj U) (G.obj V)).hom ≫ Functor.LaxMonoidal.μ G V U := by
  intro U V
  let i := L.objObjPreimageIso U
  let j := L.objObjPreimageIso V
  apply (cancel_epi (G.map i.hom ⊗ₘ G.map j.hom)).1
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← G.map_comp,
    BraidedCategory.braiding_naturality, G.map_comp, ← Category.assoc, h]
  rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural,
    ← BraidedCategory.braiding_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Faithful braided postcomposition detects the braided functor equation. -/
private theorem braidedOfPostcomp {X Y Z : Type*}
    [Category* X] [Category* Y] [Category* Z]
    [MonoidalCategory X] [MonoidalCategory Y] [MonoidalCategory Z]
    [BraidedCategory X] [BraidedCategory Y] [BraidedCategory Z]
    (G : X ⥤ Y) (F : Y ⥤ Z) [G.Monoidal] [F.Braided] [F.Faithful]
    (hcomp : ∀ U V,
      (Functor.LaxMonoidal.μ F (G.obj U) (G.obj V) ≫
        F.map (Functor.LaxMonoidal.μ G U V)) ≫ F.map (G.map (β_ U V).hom) =
      (β_ (F.obj (G.obj U)) (F.obj (G.obj V))).hom ≫
        Functor.LaxMonoidal.μ F (G.obj V) (G.obj U) ≫
          F.map (Functor.LaxMonoidal.μ G V U)) :
    ∀ U V, Functor.LaxMonoidal.μ G U V ≫ G.map (β_ U V).hom =
      (β_ (G.obj U) (G.obj V)).hom ≫ Functor.LaxMonoidal.μ G V U := by
  intro U V
  apply F.map_injective
  have h := hcomp U V
  simp only [Category.assoc] at h
  rw [← Functor.LaxBraided.braided_assoc (F := F)] at h
  apply (cancel_epi (Functor.LaxMonoidal.μ F (G.obj U) (G.obj V))).1
  simpa only [Functor.map_comp, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transfer a coherent functor through a monoidal equivalence. The specified
comparison becomes monoidal; its tensor and unit equations are preserved. -/
private theorem coreAcrossEquivalence {X Y Z : Type*}
    [Category* X] [Category* Y] [Category* Z]
    [MonoidalCategory X] [MonoidalCategory Y] [MonoidalCategory Z]
    [BraidedCategory X] [BraidedCategory Y] [BraidedCategory Z]
    (e : X ≌ Y) [e.functor.Braided] (F : X ⥤ Z) [F.Braided]
    (Q : Y ⥤ Z) (i : e.functor ⋙ Q ≅ F) :
    ∃ s : Q.CoreMonoidal, letI := s.toMonoidal;
      i.hom.IsMonoidal ∧ ∀ U V,
        Functor.LaxMonoidal.μ Q U V ≫ Q.map (β_ U V).hom =
          (β_ (Q.obj U) (Q.obj V)).hom ≫ Functor.LaxMonoidal.μ Q V U := by
  let : e.inverse.Monoidal := e.inverseMonoidal
  have : e.IsMonoidal := inferInstance
  have : e.unitIso.hom.IsMonoidal := inferInstance
  have : e.counitIso.hom.IsMonoidal := inferInstance
  have : e.counitIso.symm.hom.IsMonoidal :=
    inferInstanceAs (NatTrans.IsMonoidal e.counitIso.inv)
  let hbraid := Functor.LaxBraided.ofNatIso e.counitIso.symm
  let : e.inverse.LaxBraided := ⟨braidedOfPostcomp e.inverse e.functor
    (fun U V ↦ by
      exact hbraid.braided U V)⟩
  let : e.inverse.Braided := {}
  let φ : e.inverse ⋙ F ≅ Q :=
    Functor.isoWhiskerLeft e.inverse i.symm ≪≫ e.invFunIdAssoc Q
  let : Q.Monoidal := Functor.Monoidal.transport φ
  have hφ : φ.hom.IsMonoidal := Functor.Monoidal.natTransIsMonoidal_of_transport φ
  let ψ : F ≅ e.functor ⋙ Q :=
    (e.funInvIdAssoc F).symm ≪≫ Functor.isoWhiskerLeft e.functor φ
  have hψ : ψ.hom.IsMonoidal := by
    have hu : (e.funInvIdAssoc F).hom.IsMonoidal := by
      simp only [Equivalence.funInvIdAssoc, Iso.trans_hom, Iso.symm_hom,
        Functor.isoWhiskerRight_hom]
      infer_instance
    have : (e.funInvIdAssoc F).inv.IsMonoidal := inferInstance
    simp only [ψ, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom]
    infer_instance
  have he : ψ = i.symm := by
    apply Iso.ext
    ext T
    dsimp [ψ, φ]
    simp only [Equivalence.funInvIdAssoc_inv_app, Equivalence.invFunIdAssoc_hom_app]
    have hn := i.inv.naturality (e.unit.app T)
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn
    rw [← Category.assoc, hn, Category.assoc, ← Q.map_comp,
      e.functor_unit_comp, Q.map_id, Category.comp_id]
  have hi : i.inv.IsMonoidal := by simpa only [he, Iso.symm_hom] using hψ
  have : i.symm.hom.IsMonoidal := hi
  have hi' : i.hom.IsMonoidal := by
    exact inferInstanceAs (NatTrans.IsMonoidal i.symm.inv)
  let : Q.LaxBraided := Functor.LaxBraided.ofNatIso φ
  exact ⟨coreOfMonoidal Q, hi',
    fun U V ↦ Functor.LaxBraided.braided (F := Q) U V⟩

/-- Restrict an equivalence using preservation in both directions. No choices of
representatives or new equivalences of the ambient categories are introduced. -/
private def equivLift {X Y : Type*} [Category* X] [Category* Y]
    (e : X ≌ Y) (P : ObjectProperty X) (Q : ObjectProperty Y)
    (hF : ∀ T : X, P T → Q (e.functor.obj T))
    (hG : ∀ T : Y, Q T → P (e.inverse.obj T)) : P.FullSubcategory ≌ Q.FullSubcategory where
  functor := Q.lift (P.ι ⋙ e.functor) (fun T ↦ hF T.obj T.property)
  inverse := P.lift (Q.ι ⋙ e.inverse) (fun T ↦ hG T.obj T.property)
  unitIso := NatIso.ofComponents (fun T ↦ P.isoMk (e.unitIso.app T.obj)) (by
    intro T U f
    apply ObjectProperty.hom_ext
    exact e.unitIso.hom.naturality f.hom)
  counitIso := NatIso.ofComponents (fun T ↦ Q.isoMk (e.counitIso.app T.obj)) (by
    intro T U f
    apply ObjectProperty.hom_ext
    exact e.counitIso.hom.naturality f.hom)
  functor_unitIso_comp T := ObjectProperty.hom_ext _ (e.functor_unit_comp T.obj)

section CountableTotal

variable {B : Type a} [Category.{b} B] [Abelian B]
  [MonoidalCategory B] [MonoidalPreadditive B] [HasCountableCoproducts B]
  [leftCountable : ∀ (I : Type) [Countable I] (X : B),
    PreservesColimitsOfShape (Discrete I) (tensorLeft X)]
  [rightCountable : ∀ (I : Type) [Countable I] (X : B),
    PreservesColimitsOfShape (Discrete I) (tensorRight X)]

/-- Countable sums give the existing binary graded tensor.
Source: Stacks 06YL (blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
instance gradedTensor (X Y : GradedObject ℤ B) : X.HasTensor Y := fun _ ↦ inferInstance

/-- Right tensoring commutes with the countable sums in reassociation.
Source: Stacks 06YL (blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
instance gradedGood12 (X Y Z : GradedObject ℤ B) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := fun _ _ ↦ inferInstance

/-- Left tensoring commutes with the countable sums in reassociation.
Source: Stacks 06YL (blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
instance gradedGood23 (X Y Z : GradedObject ℤ B) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := fun _ _ ↦ inferInstance

/-- The existing fourfold tensor uses only countable sums.
Source: Stacks 06YL (blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
instance gradedFour (W X Y Z : GradedObject ℤ B) :
    GradedObject.HasTensor₄ObjExt W X Y Z := fun _ _ ↦ inferInstance

/-- Additive left tensoring preserves the zero object used by the total unit.
Source: Stacks 06YL (blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
instance tensorLeftEmpty (X : B) :
    PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X) :=
  Functor.preservesInitialObject_of_preservesZeroMorphisms _

/-- Additive right tensoring preserves the zero object used by the total unit.
Source: Stacks 06YL (blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
instance tensorRightEmpty (X : B) :
    PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X) :=
  Functor.preservesInitialObject_of_preservesZeroMorphisms _

/-- The native signed direct-sum monoidal structure, using the countable-sum instances above.
Source: Stacks 06YL (blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
instance countableCochainMonoidal : MonoidalCategory (CochainComplex B ℤ) :=
  HomologicalComplex.monoidalCategory B (.up ℤ)

attribute [local instance 12000] countableCochainMonoidal
  gradedTensor gradedGood12 gradedGood23 gradedFour tensorLeftEmpty tensorRightEmpty

/-- Unit total complexes are K-flat by the two unitors. -/
private theorem totalKFlat_unit :
    CochainComplex.IsKFlatForTotalTensor (𝟙_ (CochainComplex B ℤ)) := by
  constructor
  · intro X Y f hf
    exact (quasiIso_iff_of_arrow_mk_iso _ f
      (Arrow.isoMk (λ_ X) (λ_ Y) (by
        change (λ_ X).hom ≫ f = (𝟙 _ ⊗ₘ f) ≫ (λ_ Y).hom
        simp only [id_tensorHom, leftUnitor_naturality]))).mpr hf
  · intro X Y f hf
    exact (quasiIso_iff_of_arrow_mk_iso _ f
      (Arrow.isoMk (ρ_ X) (ρ_ Y) (by
        change (ρ_ X).hom ≫ f = (f ⊗ₘ 𝟙 _) ≫ (ρ_ Y).hom
        simp only [tensorHom_id, rightUnitor_naturality]))).mpr hf

/-- Reassociation proves closure of K-flat total complexes under tensor products. -/
private theorem totalKFlat_tensor (P Q : CochainComplex B ℤ)
    (hP : P.IsKFlatForTotalTensor) (hQ : Q.IsKFlatForTotalTensor) :
    CochainComplex.IsKFlatForTotalTensor (P ⊗ Q) := by
  constructor
  · intro X Y f hf
    apply (quasiIso_iff_of_arrow_mk_iso
      (𝟙 (P ⊗ Q) ⊗ₘ f) (𝟙 P ⊗ₘ (𝟙 Q ⊗ₘ f))
      (Arrow.isoMk (α_ P Q X) (α_ P Q Y) (by simp))).mpr
    exact hP.1 _ (hQ.1 f hf)
  · intro X Y f hf
    apply (quasiIso_iff_of_arrow_mk_iso
      (f ⊗ₘ 𝟙 (P ⊗ Q)) ((f ⊗ₘ 𝟙 P) ⊗ₘ 𝟙 Q)
      (Arrow.isoMk (α_ X P Q).symm (α_ Y P Q).symm (by simp))).mpr
    exact hQ.2 _ (hP.2 f hf)

end CountableTotal

attribute [local instance 12000] countableCochainMonoidal
  gradedTensor gradedGood12 gradedGood23 gradedFour tensorLeftEmpty tensorRightEmpty

section Models

variable {B : Type a} [Category.{b} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive B] [SymmetricCategory B] [HasCountableCoproducts B]
  [leftCountable : ∀ (I : Type) [Countable I] (X : B),
    PreservesColimitsOfShape (Discrete I) (tensorLeft X)]
  [rightCountable : ∀ (I : Type) [Countable I] (X : B),
    PreservesColimitsOfShape (Discrete I) (tensorRight X)]
  [HasDerivedCategory.{wA} B]
  [derivedMonoidal : MonoidalCategory (DerivedCategory B)]
  [derivedSymmetric : SymmetricCategory (DerivedCategory B)]

omit rightCountable in
/-- Cache the native monoidal structure on the homotopy category.
Source: the native homotopy tensor
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev countableHomotopyMonoidal : MonoidalCategory (HomotopyCategory B (.up ℤ)) :=
  inferInstance

attribute [local instance 12000] countableHomotopyMonoidal

omit rightCountable in
/-- Cache the native Koszul braiding on the homotopy category.
Source: the native homotopy braiding
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev countableHomotopyBraided : BraidedCategory (HomotopyCategory B (.up ℤ)) :=
  inferInstance

attribute [local instance 12000] countableHomotopyBraided

/-- The specified ordinary K-flat derived tensor, including its model isomorphisms.
The tensor, associator and unitors of complexes are Mathlib's direct-sum total
construction; its braiding is the native Koszul braiding. Naturality on chain maps
also gives naturality on homotopy-category maps, since every such map has a chain
representative and localization kills chain homotopies.
Source: Stacks 06YU and 0FPT
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
structure TensorModel (kf : CochainComplex B ℤ → Prop) where
  /-- The ordinary unit complex is K-flat. -/
  kflat_unit : kf (𝟙_ (CochainComplex B ℤ))
  /-- Reassociation makes tensor products of K-flat complexes K-flat. -/
  kflat_tensor : ∀ P Q : CochainComplex B ℤ, kf P → kf Q → kf (P ⊗ Q)
  /-- The fixed K-flat representative isomorphisms. -/
  pair (P Q : CochainComplex B ℤ) (_hP : kf P) (_hQ : kf Q) :
    DerivedCategory.Q.obj (P ⊗ Q) ≅ DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q
  /-- Naturality, including naturality at quasi-isomorphisms and hence their inverses. -/
  naturality : ∀ (P Q P' Q' : CochainComplex B ℤ)
    (hP : kf P) (hQ : kf Q) (hP' : kf P') (hQ' : kf Q') (f : P ⟶ P') (g : Q ⟶ Q'),
    DerivedCategory.Q.map (f ⊗ₘ g) ≫ (pair P' Q' hP' hQ').hom =
      (pair P Q hP hQ).hom ≫ (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g)
  /-- The localized ordinary tensor unit. -/
  unit : DerivedCategory.Q.obj (𝟙_ (CochainComplex B ℤ)) ≅ 𝟙_ (DerivedCategory B)
  /-- Compatibility with the native associator. -/
  associativity : ∀ (P Q T : CochainComplex B ℤ) (hP : kf P) (hQ : kf Q) (hT : kf T),
    DerivedCategory.Q.map (α_ P Q T).hom ≫
        (pair P (Q ⊗ T) hP (kflat_tensor Q T hQ hT)).hom ≫
        (𝟙 _ ⊗ₘ (pair Q T hQ hT).hom) =
      (pair (P ⊗ Q) T (kflat_tensor P Q hP hQ) hT).hom ≫
        ((pair P Q hP hQ).hom ⊗ₘ 𝟙 _) ≫
        (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj T)).hom
  /-- Compatibility with the native left unitor. -/
  left_unitality : ∀ (P : CochainComplex B ℤ) (hP : kf P),
    DerivedCategory.Q.map (λ_ P).hom =
      (pair (𝟙_ _) P kflat_unit hP).hom ≫ (unit.hom ⊗ₘ 𝟙 _) ≫
        (λ_ (DerivedCategory.Q.obj P)).hom
  /-- Compatibility with the native right unitor. -/
  right_unitality : ∀ (P : CochainComplex B ℤ) (hP : kf P),
    DerivedCategory.Q.map (ρ_ P).hom =
      (pair P (𝟙_ _) hP kflat_unit).hom ≫ (𝟙 _ ⊗ₘ unit.hom) ≫
        (ρ_ (DerivedCategory.Q.obj P)).hom
  /-- Compatibility with the native signed symmetry. -/
  symmetry : ∀ (P Q : CochainComplex B ℤ) (hP : kf P) (hQ : kf Q),
    DerivedCategory.Q.map (β_ P Q).hom ≫ (pair Q P hQ hP).hom =
      (pair P Q hP hQ).hom ≫ (β_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom


omit rightCountable in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The representative maps already contain a strong monoidal structure on the
full subcategory of good cochain complexes. This uses no resolutions. -/
private def TensorModel.coreOnComplexes (kf : CochainComplex B ℤ → Prop)
    (m : TensorModel (leftCountable := leftCountable) kf) :
    letI : ObjectProperty.IsMonoidal kf :=
      { prop_unit := (TensorModel.kflat_unit (leftCountable := leftCountable) m)
        prop_tensor := (TensorModel.kflat_tensor (leftCountable := leftCountable) m) }
    (ObjectProperty.ι kf ⋙ (DerivedCategory.Q (C := B))).CoreMonoidal := by
  letI : ObjectProperty.IsMonoidal kf :=
    { prop_unit := (TensorModel.kflat_unit (leftCountable := leftCountable) m)
      prop_tensor := (TensorModel.kflat_tensor (leftCountable := leftCountable) m) }
  refine Functor.CoreMonoidal.mk' (TensorModel.unit (leftCountable := leftCountable) m).symm
    (fun P Q ↦ ((TensorModel.pair (leftCountable := leftCountable) m)
      P.obj Q.obj P.property Q.property).symm) ?_ ?_ ?_ ?_ ?_
  · intro P P' f Q
    change
      (TensorModel.pair (leftCountable := leftCountable) m
        P.obj Q.obj P.property Q.property).hom ≫
          DerivedCategory.Q.map f.hom ▷ DerivedCategory.Q.obj Q.obj =
        DerivedCategory.Q.map (f.hom ▷ Q.obj) ≫
          (TensorModel.pair (leftCountable := leftCountable) m
            P'.obj Q.obj P'.property Q.property).hom
    simpa only [Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      Iso.symm_inv, Functor.map_id, tensorHom_id]
      using ((TensorModel.naturality (leftCountable := leftCountable) m) P.obj Q.obj P'.obj Q.obj
        P.property Q.property P'.property Q.property f.hom (𝟙 Q.obj)).symm
  · intro Q Q' P f
    change
      (TensorModel.pair (leftCountable := leftCountable) m
        P.obj Q.obj P.property Q.property).hom ≫
          DerivedCategory.Q.obj P.obj ◁ DerivedCategory.Q.map f.hom =
        DerivedCategory.Q.map (P.obj ◁ f.hom) ≫
          (TensorModel.pair (leftCountable := leftCountable) m
            P.obj Q'.obj P.property Q'.property).hom
    simpa only [Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      Iso.symm_inv, Functor.map_id, id_tensorHom]
      using ((TensorModel.naturality (leftCountable := leftCountable) m) P.obj Q.obj P.obj Q'.obj
        P.property Q.property P.property Q'.property (𝟙 P.obj) f.hom).symm
  · intro P Q T
    change
      (TensorModel.pair (leftCountable := leftCountable) m
        (P.obj ⊗ Q.obj) T.obj _ T.property).hom ≫
          (TensorModel.pair (leftCountable := leftCountable) m
            P.obj Q.obj P.property Q.property).hom ▷ DerivedCategory.Q.obj T.obj ≫
          (α_ (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj)
            (DerivedCategory.Q.obj T.obj)).hom =
        DerivedCategory.Q.map (α_ P.obj Q.obj T.obj).hom ≫
          (TensorModel.pair (leftCountable := leftCountable) m
            P.obj (Q.obj ⊗ T.obj) P.property _).hom ≫
          DerivedCategory.Q.obj P.obj ◁
            (TensorModel.pair (leftCountable := leftCountable) m
              Q.obj T.obj Q.property T.property).hom
    simpa only [Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      Iso.symm_inv, tensorHom_id, id_tensorHom]
      using ((TensorModel.associativity (leftCountable := leftCountable) m)
        P.obj Q.obj T.obj P.property Q.property T.property).symm
  · intro P
    change (λ_ (DerivedCategory.Q.obj P.obj)).inv =
      DerivedCategory.Q.map (λ_ P.obj).inv ≫
        (TensorModel.pair (leftCountable := leftCountable) m
          (𝟙_ _) P.obj (TensorModel.kflat_unit (leftCountable := leftCountable) m)
            P.property).hom ≫
        (TensorModel.unit (leftCountable := leftCountable) m).hom ▷
          DerivedCategory.Q.obj P.obj
    apply (cancel_mono (λ_ (DerivedCategory.Q.obj P.obj)).hom).1
    rw [Category.assoc, Category.assoc, ← tensorHom_id,
      ← TensorModel.left_unitality (leftCountable := leftCountable) m P.obj P.property]
    simp [← Functor.map_comp]
  · intro P
    change (ρ_ (DerivedCategory.Q.obj P.obj)).inv =
      DerivedCategory.Q.map (ρ_ P.obj).inv ≫
        (TensorModel.pair (leftCountable := leftCountable) m
          P.obj (𝟙_ _) P.property
            (TensorModel.kflat_unit (leftCountable := leftCountable) m)).hom ≫
        DerivedCategory.Q.obj P.obj ◁
          (TensorModel.unit (leftCountable := leftCountable) m).hom
    apply (cancel_mono (ρ_ (DerivedCategory.Q.obj P.obj)).hom).1
    rw [Category.assoc, Category.assoc, ← id_tensorHom,
      ← TensorModel.right_unitality (leftCountable := leftCountable) m P.obj P.property]
    simp [← Functor.map_comp]

omit rightCountable in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Descend the model's coherent localization comparisons to homotopy classes.
The quotient is full and has precisely the same objects as the complex category. -/
private def TensorModel.coreOnHomotopy (kf : CochainComplex B ℤ → Prop)
    (m : TensorModel (leftCountable := leftCountable) kf) :
    letI : ObjectProperty.IsMonoidal (fun P : HomotopyCategory B (.up ℤ) ↦ kf P.as) :=
      { prop_unit := TensorModel.kflat_unit (leftCountable := leftCountable) m
        prop_tensor := fun P Q ↦
          TensorModel.kflat_tensor (leftCountable := leftCountable) m P.as Q.as }
    ((ObjectProperty.ι (fun P : HomotopyCategory B (.up ℤ) ↦ kf P.as)) ⋙
      (DerivedCategory.Qh (C := B))).CoreMonoidal := by
  letI : ObjectProperty.IsMonoidal kf :=
    { prop_unit := TensorModel.kflat_unit (leftCountable := leftCountable) m
      prop_tensor := TensorModel.kflat_tensor (leftCountable := leftCountable) m }
  letI : ObjectProperty.IsMonoidal (fun P : HomotopyCategory B (.up ℤ) ↦ kf P.as) :=
    { prop_unit := TensorModel.kflat_unit (leftCountable := leftCountable) m
      prop_tensor := fun P Q ↦
        TensorModel.kflat_tensor (leftCountable := leftCountable) m P.as Q.as }
  letI := (TensorModel.coreOnComplexes (leftCountable := leftCountable) kf m).toMonoidal
  let q : ObjectProperty.FullSubcategory kf ⥤ DerivedCategory B :=
    ObjectProperty.ι kf ⋙ HomotopyCategory.quotient B (.up ℤ) ⋙ DerivedCategory.Qh
  let i : (ObjectProperty.ι kf ⋙ DerivedCategory.Q (C := B)) ≅ q :=
    Functor.isoWhiskerLeft (ObjectProperty.ι kf) (DerivedCategory.quotientCompQhIso B).symm
  letI : q.Monoidal := Functor.Monoidal.transport i
  let c := coreOfMonoidal q
  refine
    { εIso := c.εIso
      μIso := fun P Q ↦ c.μIso ⟨P.obj.as, P.property⟩ ⟨Q.obj.as, Q.property⟩
      μIso_hom_natural_left := ?_
      μIso_hom_natural_right := ?_
      associativity := ?_
      left_unitality := ?_
      right_unitality := ?_ }
  · intro P Q f T
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient B (.up ℤ)).map_surjective f.hom
    have he : f = ObjectProperty.homMk ((HomotopyCategory.quotient B (.up ℤ)).map g) :=
      ObjectProperty.hom_ext _ hg.symm
    rw [he]
    exact c.μIso_hom_natural_left
      (ObjectProperty.homMk (X := ⟨P.obj.as, P.property⟩)
        (Y := ⟨Q.obj.as, Q.property⟩) g) ⟨T.obj.as, T.property⟩
  · intro Q T P f
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient B (.up ℤ)).map_surjective f.hom
    have he : f = ObjectProperty.homMk ((HomotopyCategory.quotient B (.up ℤ)).map g) :=
      ObjectProperty.hom_ext _ hg.symm
    rw [he]
    exact c.μIso_hom_natural_right ⟨P.obj.as, P.property⟩
      (ObjectProperty.homMk (X := ⟨Q.obj.as, Q.property⟩)
        (Y := ⟨T.obj.as, T.property⟩) g)
  · intro P Q T
    have h := c.associativity ⟨P.obj.as, P.property⟩ ⟨Q.obj.as, Q.property⟩
      ⟨T.obj.as, T.property⟩
    change _ ≫ _ ≫ DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (.up ℤ)).map
        (α_ P.obj.as Q.obj.as T.obj.as).hom) = _ at h
    rw [HomotopyCategory.quotient_map_associator_hom] at h
    exact h
  · intro P
    have h := c.left_unitality ⟨P.obj.as, P.property⟩
    change (λ_ _).hom = _ ≫ _ ≫ DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (.up ℤ)).map (λ_ P.obj.as).hom) at h
    rw [← HomotopyCategory.MonoidalCategory.leftUnitor_hom_app] at h
    exact h
  · intro P
    have h := c.right_unitality ⟨P.obj.as, P.property⟩
    change (ρ_ _).hom = _ ≫ _ ≫ DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (.up ℤ)).map (ρ_ P.obj.as).hom) at h
    rw [← HomotopyCategory.MonoidalCategory.rightUnitor_hom_app] at h
    exact h

omit rightCountable in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A coherent braided localization on good complexes is precisely a tensor model. -/
private def TensorModel.ofMonoidal (kf : ObjectProperty (CochainComplex B ℤ))
    [kf.IsMonoidal]
    [(kf.ι ⋙ (DerivedCategory.Q (C := B))).Monoidal]
    (hbraid : ∀ P Q : kf.FullSubcategory,
      Functor.LaxMonoidal.μ (kf.ι ⋙ DerivedCategory.Q) P Q ≫
          (kf.ι ⋙ DerivedCategory.Q).map (β_ P Q).hom =
        (β_ ((kf.ι ⋙ DerivedCategory.Q).obj P)
          ((kf.ι ⋙ DerivedCategory.Q).obj Q)).hom ≫
            Functor.LaxMonoidal.μ (kf.ι ⋙ DerivedCategory.Q) Q P) :
    TensorModel (leftCountable := leftCountable) kf := by
  refine TensorModel.mk (leftCountable := leftCountable)
    kf.prop_unit (fun _ _ hP hQ ↦
      ObjectProperty.prop_tensor (P₁ := kf) (P₂ := kf) (Q := kf) hP hQ)
    (fun P Q hP hQ ↦
      (Functor.Monoidal.μIso (kf.ι ⋙ DerivedCategory.Q) ⟨P, hP⟩ ⟨Q, hQ⟩).symm)
    ?_ (Functor.Monoidal.εIso (kf.ι ⋙ DerivedCategory.Q)).symm ?_ ?_ ?_ ?_
  · intro P Q P' Q' hP hQ hP' hQ' f g
    have h :=
      (Functor.OplaxMonoidal.δ_natural (kf.ι ⋙ DerivedCategory.Q)
        (ObjectProperty.homMk (X := ⟨P, hP⟩) (Y := ⟨P', hP'⟩) f)
        (ObjectProperty.homMk (X := ⟨Q, hQ⟩) (Y := ⟨Q', hQ'⟩) g)).symm
    simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj,
      Functor.Monoidal.map_tensor kf.ι, ObjectProperty.ι_δ, ObjectProperty.ι_μ,
      Category.id_comp, Category.comp_id] at h
    simp only [Iso.symm_hom, Functor.Monoidal.μIso_inv]
    convert! h using 1
  · intro P Q T hP hQ hT
    have h :=
      (Functor.OplaxMonoidal.associativity (kf.ι ⋙ DerivedCategory.Q)
        ⟨P, hP⟩ ⟨Q, hQ⟩ ⟨T, hT⟩).symm
    simp only [Functor.comp_obj, Functor.comp_map,
      ObjectProperty.ι_obj,
      Functor.Monoidal.map_associator kf.ι,
      ObjectProperty.ι_δ, ObjectProperty.ι_μ,
      id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id] at h
    simp only [Iso.symm_hom, Functor.Monoidal.μIso_inv, tensorHom_id, id_tensorHom]
    convert! h using 1
  · intro P hP
    have hη : Functor.OplaxMonoidal.η kf.ι = 𝟙 _ := rfl
    have h :=
      (Functor.OplaxMonoidal.left_unitality_hom (kf.ι ⋙ DerivedCategory.Q) ⟨P, hP⟩).symm
    simp only [Functor.comp_obj, Functor.comp_map,
      ObjectProperty.ι_obj,
      Functor.Monoidal.map_leftUnitor kf.ι, ObjectProperty.ι_δ, hη,
      id_whiskerRight, Category.id_comp] at h
    simp only [Iso.symm_hom, Functor.Monoidal.μIso_inv, Functor.Monoidal.εIso_inv, tensorHom_id]
    convert! h using 1
  · intro P hP
    have hη : Functor.OplaxMonoidal.η kf.ι = 𝟙 _ := rfl
    have h :=
      (Functor.OplaxMonoidal.right_unitality_hom (kf.ι ⋙ DerivedCategory.Q) ⟨P, hP⟩).symm
    simp only [Functor.comp_obj, Functor.comp_map,
      ObjectProperty.ι_obj,
      Functor.Monoidal.map_rightUnitor kf.ι, ObjectProperty.ι_δ, hη,
      whiskerLeft_id, Category.id_comp] at h
    simp only [Iso.symm_hom, Functor.Monoidal.μIso_inv, Functor.Monoidal.εIso_inv, id_tensorHom]
    convert! h using 1
  · intro P Q hP hQ
    let : (kf.ι ⋙ (DerivedCategory.Q (C := B))).LaxBraided := ⟨hbraid⟩
    let : (kf.ι ⋙ (DerivedCategory.Q (C := B))).Braided := {}
    have h := Functor.map_braiding (kf.ι ⋙ DerivedCategory.Q) ⟨P, hP⟩ ⟨Q, hQ⟩
    simp only [Functor.comp_obj, Functor.comp_map,
      Functor.map_braiding kf.ι, ObjectProperty.ι_obj,
      ObjectProperty.ι_δ, ObjectProperty.ι_μ,
      Category.id_comp, Category.comp_id] at h
    change DerivedCategory.Q.map (β_ P Q).hom ≫ _ = _
    rw [h]
    simp only [Iso.symm_hom, Functor.Monoidal.μIso_inv, Category.assoc,
      Functor.Monoidal.μ_δ]
    congr 1
    exact Category.comp_id _

omit [MonoidalPreadditive B] [SymmetricCategory B] [HasCountableCoproducts B]
  [MonoidalCategory B] leftCountable rightCountable derivedMonoidal derivedSymmetric in
/-- The homotopy localization restricts to any class admitting K-flat replacements.
Refining the vertices of fractions proves the full localization property. -/
private theorem model_localization (kf : CochainComplex B ℤ → Prop)
    (res : ∀ P : CochainComplex B ℤ, ∃ (K : CochainComplex B ℤ) (f : K ⟶ P),
      kf K ∧ QuasiIso f) :
    ((ObjectProperty.ι (fun P : HomotopyCategory B (.up ℤ) ↦ kf P.as)) ⋙
      (DerivedCategory.Qh (C := B))).IsLocalization
      ((HomotopyCategory.quasiIso B (.up ℤ)).inverseImage
        (ObjectProperty.ι (fun P : HomotopyCategory B (.up ℤ) ↦ kf P.as))) := by
  apply SheafOfModules.restriction_localization
  intro P
  obtain ⟨K, f, hK, hf⟩ := res P.as
  refine ⟨⟨(HomotopyCategory.quotient B (.up ℤ)).obj K, hK⟩,
    (HomotopyCategory.quotient B (.up ℤ)).map f, ?_⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr hf

omit rightCountable in
/-- The identity comparison between two tensor models is obtained by the monoidal
universal property of the same K-flat homotopy localization. -/
private def modelIdentity (kf : ObjectProperty (CochainComplex B ℤ))
    (m : TensorModel (leftCountable := leftCountable) kf)
    (res : ∀ P : CochainComplex B ℤ, ∃ (K : CochainComplex B ℤ) (f : K ⟶ P),
      kf K ∧ QuasiIso f)
    (d' : MonoidalCategory (DerivedCategory B))
    (s' : @SymmetricCategory (DerivedCategory B) _ d')
    (m' : letI := d'; letI := s';
      TensorModel (leftCountable := leftCountable) kf) :
    @Functor.CoreMonoidal (DerivedCategory B) _ derivedMonoidal
      (DerivedCategory B) _ d' (𝟭 (DerivedCategory B)) := by
  let kH : ObjectProperty (HomotopyCategory B (.up ℤ)) := fun P ↦ kf P.as
  letI : kH.IsMonoidal :=
    { prop_unit := TensorModel.kflat_unit (leftCountable := leftCountable)
        (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric) m
      prop_tensor := fun P Q ↦
        TensorModel.kflat_tensor (leftCountable := leftCountable)
          (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric)
          m P.as Q.as }
  let L := kH.ι ⋙ (DerivedCategory.Qh (C := B))
  let W := (HomotopyCategory.quasiIso B (.up ℤ)).inverseImage kH.ι
  let loc : L.IsLocalization W := model_localization kf res
  let c := TensorModel.coreOnHomotopy (leftCountable := leftCountable)
    (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric) kf m
  let cm := @Functor.CoreMonoidal.toMonoidal _ _ _ _ _ derivedMonoidal _ c
  let c' := TensorModel.coreOnHomotopy (leftCountable := leftCountable)
    (derivedMonoidal := d') (derivedSymmetric := s') kf m'
  let lift : Localization.Lifting L W L (𝟭 (DerivedCategory B)) :=
    ⟨L.rightUnitor⟩
  exact @Localization.Monoidal.functorCoreMonoidalOfComp
    kH.FullSubcategory (DerivedCategory B) (DerivedCategory B) _ _ _
    _ derivedMonoidal d' L W loc cm (𝟭 (DerivedCategory B)) L
    c'.toMonoidal inferInstance lift

omit rightCountable in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The localized identity has precisely the representative comparison maps. -/
private theorem modelIdentity_maps (kf : ObjectProperty (CochainComplex B ℤ))
    (m : TensorModel (leftCountable := leftCountable) kf)
    (res : ∀ P : CochainComplex B ℤ, ∃ (K : CochainComplex B ℤ) (f : K ⟶ P),
      kf K ∧ QuasiIso f)
    (d' : MonoidalCategory (DerivedCategory B))
    (s' : @SymmetricCategory (DerivedCategory B) _ d')
    (m' : letI := d'; letI := s';
      TensorModel (leftCountable := leftCountable) kf) :
    let oldUnit := TensorModel.unit (leftCountable := leftCountable)
      (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric) m
    let oldPair := TensorModel.pair (leftCountable := leftCountable)
      (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric) m
    let j := modelIdentity (leftCountable := leftCountable)
      (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric)
      kf m res d' s' m'
    @Functor.CoreMonoidal.εIso (DerivedCategory B) _ derivedMonoidal
      (DerivedCategory B) _ d' (𝟭 _) j =
        (TensorModel.unit (leftCountable := leftCountable) m').symm ≪≫ oldUnit ∧
    ∀ P Q (hP : kf P) (hQ : kf Q),
      @Functor.CoreMonoidal.μIso (DerivedCategory B) _ derivedMonoidal
        (DerivedCategory B) _ d' (𝟭 _) j
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) =
        (TensorModel.pair (leftCountable := leftCountable) m' P Q hP hQ).symm ≪≫
          oldPair P Q hP hQ := by
  dsimp only
  constructor
  · apply Iso.ext
    simp [modelIdentity, Functor.CoreMonoidal.toMonoidal,
      Functor.CoreMonoidal.toLaxMonoidal_ε,
      Functor.CoreMonoidal.toOplaxMonoidal_η,
      TensorModel.coreOnHomotopy, coreOfMonoidal,
      TensorModel.coreOnComplexes, Category.assoc]
  · intro P Q hP hQ
    apply Iso.ext
    let kH : ObjectProperty (HomotopyCategory B (.up ℤ)) := fun P ↦ kf P.as
    let : kH.IsMonoidal :=
      { prop_unit := TensorModel.kflat_unit (leftCountable := leftCountable)
          (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric) m
        prop_tensor := fun P Q ↦ TensorModel.kflat_tensor
          (leftCountable := leftCountable) (derivedMonoidal := derivedMonoidal)
          (derivedSymmetric := derivedSymmetric) m P.as Q.as }
    let L := kH.ι ⋙ (DerivedCategory.Qh (C := B))
    let W := (HomotopyCategory.quasiIso B (.up ℤ)).inverseImage kH.ι
    let loc : L.IsLocalization W := model_localization kf res
    let c := TensorModel.coreOnHomotopy (leftCountable := leftCountable)
      (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric) kf m
    let cm := @Functor.CoreMonoidal.toMonoidal _ _ _ _ _ derivedMonoidal _ c
    let c' := TensorModel.coreOnHomotopy (leftCountable := leftCountable)
      (derivedMonoidal := d') (derivedSymmetric := s') kf m'
    let lift : Localization.Lifting L W L (𝟭 (DerivedCategory B)) := ⟨L.rightUnitor⟩
    let κ := DerivedCategory.quotientCompQhIso B
    have h := @Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app'
      kH.FullSubcategory (DerivedCategory B) (DerivedCategory B) _ _ _
      _ derivedMonoidal d' L W loc cm (𝟭 (DerivedCategory B)) L
      c'.toMonoidal inferInstance lift
      ⟨(HomotopyCategory.quotient B (.up ℤ)).obj P, hP⟩
      ⟨(HomotopyCategory.quotient B (.up ℤ)).obj Q, hQ⟩
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
      (κ.app P).symm (κ.app Q).symm
    refine h.trans ?_
    symm
    simp only [Functor.CoreMonoidal.toLaxMonoidal_μ,
      Functor.CoreMonoidal.toOplaxMonoidal_δ,
      c, c', TensorModel.coreOnHomotopy, coreOfMonoidal,
      Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Localization.Lifting.iso, Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.id_map, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
      Iso.trans_hom,
      Category.id_comp,

      κ, lift, HomotopyCategory.quotient_obj_as, Category.assoc,
      ← tensorHom_comp_tensorHom]
    simp only [Functor.Monoidal.coreMonoidalTransport, Functor.Monoidal.μIso_hom,
      Functor.Monoidal.μIso_inv,
      Functor.CoreMonoidal.toLaxMonoidal_μ, Functor.CoreMonoidal.toOplaxMonoidal_δ,
      TensorModel.coreOnComplexes, Functor.CoreMonoidal.mk',
      Iso.trans_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv,
      Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app_assoc]
    dsimp only [Functor.whiskerLeft_app, Functor.comp_obj, ObjectProperty.ι_obj]
    change (TensorModel.pair (leftCountable := leftCountable) m' P Q hP hQ).inv ≫
      (TensorModel.pair (leftCountable := leftCountable)
        (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric)
        m P Q hP hQ).hom =
      (@MonoidalCategory.tensorHom _ _ d'.toMonoidalCategoryStruct _ _ _ _
        ((DerivedCategory.quotientCompQhIso B).inv.app P)
        ((DerivedCategory.quotientCompQhIso B).inv.app Q)) ≫
      (@MonoidalCategory.tensorHom _ _ d'.toMonoidalCategoryStruct _ _ _ _ (𝟙 _) (𝟙 _)) ≫
      (@MonoidalCategory.tensorHom _ _ d'.toMonoidalCategoryStruct _ _ _ _
        ((DerivedCategory.quotientCompQhIso B).hom.app P)
        ((DerivedCategory.quotientCompQhIso B).hom.app Q)) ≫
      (TensorModel.pair (leftCountable := leftCountable) m' P Q hP hQ).inv ≫
      (TensorModel.pair (leftCountable := leftCountable)
        (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric)
        m P Q hP hQ).hom ≫
      (@MonoidalCategory.tensorHom _ _ derivedMonoidal.toMonoidalCategoryStruct _ _ _ _
        ((DerivedCategory.quotientCompQhIso B).inv.app P)
        ((DerivedCategory.quotientCompQhIso B).inv.app Q)) ≫
      (@MonoidalCategory.tensorHom _ _ derivedMonoidal.toMonoidalCategoryStruct _ _ _ _
        ((DerivedCategory.quotientCompQhIso B).hom.app P)
        ((DerivedCategory.quotientCompQhIso B).hom.app Q))
    have hn :
        (@MonoidalCategory.tensorHom _ _ d'.toMonoidalCategoryStruct _ _ _ _
          ((DerivedCategory.quotientCompQhIso B).inv.app P)
          ((DerivedCategory.quotientCompQhIso B).inv.app Q)) ≫
        (@MonoidalCategory.tensorHom _ _ d'.toMonoidalCategoryStruct _ _ _ _
          ((DerivedCategory.quotientCompQhIso B).hom.app P)
          ((DerivedCategory.quotientCompQhIso B).hom.app Q)) = 𝟙 _ :=
      ((DerivedCategory.quotientCompQhIso B).app P ⊗ᵢ
        (DerivedCategory.quotientCompQhIso B).app Q).inv_hom_id
    have ho :
        (@MonoidalCategory.tensorHom _ _ derivedMonoidal.toMonoidalCategoryStruct _ _ _ _
          ((DerivedCategory.quotientCompQhIso B).inv.app P)
          ((DerivedCategory.quotientCompQhIso B).inv.app Q)) ≫
        (@MonoidalCategory.tensorHom _ _ derivedMonoidal.toMonoidalCategoryStruct _ _ _ _
          ((DerivedCategory.quotientCompQhIso B).hom.app P)
          ((DerivedCategory.quotientCompQhIso B).hom.app Q)) = 𝟙 _ := by
      let := derivedMonoidal
      exact ((DerivedCategory.quotientCompQhIso B).app P ⊗ᵢ
        (DerivedCategory.quotientCompQhIso B).app Q).inv_hom_id
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp]
    rw [reassoc_of% hn, ho, Category.comp_id]

attribute [irreducible] modelIdentity

omit [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
  [HasCountableCoproducts B] leftCountable rightCountable derivedMonoidal derivedSymmetric in
/-- Every derived object has a representative in a class with quasi-isomorphic replacements. -/
private theorem model_essSurj (kf : ObjectProperty (CochainComplex B ℤ))
    (res : ∀ P : CochainComplex B ℤ, ∃ (K : CochainComplex B ℤ) (f : K ⟶ P),
      kf K ∧ QuasiIso f) :
    (kf.ι ⋙ (DerivedCategory.Q (C := B))).EssSurj := by
  constructor
  intro X
  obtain ⟨K, f, hK, hf⟩ := res ((DerivedCategory.Q (C := B)).objPreimage X)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso B f).mpr hf
  exact ⟨⟨K, hK⟩, ⟨asIso (DerivedCategory.Q.map f) ≪≫
    (DerivedCategory.Q (C := B)).objObjPreimageIso X⟩⟩

omit rightCountable in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The identity comparison preserves the native symmetry, as checked on good models. -/
private theorem modelIdentity_braided (kf : ObjectProperty (CochainComplex B ℤ))
    (m : TensorModel (leftCountable := leftCountable) kf)
    (res : ∀ P : CochainComplex B ℤ, ∃ (K : CochainComplex B ℤ) (f : K ⟶ P),
      kf K ∧ QuasiIso f)
    (d' : MonoidalCategory (DerivedCategory B))
    (s' : @SymmetricCategory (DerivedCategory B) _ d')
    (m' : letI := d'; letI := s';
      TensorModel (leftCountable := leftCountable) kf) :
    let oldBraiding := fun X Y : DerivedCategory B ↦
      (@BraidedCategory.braiding _ _ derivedMonoidal derivedSymmetric.toBraidedCategory X Y).hom
    let j := modelIdentity (leftCountable := leftCountable)
      (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric)
      kf m res d' s' m'
    let jPair := @Functor.CoreMonoidal.μIso (DerivedCategory B) _ derivedMonoidal
      (DerivedCategory B) _ d' (𝟭 _) j
    ∀ X Y, oldBraiding X Y ≫ (jPair Y X).inv =
      (jPair X Y).inv ≫ (β_ X Y).hom := by
  dsimp only
  let j := modelIdentity (leftCountable := leftCountable)
    (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric)
    kf m res d' s' m'
  let jm := @Functor.CoreMonoidal.toMonoidal (DerivedCategory B) _ derivedMonoidal
    (DerivedCategory B) _ d' (𝟭 _) j
  let L := kf.ι ⋙ (DerivedCategory.Q (C := B))
  let surj : L.EssSurj := model_essSurj kf res
  have hmaps := (modelIdentity_maps (leftCountable := leftCountable)
    (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric)
    kf m res d' s' m').2
  have hb := @braidedOfImages kf.FullSubcategory (DerivedCategory B) (DerivedCategory B)
    _ _ _ derivedMonoidal d' derivedSymmetric.toBraidedCategory s'.toBraidedCategory
    L surj (𝟭 _) jm (fun P Q ↦ by
      change (@Functor.CoreMonoidal.μIso (DerivedCategory B) _ derivedMonoidal
        (DerivedCategory B) _ d' (𝟭 _) (modelIdentity (leftCountable := leftCountable)
          (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric)
          kf m res d' s' m') (DerivedCategory.Q.obj P.obj)
            (DerivedCategory.Q.obj Q.obj)).hom ≫
          (@BraidedCategory.braiding _ _ derivedMonoidal
            derivedSymmetric.toBraidedCategory _ _).hom =
        (β_ (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj)).hom ≫
          (@Functor.CoreMonoidal.μIso (DerivedCategory B) _ derivedMonoidal
            (DerivedCategory B) _ d' (𝟭 _) (modelIdentity (leftCountable := leftCountable)
              (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric)
              kf m res d' s' m') (DerivedCategory.Q.obj Q.obj)
                (DerivedCategory.Q.obj P.obj)).hom
      rw [hmaps P.obj Q.obj P.property Q.property,
        hmaps Q.obj P.obj Q.property P.property]
      simp only [Iso.trans_hom, Iso.symm_hom]
      rw [Category.assoc, ← TensorModel.symmetry (leftCountable := leftCountable)
        (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric)
        m P.obj Q.obj P.property Q.property]
      apply (cancel_mono
        (TensorModel.pair (leftCountable := leftCountable)
          (derivedMonoidal := derivedMonoidal) (derivedSymmetric := derivedSymmetric)
          m Q.obj P.obj Q.property P.property).inv).1
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      apply (cancel_mono
        (TensorModel.pair (leftCountable := leftCountable) m'
          Q.obj P.obj Q.property P.property).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [TensorModel.symmetry (leftCountable := leftCountable) m']
      simp only [Iso.inv_hom_id_assoc])
  intro X Y
  let p := @Functor.CoreMonoidal.μIso (DerivedCategory B) _ derivedMonoidal
    (DerivedCategory B) _ d' (𝟭 _) j
  change _ ≫ (p Y X).inv = (p X Y).inv ≫ _
  have h := hb X Y
  change (p X Y).hom ≫
      (@BraidedCategory.braiding _ _ derivedMonoidal
        derivedSymmetric.toBraidedCategory X Y).hom =
    (β_ X Y).hom ≫ (p Y X).hom at h
  apply (cancel_epi (p X Y).hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Models

attribute [local instance 12000] countableHomotopyMonoidal countableHomotopyBraided

section Ringed

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- Cache the existing forgetful functor's preservation of sheaves.
Source: Mathlib's limit-preserving sheaf composition
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev ringedForgetSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := inferInstance

attribute [local instance 12000] ringedForgetSheafCompose

/-- Cache the existing sheafification instance in the coefficient universe.
Source: coefficient-universe sheafification
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev ringedWeakSheafify : HasWeakSheafify J AddCommGrpCat.{r} := inferInstance

attribute [local instance 12000] ringedWeakSheafify

/-- The existing module-sheaf category at the independent coefficient universe.
Source: Stacks 03EK (blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev Modules := ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The existing module-sheaf structure, cached to avoid repeated sheafification searches.
Source: the native module-sheaf instances
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev ringedModuleAbelian : Abelian (Modules R) := inferInstance

attribute [local instance 12000] ringedModuleAbelian

/-- The existing module-sheaf structure, cached to avoid repeated sheafification searches.
Source: the native module-sheaf instances
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev ringedModuleMonoidal : MonoidalCategory (Modules R) := inferInstance

attribute [local instance 12000] ringedModuleMonoidal

/-- The existing module-sheaf structure, cached to avoid repeated sheafification searches.
Source: the native module-sheaf instances
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev ringedModuleMonoidalPreadditive : MonoidalPreadditive (Modules R) := inferInstance

attribute [local instance 12000] ringedModuleMonoidalPreadditive

/-- The existing module-sheaf structure, cached to avoid repeated sheafification searches.
Source: the native module-sheaf instances
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev ringedModuleSymmetric : SymmetricCategory (Modules R) := inferInstance

attribute [local instance 12000] ringedModuleSymmetric

/-- The existing module-sheaf structure, cached to avoid repeated sheafification searches.
Source: the native module-sheaf instances
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev ringedModuleCoproducts : HasCountableCoproducts (Modules R) := inferInstance

attribute [local instance 12000] ringedModuleCoproducts

/-- Countable left-tensor preservation for the fixed module-sheaf category.
Source: Stacks 03EK (blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev ringedLeftCountable : ∀ (I : Type) [Countable I] (X : Modules R),
    PreservesColimitsOfShape (Discrete I) (tensorLeft X) := fun _ _ _ ↦ inferInstance

/-- Countable right-tensor preservation for the fixed module-sheaf category.
Source: Stacks 03EK (blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev ringedRightCountable : ∀ (I : Type) [Countable I] (X : Modules R),
    PreservesColimitsOfShape (Discrete I) (tensorRight X) := fun _ _ _ ↦ inferInstance

/-- The native total tensor on the fixed ringed module category, with the
countable preservation arguments supplied explicitly for stable elaboration.
Source: Stacks 06YL (blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
instance ringedCochainMonoidal : MonoidalCategory (CochainComplex (Modules R) ℤ) :=
  countableCochainMonoidal
    (leftCountable := ringedLeftCountable R)
    (rightCountable := ringedRightCountable R)

/-- The specified flat-term K-flat homotopy subcategory on the ringed site.
Source: Stacks 06YS, 0G7D
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
def resolvingRinged : ObjectProperty (HomotopyCategory (Modules R) (.up ℤ)) :=
  fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P.as ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.as.X n)

/-- Flat-term K-flat representatives localize to the source derived category. -/
private theorem source_localization [HasDerivedCategory.{wR} (Modules R)] :
    ((resolvingRinged R).ι ⋙ (DerivedCategory.Qh (C := Modules R))).IsLocalization
      ((HomotopyCategory.quasiIso (Modules R) (.up ℤ)).inverseImage
        (resolvingRinged R).ι) := by
  apply SheafOfModules.restriction_localization
  intro X
  obtain ⟨K, f, hK, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
  have hs : ∀ n, SheafOfModules.IsFlatOnSite (J := J) (R := R) (K.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (K.X n)).symm (hflat n)
  refine ⟨⟨(HomotopyCategory.quotient (Modules R) (.up ℤ)).obj K, hK, hs⟩,
    (HomotopyCategory.quotient (Modules R) (.up ℤ)).map f, ?_⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr hf

end Ringed

attribute [local instance 12001] ringedCochainMonoidal

attribute [local instance 12000] ringedForgetSheafCompose ringedWeakSheafify
  ringedModuleAbelian ringedModuleMonoidal
  ringedModuleMonoidalPreadditive ringedModuleSymmetric ringedModuleCoproducts


section Target

variable (A : Type a) [Category.{b} A] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A] [HasCountableCoproducts A]

/-- The target resolving class uses tensor exactness and the recorded two-sided K-flat test.
Source: Stacks 06YS, 0G7D and the exact-equivalence transfer argument
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
def resolvingTarget : ObjectProperty (HomotopyCategory A (.up ℤ)) :=
  fun P ↦ CochainComplex.IsKFlatForTotalTensor P.as ∧
    ∀ n : ℤ, exactFunctor A A (tensorRight (P.as.X n))

end Target

section Comparison

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{r}}
  {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A] [SymmetricCategory A] [HasCountableCoproducts A]
  [leftCountable : ∀ (I : Type) [Countable I] (X : A),
    PreservesColimitsOfShape (Discrete I) (tensorLeft X)]
  [rightCountable : ∀ (I : Type) [Countable I] (X : A),
    PreservesColimitsOfShape (Discrete I) (tensorRight X)]
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wA} A]
  (e : Modules R ≌ A) [e.functor.Additive] [e.inverse.Additive]

/-- The actual derived equivalence: its unit and counit are the localizations of the
termwise unit and counit, with the standard exact-functor comparison isomorphisms.
This is the existing equivalence construction, not a new choice of functors.
Source: Stacks 015F and the transfer argument, step 1
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
def derivedEquivalence : DerivedCategory (Modules R) ≌ DerivedCategory A :=
  e.mapDerivedCategory

/-- The two specified total comparisons are inverse through the termwise unit and counit.
Source: the transfer argument, hypotheses and step 1
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
def InverseTotalComparisons
    (tc : (e.functor.mapHomologicalComplex (.up ℤ)).CoreMonoidal)
    (gc : (e.inverse.mapHomologicalComplex (.up ℤ)).CoreMonoidal) : Prop :=
  (∀ P Q : CochainComplex (Modules R) ℤ,
    (e.mapHomologicalComplex (.up ℤ)).unitIso.hom.app (P ⊗ Q) ≫
      (e.inverse.mapHomologicalComplex (.up ℤ)).map (tc.μIso P Q).inv ≫
      (gc.μIso ((e.functor.mapHomologicalComplex (.up ℤ)).obj P)
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q)).inv =
      MonoidalCategory.tensorHom (X₁ := P) (X₂ := Q)
        (Y₁ := (e.mapHomologicalComplex (.up ℤ)).inverse.obj
          ((e.mapHomologicalComplex (.up ℤ)).functor.obj P))
        (Y₂ := (e.mapHomologicalComplex (.up ℤ)).inverse.obj
          ((e.mapHomologicalComplex (.up ℤ)).functor.obj Q))
        ((e.mapHomologicalComplex (.up ℤ)).unitIso.hom.app P)
        ((e.mapHomologicalComplex (.up ℤ)).unitIso.hom.app Q)) ∧
  ((e.mapHomologicalComplex (.up ℤ)).unitIso.hom.app (𝟙_ (CochainComplex (Modules R) ℤ)) ≫
      (e.inverse.mapHomologicalComplex (.up ℤ)).map tc.εIso.inv ≫ gc.εIso.inv =
      𝟙 (𝟙_ (CochainComplex (Modules R) ℤ))) ∧
  (∀ P Q : CochainComplex A ℤ,
    (e.functor.mapHomologicalComplex (.up ℤ)).map (gc.μIso P Q).inv ≫
      (tc.μIso ((e.inverse.mapHomologicalComplex (.up ℤ)).obj P)
        ((e.inverse.mapHomologicalComplex (.up ℤ)).obj Q)).inv ≫
      MonoidalCategory.tensorHom (Y₁ := P) (Y₂ := Q)
        (X₁ := (e.mapHomologicalComplex (.up ℤ)).functor.obj
          ((e.mapHomologicalComplex (.up ℤ)).inverse.obj P))
        (X₂ := (e.mapHomologicalComplex (.up ℤ)).functor.obj
          ((e.mapHomologicalComplex (.up ℤ)).inverse.obj Q))
        ((e.mapHomologicalComplex (.up ℤ)).counitIso.hom.app P)
        ((e.mapHomologicalComplex (.up ℤ)).counitIso.hom.app Q) =
      (e.mapHomologicalComplex (.up ℤ)).counitIso.hom.app (P ⊗ Q)) ∧
  (tc.εIso.hom ≫ (e.functor.mapHomologicalComplex (.up ℤ)).map gc.εIso.hom ≫
      (e.mapHomologicalComplex (.up ℤ)).counitIso.hom.app (𝟙_ (CochainComplex A ℤ)) =
      𝟙 (𝟙_ (CochainComplex A ℤ)))

variable [dR : MonoidalCategory (DerivedCategory (Modules R))]
  [sR : SymmetricCategory (DerivedCategory (Modules R))]
  [dA : MonoidalCategory (DerivedCategory A)] [sA : SymmetricCategory (DerivedCategory A)]
  (mR : TensorModel (B := Modules R) (leftCountable := ringedLeftCountable R)
    (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)))
  (mA : TensorModel (B := A) (leftCountable := leftCountable)
    (CochainComplex.IsKFlatForTotalTensor (C := A)))
  (tc : (e.functor.mapHomologicalComplex (.up ℤ)).CoreMonoidal)
  (hF : ∀ P : CochainComplex (Modules R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      CochainComplex.IsKFlatForTotalTensor
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj P))

/-- The natural isomorphism t of derived tensor bifunctors.
Source: the transfer argument, step 7
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
abbrev TensorComparison :=
  tensor (DerivedCategory (Modules R)) ⋙ e.functor.mapDerivedCategory ≅
    (e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory) ⋙
      tensor (DerivedCategory A)

/-- The natural comparison carried by a coherent strong monoidal structure.
Source: the transfer argument, step 9
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
def comparisonOfCore (s : e.functor.mapDerivedCategory.CoreMonoidal) : TensorComparison e :=
  letI := s.toMonoidal
  (Functor.Monoidal.μNatIso e.functor.mapDerivedCategory).symm

/-- The prescribed representative equation, with composition written in Lean's order.
Here `tc.μIso.inv` is the specified signed-total comparison τ, and
`mapDerivedCategoryFactors` is exactly κ. No unspecified comparison arrow is used.
Source: the transfer argument, steps 7--8
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
def NormalizationEquation (t : TensorComparison e)
    (P Q : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q) : Prop :=
  e.functor.mapDerivedCategory.map ((TensorModel.pair (leftCountable := ringedLeftCountable R) mR)
      P Q hP hQ).hom ≫
      (t.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)).hom ≫
      (e.functor.mapDerivedCategoryFactors.hom.app P ⊗ₘ
        e.functor.mapDerivedCategoryFactors.hom.app Q) =
    e.functor.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
      (DerivedCategory.Q (C := A)).map (tc.μIso P Q).inv ≫
      ((TensorModel.pair (leftCountable := leftCountable) mA)
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj P)
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q) (hF P hP) (hF Q hQ)).hom

/-- The localized ordinary unit comparison. The total unit is required to be the
termwise ordinary unit in the theorem's hypotheses.
Source: the transfer argument, step 4 and step 9
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
def unitComparison :
    e.functor.mapDerivedCategory.obj (𝟙_ (DerivedCategory (Modules R))) ≅
      𝟙_ (DerivedCategory A) :=
  e.functor.mapDerivedCategory.mapIso
      (TensorModel.unit (leftCountable := ringedLeftCountable R) mR).symm ≪≫
    e.functor.mapDerivedCategoryFactors.app (𝟙_ (CochainComplex (Modules R) ℤ)) ≪≫
    (DerivedCategory.Q (C := A)).mapIso tc.εIso.symm ≪≫
      TensorModel.unit (leftCountable := leftCountable) mA

/-- Uniqueness on flat-term K-flat representatives, for the tensor comparison alone.
Source: the transfer argument, step 7
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
def ResolvingNormalization (t : TensorComparison e) : Prop :=
  ∀ (P Q : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X n)) →
    NormalizationEquation (leftCountable := leftCountable) e mR mA tc hF t P Q hP hQ

/-- The comparison is a natural isomorphism, with all three monoidal coherence
axioms and the native symmetry square. `CoreMonoidal` contains natural isomorphisms,
not merely objectwise isomorphism existence. Its inverse tensorator is t.
Source: the transfer argument, steps 7--9
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
def ComparisonSpec (s : e.functor.mapDerivedCategory.CoreMonoidal) : Prop :=
  s.εIso = (unitComparison (leftCountable := leftCountable) e mR mA tc).symm ∧
  (∀ (K L : DerivedCategory (Modules R)),
    e.functor.mapDerivedCategory.map (β_ K L).hom ≫ (s.μIso L K).inv =
      (s.μIso K L).inv ≫
        (β_ (e.functor.mapDerivedCategory.obj K) (e.functor.mapDerivedCategory.obj L)).hom) ∧
  (∀ (P Q : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
    NormalizationEquation (leftCountable := leftCountable) e mR mA tc hF
      (comparisonOfCore e s) P Q hP hQ) ∧
  (∀ t' : TensorComparison e,
    ResolvingNormalization (leftCountable := leftCountable) e mR mA tc hF t' →
      t' = comparisonOfCore e s)

/-- Agreement with an independently specified ordinary K-flat derived tensor.
The identity comparison is strong monoidal, respects the native symmetries, and is
specified by the two model maps; every normalized comparison t' is t followed by it.
The local instance bindings in this definition distinguish two structures on the same
derived category; they do not choose resolutions or change that category.
Source: the transfer argument, step 10
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
def ModelAgreement (s : e.functor.mapDerivedCategory.CoreMonoidal)
    (dA' : MonoidalCategory (DerivedCategory A))
    (sA' : @SymmetricCategory (DerivedCategory A) _ dA') : Prop :=
  let oldBraiding := fun X Y : DerivedCategory A ↦
    (@BraidedCategory.braiding _ _ dA sA.toBraidedCategory X Y).hom
  let oldPair := TensorModel.pair (leftCountable := leftCountable)
    (derivedMonoidal := dA) (derivedSymmetric := sA) mA
  let oldUnit := TensorModel.unit (leftCountable := leftCountable)
    (derivedMonoidal := dA) (derivedSymmetric := sA) mA
  let oldComparison := @Functor.CoreMonoidal.μIso
    (DerivedCategory (Modules R)) _ dR (DerivedCategory A) _ dA
    e.functor.mapDerivedCategory s
  letI := dA'
  letI := sA'
  ∀ mA' : TensorModel (B := A) (leftCountable := leftCountable)
    (CochainComplex.IsKFlatForTotalTensor (C := A)),
    ∃ j : @Functor.CoreMonoidal (DerivedCategory A) _ dA
        (DerivedCategory A) _ dA' (𝟭 (DerivedCategory A)),
      let jPair := @Functor.CoreMonoidal.μIso (DerivedCategory A) _ dA
        (DerivedCategory A) _ dA' (𝟭 (DerivedCategory A)) j
      let jUnit := @Functor.CoreMonoidal.εIso (DerivedCategory A) _ dA
        (DerivedCategory A) _ dA' (𝟭 (DerivedCategory A)) j
      jUnit = (TensorModel.unit (leftCountable := leftCountable) mA').symm ≪≫ oldUnit ∧
      (∀ (P Q : CochainComplex A ℤ) (hP : P.IsKFlatForTotalTensor)
        (hQ : Q.IsKFlatForTotalTensor),
        (jPair (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).inv =
          (oldPair P Q hP hQ).inv ≫
            ((TensorModel.pair (leftCountable := leftCountable) mA') P Q hP hQ).hom) ∧
      (∀ X Y : DerivedCategory A,
        oldBraiding X Y ≫ (jPair Y X).inv = (jPair X Y).inv ≫ (β_ X Y).hom) ∧
      (∀ t' : TensorComparison e,
        ResolvingNormalization (leftCountable := leftCountable) e mR mA' tc hF t' →
          ∀ K L : DerivedCategory (Modules R),
            (t'.app (K, L)).hom = (oldComparison K L).inv ≫
              (jPair (e.functor.mapDerivedCategory.obj K)
                (e.functor.mapDerivedCategory.obj L)).inv)

omit rightCountable [e.inverse.Additive] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Normalization on flat-term representatives determines the whole tensor comparison. -/
private theorem comparison_ext
    [((resolvingRinged R).ι ⋙ (DerivedCategory.Qh (C := Modules R))).IsLocalization
      ((HomotopyCategory.quasiIso (Modules R) (.up ℤ)).inverseImage
        (resolvingRinged R).ι)]
    (t t' : TensorComparison e)
    (ht : ResolvingNormalization (leftCountable := leftCountable) e mR mA tc hF t)
    (ht' : ResolvingNormalization (leftCountable := leftCountable) e mR mA tc hF t') :
    t = t' := by
  have hrep (P Q : CochainComplex (Modules R) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
      (hPf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n))
      (hQf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X n)) :
      t.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        t'.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
    apply (cancel_epi (e.functor.mapDerivedCategory.map
      (TensorModel.pair (leftCountable := ringedLeftCountable R) mR P Q hP hQ).hom)).1
    apply (cancel_mono (e.functor.mapDerivedCategoryFactors.hom.app P ⊗ₘ
      e.functor.mapDerivedCategoryFactors.hom.app Q)).1
    simpa only [Category.assoc, Iso.app_hom] using
      (ht P Q hP hQ hPf hQf).trans (ht' P Q hP hQ hPf hQf).symm
  apply Iso.ext
  let L := (resolvingRinged R).ι ⋙ (DerivedCategory.Qh (C := Modules R))
  let W := (HomotopyCategory.quasiIso (Modules R) (.up ℤ)).inverseImage
    (resolvingRinged R).ι
  apply Localization.natTrans_ext (L.prod L) (W.prod W)
  rintro ⟨P, Q⟩
  let i := (DerivedCategory.quotientCompQhIso (Modules R)).app P.obj.as
  let j := (DerivedCategory.quotientCompQhIso (Modules R)).app Q.obj.as
  have h := hrep P.obj.as Q.obj.as P.property.1 Q.property.1
    P.property.2 Q.property.2
  let ij : (L.obj P, L.obj Q) ≅
      (DerivedCategory.Q.obj P.obj.as, DerivedCategory.Q.obj Q.obj.as) := i.prod j
  have hf : IsIso ij.hom := ij.isIso_hom
  apply (cancel_mono (((e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory) ⋙
    tensor (DerivedCategory A)).map ij.hom)).1
  rw [← t.hom.naturality, ← t'.hom.naturality, h]

omit rightCountable [e.inverse.Additive] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Any other K-flat tensor model is identified by the localized identity comparison. -/
private theorem comparison_agreement
    (s : e.functor.mapDerivedCategory.CoreMonoidal)
    (hnorm : ResolvingNormalization (leftCountable := leftCountable)
      e mR mA tc hF (comparisonOfCore e s))
    (res : ∀ P : CochainComplex A ℤ, ∃ (K : CochainComplex A ℤ) (f : K ⟶ P),
      K.IsKFlatForTotalTensor ∧ QuasiIso f)
    (dA' : MonoidalCategory (DerivedCategory A))
    (sA' : @SymmetricCategory (DerivedCategory A) _ dA') :
    ModelAgreement (leftCountable := leftCountable) (dA := dA) (sA := sA)
      e mR mA tc hF s dA' sA' := by
  dsimp only [ModelAgreement]
  intro mA'
  let kf : ObjectProperty (CochainComplex A ℤ) := CochainComplex.IsKFlatForTotalTensor
  let j := modelIdentity (leftCountable := leftCountable)
    (derivedMonoidal := dA) (derivedSymmetric := sA) kf mA res dA' sA' mA'
  let jp := @Functor.CoreMonoidal.μIso (DerivedCategory A) _ dA
    (DerivedCategory A) _ dA' (𝟭 _) j
  have hm := modelIdentity_maps (leftCountable := leftCountable)
    (derivedMonoidal := dA) (derivedSymmetric := sA) kf mA res dA' sA' mA'
  refine ⟨j, hm.1, ?_, ?_, ?_⟩
  · intro P Q hP hQ
    have h := congrArg Iso.inv (hm.2 P Q hP hQ)
    simpa only [Iso.trans_inv, Iso.symm_inv] using h
  · exact modelIdentity_braided (leftCountable := leftCountable)
      (derivedMonoidal := dA) (derivedSymmetric := sA) kf mA res dA' sA' mA'
  · let oldT := comparisonOfCore (dA := dA) e s
    let := dA'
    let := sA'
    let jm := @Functor.CoreMonoidal.toMonoidal (DerivedCategory A) _ dA
      (DerivedCategory A) _ dA' (𝟭 _) j
    let t : TensorComparison e := oldT ≪≫
      Functor.isoWhiskerLeft (e.functor.mapDerivedCategory.prod e.functor.mapDerivedCategory)
        (@Functor.Monoidal.μNatIso (DerivedCategory A) _ dA
          (DerivedCategory A) _ dA' (𝟭 _) jm).symm
    have ht : ResolvingNormalization (leftCountable := leftCountable)
        e mR mA' tc hF t := by
      intro P Q hP hQ hPf hQf
      have hj := congrArg Iso.inv (hm.2
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj P)
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q) (hF P hP) (hF Q hQ))
      simp only [Iso.trans_inv, Iso.symm_inv] at hj
      have hn := hnorm P Q hP hQ hPf hQf
      have hd := @Functor.OplaxMonoidal.δ_natural (DerivedCategory A) _ dA
        (DerivedCategory A) _ dA' (𝟭 _) jm.toOplaxMonoidal
        _ _ _ _ (e.functor.mapDerivedCategoryFactors.hom.app P)
        (e.functor.mapDerivedCategoryFactors.hom.app Q)
      dsimp only [Functor.id_map] at hd
      dsimp only [NormalizationEquation] at hn ⊢
      have he := congrArg (fun f ↦
        e.functor.mapDerivedCategory.map
          (TensorModel.pair (leftCountable := ringedLeftCountable R) mR P Q hP hQ).hom ≫
        oldT.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫ f) hd
      have he' := congrArg (fun f ↦ f ≫
        @Functor.OplaxMonoidal.δ (DerivedCategory A) _ dA
          (DerivedCategory A) _ dA' (𝟭 _) jm.toOplaxMonoidal
          (DerivedCategory.Q.obj ((e.functor.mapHomologicalComplex (.up ℤ)).obj P))
          (DerivedCategory.Q.obj ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q))) hn
      dsimp only [t, NatTrans.comp_app, Iso.app_hom, Iso.trans_hom, Iso.symm_hom,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
        Functor.Monoidal.μNatIso_inv_app, Functor.prod_obj]
      simp only [Category.assoc]
      change _ ≫ _ ≫ @Functor.OplaxMonoidal.δ
        (DerivedCategory A) _ dA (DerivedCategory A) _ dA' (𝟭 _) jm.toOplaxMonoidal
        (e.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
        (e.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)) ≫ _ = _
      refine he.trans ?_
      simp only [Category.assoc] at he'
      refine he'.trans ?_
      have hj' : @Functor.OplaxMonoidal.δ (DerivedCategory A) _ dA
          (DerivedCategory A) _ dA' (𝟭 _) jm.toOplaxMonoidal
          (DerivedCategory.Q.obj ((e.functor.mapHomologicalComplex (.up ℤ)).obj P))
          (DerivedCategory.Q.obj ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q)) =
          (TensorModel.pair (leftCountable := leftCountable)
            (derivedMonoidal := dA) (derivedSymmetric := sA) mA
            ((e.functor.mapHomologicalComplex (.up ℤ)).obj P)
            ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q)
            (hF P hP) (hF Q hQ)).inv ≫
          (TensorModel.pair (leftCountable := leftCountable) mA'
            ((e.functor.mapHomologicalComplex (.up ℤ)).obj P)
            ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q)
            (hF P hP) (hF Q hQ)).hom := hj
      rw [hj']
      simp only [Iso.hom_inv_id_assoc]
    intro t' ht' K L
    have := source_localization (R := R)
    have heq := comparison_ext (leftCountable := leftCountable)
      e mR mA' tc hF t' t ht' ht
    rw [heq]
    rfl

end Comparison

section Conclusion

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{r}}
  {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A] [SymmetricCategory A] [HasCountableCoproducts A]
  [leftCountable : ∀ (I : Type) [Countable I] (X : A),
    PreservesColimitsOfShape (Discrete I) (tensorLeft X)]
  [rightCountable : ∀ (I : Type) [Countable I] (X : A),
    PreservesColimitsOfShape (Discrete I) (tensorRight X)]
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wA} A]
  (e : Modules R ≌ A) [e.functor.Additive] [e.inverse.Additive]
  [MonoidalCategory (DerivedCategory (Modules R))]
  [SymmetricCategory (DerivedCategory (Modules R))]
  (mR : TensorModel (B := Modules R) (leftCountable := ringedLeftCountable R)
    (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)))
  (tc : (e.functor.mapHomologicalComplex (.up ℤ)).CoreMonoidal)
  (hF : ∀ P : CochainComplex (Modules R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      CochainComplex.IsKFlatForTotalTensor
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj P))

/-- The tensor constructed on the ordinary unbounded derived category, with the
normalized coherent comparison and its independence of another tensor presentation.
The bindings specify structures under the existential in the main theorem; no data
are selected from an unspecified existence proof.
Source: the transfer argument, steps 4--10
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent). -/
def TransferSpec (dA : MonoidalCategory (DerivedCategory A))
    (sA : @SymmetricCategory (DerivedCategory A) _ dA) : Prop :=
  letI := dA
  letI := sA
  ∃ mA : TensorModel (B := A) (leftCountable := leftCountable)
    (CochainComplex.IsKFlatForTotalTensor (C := A)),
    ∃ s : e.functor.mapDerivedCategory.CoreMonoidal,
      ComparisonSpec (leftCountable := leftCountable) e mR mA tc hF s ∧
      ∀ (dA' : MonoidalCategory (DerivedCategory A))
        (sA' : @SymmetricCategory (DerivedCategory A) _ dA'),
        ModelAgreement (leftCountable := leftCountable) (dA := dA) (sA := sA)
          e mR mA tc hF s dA' sA'

omit [SymmetricCategory A] leftCountable rightCountable
  [HasDerivedCategory (Modules R)] [HasDerivedCategory A]
  [MonoidalCategory (DerivedCategory (Modules R))]
  [SymmetricCategory (DerivedCategory (Modules R))] in
private theorem target_resolution
    (hF : ∀ P : CochainComplex (Modules R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
        CochainComplex.IsKFlatForTotalTensor
          ((e.functor.mapHomologicalComplex (.up ℤ)).obj P))
    (hFlatF : ∀ M : Modules R, SheafOfModules.IsFlatOnSite (J := J) (R := R) M ↔
      exactFunctor A A (tensorRight (e.functor.obj M)))
    (P : CochainComplex A ℤ) :
    ∃ (K : CochainComplex A ℤ) (f : K ⟶ P),
      K.IsKFlatForTotalTensor ∧
        (∀ n : ℤ, exactFunctor A A (tensorRight (K.X n))) ∧ QuasiIso f := by
  obtain ⟨K, f, hK, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      ((e.inverse.mapHomologicalComplex (.up ℤ)).obj P)
  have : QuasiIso f := hf
  refine ⟨(e.functor.mapHomologicalComplex (.up ℤ)).obj K,
    (e.functor.mapHomologicalComplex (.up ℤ)).map f ≫
      (e.mapHomologicalComplex (.up ℤ)).counitIso.hom.app P, hF K hK, ?_, ?_⟩
  · intro n
    exact (hFlatF (K.X n)).mp
      ((exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R (K.X n)).symm (hflat n))
  · have hm : QuasiIso ((e.functor.mapHomologicalComplex (.up ℤ)).map f) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology f e.functor
    have : IsIso ((e.mapHomologicalComplex (.up ℤ)).counitIso.hom.app P) :=
      ((e.mapHomologicalComplex (.up ℤ)).counitIso.app P).isIso_hom
    have hc : QuasiIso ((e.mapHomologicalComplex (.up ℤ)).counitIso.hom.app P) :=
      quasiIso_of_isIso _
    exact quasiIso_comp _ _ (hφ := hm) (hφ' := hc)

omit [SymmetricCategory A] leftCountable rightCountable
  [HasDerivedCategory (Modules R)] [MonoidalCategory (DerivedCategory (Modules R))]
  [SymmetricCategory (DerivedCategory (Modules R))] in
private theorem target_localization
    (hF : ∀ P : CochainComplex (Modules R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
        CochainComplex.IsKFlatForTotalTensor
          ((e.functor.mapHomologicalComplex (.up ℤ)).obj P))
    (hFlatF : ∀ M : Modules R, SheafOfModules.IsFlatOnSite (J := J) (R := R) M ↔
      exactFunctor A A (tensorRight (e.functor.obj M))) :
    ((resolvingTarget A).ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage (resolvingTarget A).ι) := by
  apply SheafOfModules.restriction_localization
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh (resolvingTarget A)
  intro X
  obtain ⟨K, f, hK, hflat, hf⟩ :=
    target_resolution e hF hFlatF X.as
  refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj K, hK, hflat⟩,
    (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr hf

/-- Transfer of resolving localization and ordinary K-flat derived tensor.

`e` specifies F, G and their ordinary unit and counit. Their derived equivalence is
`derivedEquivalence e`, the existing exact-functor localization construction; it uses
the termwise unit and counit, not an independently chosen derived equivalence.
`tc` and `gc` specify the coherent total comparisons and `hInverse` makes them inverse.
The ordinary and total symmetry squares, ordinary unit normalization, flatness and
K-flatness preservation and reflection are explicit below. The given `mR` is the
ringed-site derived tensor with its fixed canonical model comparisons, expressed
independently of a particular equivalent monoidal presentation of that tensor.

Source: Stacks Project, Tags 06YS, 0G7D, 06YT, 06YU, and the agent-written transfer
(blueprint: lem-sfb-ringed-equivalence-resolving-tensor-descent).

Proof:
1. Use the existing exact derived equivalence and its localization comparison κ.
   Transfer flat-term K-flat replacements from the source, and apply the fraction
   restriction theorem to obtain the target resolving localization.
2. Transport the supplied source symmetric monoidal derived category along this
   equivalence. The source model maps make localization on all K-flat complexes
   strong monoidal and braided. Restrict the given total comparison to the K-flat
   equivalence, then transport that localization functor through the equivalence
   and κ. Its inverse tensorator and inverse unit give the target `TensorModel`.
3. Invert the monoidality equations for κ to obtain the prescribed tensor and unit
   normalizations. This works on every K-flat pair directly. The transported derived
   equivalence is braided. Two-variable localization extensionality proves uniqueness
   on flat-term K-flat representatives after canceling the model maps and κ.
4. For an independently supplied target model, descend both coherent model functors
   to the K-flat homotopy subcategory. Apply monoidal localization to the identity
   functor. Its unit and tensorator compute to the new model inverse followed by
   the old model. The two model symmetry equations and essential surjectivity give
   its native symmetry square. Oplax naturality shows that the old comparison
   followed by this identity comparison is normalized for the new model; uniqueness
   identifies it with every independently normalized comparison.
-/
theorem ringed_equivalence_resolving_tensor_descent
    [e.functor.Braided] [e.inverse.Braided]
    [NatTrans.IsMonoidal e.unitIso.hom] [NatTrans.IsMonoidal e.counitIso.hom]
    (gc : (e.inverse.mapHomologicalComplex (.up ℤ)).CoreMonoidal)
    (hInverse : InverseTotalComparisons (leftCountable := leftCountable) e tc gc)
    (hUnitF : tc.εIso = e.functor.mapCochainComplexεIso)
    (hUnitG : gc.εIso = e.inverse.mapCochainComplexεIso)
    (hSymF : ∀ P Q : CochainComplex (Modules R) ℤ,
      (e.functor.mapHomologicalComplex (.up ℤ)).map (β_ P Q).hom ≫
          (tc.μIso Q P).inv =
        (tc.μIso P Q).inv ≫
          (β_ ((e.functor.mapHomologicalComplex (.up ℤ)).obj P)
            ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q)).hom)
    (hSymG : ∀ P Q : CochainComplex A ℤ,
      (e.inverse.mapHomologicalComplex (.up ℤ)).map (β_ P Q).hom ≫
          (gc.μIso Q P).inv =
        (gc.μIso P Q).inv ≫
          (β_ ((e.inverse.mapHomologicalComplex (.up ℤ)).obj P)
            ((e.inverse.mapHomologicalComplex (.up ℤ)).obj Q)).hom)
    (hFlatF : ∀ M : Modules R, SheafOfModules.IsFlatOnSite (J := J) (R := R) M ↔
      exactFunctor A A (tensorRight (e.functor.obj M)))
    (hFlatG : ∀ M : A, exactFunctor A A (tensorRight M) ↔
      SheafOfModules.IsFlatOnSite (J := J) (R := R) (e.inverse.obj M))
    (hKFlatF : ∀ P : CochainComplex (Modules R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ↔
        CochainComplex.IsKFlatForTotalTensor
          ((e.functor.mapHomologicalComplex (.up ℤ)).obj P))
    (hKFlatG : ∀ P : CochainComplex A ℤ, P.IsKFlatForTotalTensor ↔
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
        ((e.inverse.mapHomologicalComplex (.up ℤ)).obj P)) :
    (∃ L : ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage
        (resolvingTarget A).ι).Localization ⥤ DerivedCategory A,
      L.IsEquivalence ∧
        Nonempty (((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage
          (resolvingTarget A).ι).Q ⋙ L ≅ (resolvingTarget A).ι ⋙ DerivedCategory.Qh)) ∧
    ∃ (dA : MonoidalCategory (DerivedCategory A))
      (sA : @SymmetricCategory (DerivedCategory A) _ dA),
      TransferSpec (leftCountable := leftCountable) e mR tc
        (fun P hP ↦ (hKFlatF P).mp hP) dA sA := by
  have _ := hInverse
  have _ := hUnitF
  have _ := hUnitG
  have _ := hSymG
  have _ := hFlatG
  constructor
  · let L := (resolvingTarget A).ι ⋙ (DerivedCategory.Qh (C := A))
    let W := (HomotopyCategory.quasiIso A (.up ℤ)).inverseImage (resolvingTarget A).ι
    have : L.IsLocalization W := target_localization e (fun P hP ↦ (hKFlatF P).mp hP) hFlatF
    refine ⟨Localization.Construction.lift L (Localization.inverts L W),
      Functor.IsLocalization.isEquivalence, ?_⟩
    exact ⟨eqToIso (Localization.Construction.fac L (Localization.inverts L W))⟩
  · let : MonoidalCategory (CochainComplex (Modules R) ℤ) := ringedCochainMonoidal R
    let : MonoidalCategory (CochainComplex A ℤ) :=
      countableCochainMonoidal (leftCountable := leftCountable)
        (rightCountable := rightCountable)
    let ed := derivedEquivalence e
    let dA : MonoidalCategory (DerivedCategory A) := Monoidal.transport ed
    let := dA
    let sA : SymmetricCategory (DerivedCategory A) :=
      Monoidal.Transported.instSymmetricCategory ed
    let := sA
    let : e.functor.mapDerivedCategory.Braided := by
      change (Monoidal.equivalenceTransported ed).functor.Braided
      infer_instance
    let kfR : ObjectProperty (CochainComplex (Modules R) ℤ) :=
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
    let kfA : ObjectProperty (CochainComplex A ℤ) :=
      CochainComplex.IsKFlatForTotalTensor
    let : kfR.IsMonoidal :=
      { prop_unit := TensorModel.kflat_unit (leftCountable := ringedLeftCountable R) mR
        prop_tensor := TensorModel.kflat_tensor (leftCountable := ringedLeftCountable R) mR }
    let : kfA.IsMonoidal :=
      { prop_unit := totalKFlat_unit
          (leftCountable := leftCountable) (rightCountable := rightCountable)
        prop_tensor := totalKFlat_tensor
          (leftCountable := leftCountable) (rightCountable := rightCountable) }
    let ec := equivLift (e.mapHomologicalComplex (.up ℤ)) kfR kfA
      (fun P hP ↦ (hKFlatF P).mp hP) (fun P hP ↦ (hKFlatG P).mp hP)
    let : ec.functor.Monoidal :=
      (coreLift kfR kfA (e.functor.mapHomologicalComplex (.up ℤ)) tc
        (fun P hP ↦ (hKFlatF P).mp hP)).toMonoidal
    let : ec.functor.LaxBraided :=
      { braided P Q := by
          apply ObjectProperty.hom_ext
          change (tc.μIso P.obj Q.obj).hom ≫
              (e.functor.mapHomologicalComplex (.up ℤ)).map (β_ P.obj Q.obj).hom =
            (β_ ((e.functor.mapHomologicalComplex (.up ℤ)).obj P.obj)
              ((e.functor.mapHomologicalComplex (.up ℤ)).obj Q.obj)).hom ≫
                (tc.μIso Q.obj P.obj).hom
          apply (cancel_mono (tc.μIso Q.obj P.obj).inv).1
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
          rw [hSymF, Iso.hom_inv_id_assoc] }
    let : ec.functor.Braided := {}
    let qR := kfR.ι ⋙ (DerivedCategory.Q (C := Modules R))
    let : qR.Monoidal :=
      (TensorModel.coreOnComplexes (leftCountable := ringedLeftCountable R) kfR mR).toMonoidal
    let : qR.LaxBraided :=
      { braided P Q := by
          change (TensorModel.pair (leftCountable := ringedLeftCountable R) mR
              P.obj Q.obj P.property Q.property).inv ≫
                DerivedCategory.Q.map (β_ P.obj Q.obj).hom =
            (β_ (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj)).hom ≫
              (TensorModel.pair (leftCountable := ringedLeftCountable R) mR
                Q.obj P.obj Q.property P.property).inv
          apply (cancel_mono (TensorModel.pair
            (leftCountable := ringedLeftCountable R) mR
              Q.obj P.obj Q.property P.property).hom).1
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
          rw [TensorModel.symmetry, Iso.inv_hom_id_assoc] }
    let : qR.Braided := {}
    let qA := kfA.ι ⋙ (DerivedCategory.Q (C := A))
    let i : ec.functor ⋙ qA ≅ qR ⋙ e.functor.mapDerivedCategory :=
      (Functor.isoWhiskerLeft kfR.ι e.functor.mapDerivedCategoryFactors).symm
    obtain ⟨qa, hi, hb⟩ := coreAcrossEquivalence ec
      (qR ⋙ e.functor.mapDerivedCategory) qA i
    let := qa.toMonoidal
    let mA := TensorModel.ofMonoidal (leftCountable := leftCountable) kfA hb
    let s := coreOfMonoidal e.functor.mapDerivedCategory
    have hnorm (P Q : CochainComplex (Modules R) ℤ) (hP : kfR P) (hQ : kfR Q) :
        NormalizationEquation (leftCountable := leftCountable) e mR mA tc
          (fun P hP ↦ (hKFlatF P).mp hP) (comparisonOfCore e s) P Q hP hQ := by
      have heq :
          Functor.Monoidal.μIso (ec.functor ⋙ qA) ⟨P, hP⟩ ⟨Q, hQ⟩ ≪≫
              i.app (⟨P, hP⟩ ⊗ ⟨Q, hQ⟩) =
            (i.app ⟨P, hP⟩ ⊗ᵢ i.app ⟨Q, hQ⟩) ≪≫
              Functor.Monoidal.μIso (qR ⋙ e.functor.mapDerivedCategory)
                ⟨P, hP⟩ ⟨Q, hQ⟩ := by
        apply Iso.ext
        exact NatTrans.IsMonoidal.tensor (τ := i.hom) ⟨P, hP⟩ ⟨Q, hQ⟩
      have h := congrArg Iso.inv heq
      dsimp only [NormalizationEquation]
      simp only [Iso.trans_inv, tensorIso_inv] at h
      convert! h.symm using 1
      simp only [Functor.Monoidal.μIso_inv, Functor.OplaxMonoidal.comp_δ,
          Category.assoc]
      rfl
    refine ⟨dA, sA, mA, s, ?_, ?_⟩
    · refine ⟨?_, ?_, hnorm, ?_⟩
      · apply Iso.ext
        have hu := NatTrans.IsMonoidal.unit (τ := i.hom)
        simp only [Functor.LaxMonoidal.comp_ε, Category.assoc] at hu
        change qa.εIso.hom ≫ (DerivedCategory.Q (C := A)).map tc.εIso.hom ≫
            e.functor.mapDerivedCategoryFactors.inv.app (𝟙_ _) =
          Functor.LaxMonoidal.ε e.functor.mapDerivedCategory ≫
            e.functor.mapDerivedCategory.map
              (TensorModel.unit (leftCountable := ringedLeftCountable R) mR).inv at hu
        have h := congrArg (fun f ↦ f ≫ e.functor.mapDerivedCategory.map
          (TensorModel.unit (leftCountable := ringedLeftCountable R) mR).hom) hu
        simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
          Functor.map_id, Category.comp_id] at h
        convert! h.symm using 1
        simp only [unitComparison, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv,
            Iso.symm_inv, Category.assoc]
        rfl
      · intro K L
        change e.functor.mapDerivedCategory.map (β_ K L).hom ≫
            Functor.OplaxMonoidal.δ e.functor.mapDerivedCategory L K = _
        rw [Functor.map_braiding]
        simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
        rfl
      · intro t' ht'
        have := source_localization (R := R)
        exact comparison_ext (leftCountable := leftCountable) e mR mA tc
          (fun P hP ↦ (hKFlatF P).mp hP) t' (comparisonOfCore e s) ht'
          (fun P Q hP hQ _ _ ↦ hnorm P Q hP hQ)
    · intro dA' sA'
      apply comparison_agreement (leftCountable := leftCountable)
        (dA := dA) (sA := sA) e mR mA tc
        (fun P hP ↦ (hKFlatF P).mp hP) s
        (fun P Q hP hQ _ _ ↦ hnorm P Q hP hQ) _ dA' sA'
      intro P
      obtain ⟨K, f, hK, _, hf⟩ :=
        target_resolution e (fun P hP ↦ (hKFlatF P).mp hP) hFlatF P
      exact ⟨K, f, hK, hf⟩

end Conclusion

end CategoryTheory.RingedEquivalenceTensorDescent
