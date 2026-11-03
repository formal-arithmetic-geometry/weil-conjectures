/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo

/-! # Ordinary-module presentation of derived change of rings

Source: Stacks Project, Tags 06YY, 06XN, 06Y1 and 0A6A.
(blueprint: lem-pur-derived-change-of-rings).
The generic ringed-site construction remains publicly imported. The additional
presentation retains ordinary module complexes and normalizes the tensor comparison
by the ordinary scalar-extension tensor comparison on K-flat representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ModuleCat


-- A full, essentially surjective functor is initial: every comma object maps
-- to a fixed lift of the target, giving a zigzag between any two objects.
section LocalizationTensor

universe v w
variable {A : Type*} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

end LocalizationTensor

section UniversalPair

universe v w
variable {A B : Type*} [Category.{v} A] [Category.{w} B] [Abelian A] [Abelian B]
  [IsGrothendieckAbelian.{v} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [MonoidalClosed A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  [HasDerivedCategory.{v} A] [HasDerivedCategory.{w} B]
  [HasColimitsOfSize.{0, 0} A]

end UniversalPair

end ModuleCat

namespace ModuleCat

/-- The ordinary-module universal pair, including its canonical tensor structure.
Source: Stacks 06YY and 0A6A (blueprint: lem-pur-derived-change-of-rings).
The tensor equation fixes the structure on resolving representatives, so the
monoidal structure is not arbitrary extra data. -/
structure OrdinaryDerivedChangeOfRings {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) where
  F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S)
  counit : DerivedCategory.Q ⋙ F ⟶
    (extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : F.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
  pointwise : ((extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
  computes : ∀ P : CochainComplex (ModuleCat.{u} R) ℤ,
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P →
      IsIso (counit.app P)
  triangulated : ∃ (_ : F.CommShift ℤ), F.IsTriangulated
  [monoidal : F.Monoidal]
  unit_normalized :
    F.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
        counit.app (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ≫
        DerivedCategory.Q.map (Functor.OplaxMonoidal.η
          ((extendScalars φ).mapHomologicalComplex (.up ℤ))) =
      Functor.OplaxMonoidal.η F ≫ Functor.LaxMonoidal.ε DerivedCategory.Q
  tensor_normalized : ∀ (P Q : CochainComplex (ModuleCat.{u} R) ℤ),
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat Q →
    Functor.LaxMonoidal.μ F (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
        F.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫ counit.app (P ⊗ Q) ≫
        DerivedCategory.Q.map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
            (extendScalars φ)).app P).app Q) =
      (counit.app P ⊗ₘ counit.app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          (((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)
          (((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj Q)

private theorem ordinary_Q_μ [HasColimitsOfSize.{0, 0} A]
    (P Q : CochainComplex A ℤ)
    (hQ : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat Q) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  have hQh := (HomotopyCategory.kFlat_quotient_obj_iff Q).2 hQ
  have := DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (.up ℤ))
      ((HomotopyCategory.quotient _ _).obj P) _ hQh
  have h : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ _).obj P)
      ((HomotopyCategory.quotient _ _).obj Q)) := this
  change IsIso ((_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
    DerivedCategory.Qh.map _) ≫ _)
  infer_instance

private theorem ordinary_Q_ε :
    IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := A))) := by
  have := DerivedCategory.isIso_ε_Qh A
  change IsIso ((Functor.LaxMonoidal.ε DerivedCategory.Qh ≫ DerivedCategory.Qh.map
    (Functor.LaxMonoidal.ε (HomotopyCategory.quotient _ _))) ≫ _)
  infer_instance

private theorem ordinary_kflat_map {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} S) (.up ℤ)).kFlat
      (((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P) := by
  have hp := (HomotopyCategory.kFlat_iff_preserves_acyclic _).1
    ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
  have hp' (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.Acyclic) :
      (CochainComplex.mapBifunctor L P (curriedTensor _)).Acyclic := by
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (hp ((HomotopyCategory.quotient _ _).obj L)
        ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hL)).2
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨L, rfl⟩ := N.quotient_obj_surjective
  have hL := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 hN
  have h := CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ P hp' L hL
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 h
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩

-- The cochain universal pair is obtained from the existing K-flat derivability structure.

private theorem ordinary_pair (E : A ⥤ B) [E.Additive] [E.PreservesKFlatQuasiIso] :
    ∃ (F : DerivedCategory A ⥤ DerivedCategory B)
      (ε : DerivedCategory.Q ⋙ F ⟶
        E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      F.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
          (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      (∃ (_ : F.CommShift ℤ), F.IsTriangulated) ∧
      ∀ P, (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P →
        IsIso (ε.app P) := by
  let H := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let P : Set (HomotopyCategory A (.up ℤ)) :=
    (HomotopyCategory.quasiIso A (.up ℤ)).kFlat
  have hres (X : HomotopyCategory A (.up ℤ)) :
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    obtain ⟨L⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
      (Φ := (HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat) X
    exact ⟨L.X₁.obj, L.w, L.X₁.property, L.hw⟩
  obtain ⟨hpw, F, ε, hu, ht, hc⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) H P hres
      (fun _ _ f hX hY hf ↦ E.isIso_Qh_map_mapHomotopyCategory_map hX hY f hf)
  let : H.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) := hpw
  let : F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) := hu
  let q := HomotopyCategory.quotient A (.up ℤ)
  let α := (Functor.associator q DerivedCategory.Qh F).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh H F ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor F ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ H ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let β := Functor.whiskerRight i.inv F ≫ α ≫ j.hom
  have hβ := pointwise_change_iso F i j α hα
  refine ⟨F, β, ⟨hβ.isRightKanExtension⟩, ?_, ht, ?_⟩
  · intro X
    exact (Functor.hasPointwiseLeftDerivedFunctorAt_iff _ DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) X).2
        ((hβ _).hasPointwiseRightKanExtensionAt)
  · intro K hK
    have := hc (q.obj K) ((HomotopyCategory.kFlat_quotient_obj_iff K).2 hK)
    dsimp [β, α]
    infer_instance

/-- Ordinary module complexes admit normalized strong monoidal derived scalar extension.
Source: Stacks 06YY, 06XN, 06Y1 and 0A6A (blueprint: lem-pur-derived-change-of-rings).

Proof:
1. Ordinary scalar extension preserves quasi-isomorphisms between K-flat complexes.
   Apply the existing resolving-class theorem to its homotopy functor followed by
   localization. Transfer its pointwise universal pair through the full, essentially
   surjective homotopy quotient, using initial restriction of the defining limit cones.
   This gives the cochain counit, triangulatedness and its K-flat computation property.
2. Scalar extension preserves K-flatness: tensor an acyclic target complex with an
   extended K-flat complex, restrict scalars, and use the existing tensor comparison.
   Thus the target localization tensorator is invertible on extended K-flat models.
3. Both tensor-after-deriving and derive-after-tensoring are two-variable left derived
   functors: on two K-flat models their counits are invertible. Derive the ordinary
   scalar-extension tensor isomorphism to obtain an invertible comparison between them.
   Its defining localization equation is the required counit square.
4. Apply the existing oplax-of-lax-square coherence construction, using K-flat models
   of every derived object and invertibility of the target localization tensorator.
   Its unit is the prescribed counit composite, hence invertible; its tensor map is
   the derived isomorphism. Invert these maps to obtain a strong monoidal structure.
   The unit normalization cancels the target localization unit; tensor normalization
   follows by composing the defining counit square with the inverse tensor comparison.
No flatness of the ring map or bounds on complexes are used. The universal pair is
unique up to its counit-compatible isomorphism, with tensor structure fixed by the square. -/
theorem nonempty_ordinaryDerivedChangeOfRings {R S : Type u}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    Nonempty (OrdinaryDerivedChangeOfRings φ) := by
  classical
  have : (extendScalars φ).PreservesKFlatQuasiIso := extendScalars_preservesKFlatQuasiIso φ
  obtain ⟨F, ε, hu, hp, ht, hc⟩ := ordinary_pair (extendScalars φ)
  let E := (extendScalars φ).mapHomologicalComplex (.up ℤ)
  let T := (((Functor.whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor _)
  let U := (Functor.postcompose₂.obj F).obj (curriedTensor _)
  let a : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj T ⟶
      (((Functor.whiskeringLeft₂ _).obj E).obj E).obj
        ((Functor.postcompose₂.obj DerivedCategory.Q).obj (curriedTensor _)) :=
    (((Functor.whiskeringLeft₂ _).map ε).app (DerivedCategory.Q ⋙ F)).app
        (curriedTensor _) ≫
      (((Functor.whiskeringLeft₂ _).obj (E ⋙ DerivedCategory.Q)).map ε).app
        (curriedTensor _) ≫
      (((Functor.whiskeringLeft₂ _).obj E).obj E).map
        (Functor.LaxMonoidal.μNatTrans DerivedCategory.Q)
  let b : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj U ⟶
      (Functor.postcompose₂.obj (E ⋙ DerivedCategory.Q)).obj (curriedTensor _) :=
    (Functor.postcompose₂.obj F).map (Functor.LaxMonoidal.μNatTrans DerivedCategory.Q) ≫
      (Functor.postcompose₂.map ε).app (curriedTensor _)
  have ha : T.IsLeftDerivedFunctor₂ a
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).localizerMorphismKFlat
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).localizerMorphismKFlat
    intro P Q
    have := hc P.obj P.property
    have := hc Q.obj Q.property
    have hμ := ordinary_Q_μ (E.obj P.obj) (E.obj Q.obj)
      (ordinary_kflat_map φ Q.obj Q.property)
    dsimp only [a, NatTrans.comp_app]
    exact IsIso.comp_isIso'
      (inferInstanceAs (IsIso (ε.app P.obj ▷ _)))
      (IsIso.comp_isIso' (inferInstanceAs (IsIso (_ ◁ ε.app Q.obj))) hμ)
  have hb : U.IsLeftDerivedFunctor₂ b
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).localizerMorphismKFlat
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).localizerMorphismKFlat
    intro P Q
    have := ordinary_Q_μ P.obj Q.obj Q.property
    have := hc (P.obj ⊗ Q.obj)
      ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat.prop_tensor
        P.property Q.property)
    exact IsIso.comp_isIso'
      (Functor.map_isIso F (Functor.LaxMonoidal.μ DerivedCategory.Q P.obj Q.obj))
      (inferInstanceAs (IsIso (ε.app (P.obj ⊗ Q.obj))))
  have hEδ : IsIso (Functor.OplaxMonoidal.δNatTrans E) := inferInstance
  let di : U ≅ T := Functor.leftDerived₂NatIso T a
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) U b
    ((Functor.postcompose₂.obj DerivedCategory.Q).mapIso
      (asIso (Functor.OplaxMonoidal.δNatTrans E)))
  let d : U ⟶ T := di.hom
  have hd : IsIso d := di.isIso_hom
  have hsq (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
      (d.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
          (ε.app P ⊗ₘ ε.app Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q (E.obj P) (E.obj Q) =
        F.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫ ε.app (P ⊗ Q) ≫
          DerivedCategory.Q.map (Functor.OplaxMonoidal.δ E P Q) := by
    have h := Functor.leftDerived₂NatTrans_app_app T a
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) U b
      ((Functor.postcompose₂.obj DerivedCategory.Q).map
        (Functor.OplaxMonoidal.δNatTrans E)) P Q
    change (d.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
      ((ε.app P ▷ _) ≫ (_ ◁ ε.app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (E.obj P) (E.obj Q)) =
      (F.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫ ε.app (P ⊗ Q)) ≫
        DerivedCategory.Q.map (Functor.OplaxMonoidal.δ E P Q) at h
    simpa only [tensorHom_def, Category.assoc] using h
  have hmodels (X : DerivedCategory (ModuleCat.{u} R)) :
      ∃ P, (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ X) := by
    obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_kFlat_iso X
    obtain ⟨P, rfl⟩ := P.quotient_obj_surjective
    exact ⟨P, (HomotopyCategory.kFlat_quotient_obj_iff P).1 hP,
      ⟨(DerivedCategory.quotientCompQhIso _).symm.app P ≪≫ e⟩⟩
  have := ordinary_Q_ε (A := ModuleCat.{u} S)
  let oplax : F.OplaxMonoidal := Functor.OplaxMonoidal.ofLaxSquare'
    (Q₁ := DerivedCategory.Q) (Q₂ := DerivedCategory.Q) (F := E) d
    (fun P ↦ ε.app P) (fun _ _ f ↦ ε.naturality f) hsq
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat hmodels hc
    (fun P Q hQ ↦ ordinary_Q_μ P (E.obj Q) (ordinary_kflat_map φ Q hQ))
  have hη : IsIso (Functor.OplaxMonoidal.η F) := by
    have := ordinary_Q_ε (A := ModuleCat.{u} R)
    have := hc (𝟙_ _) (ObjectProperty.prop_unit
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat)
    change IsIso (F.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫ ε.app (𝟙_ _) ≫
      DerivedCategory.Q.map (Functor.OplaxMonoidal.η E) ≫
        CategoryTheory.inv (Functor.LaxMonoidal.ε DerivedCategory.Q))
    infer_instance
  have hδ (X Y : DerivedCategory (ModuleCat.{u} R)) :
      IsIso (Functor.OplaxMonoidal.δ F X Y) :=
    inferInstanceAs (IsIso ((d.app X).app Y))
  let mon : F.Monoidal := (Functor.CoreMonoidal.ofOplaxMonoidal F).toMonoidal
  refine ⟨{ F := F
            counit := ε
            universal := hu
            pointwise := hp
            computes := hc
            triangulated := ht
            monoidal := mon
            unit_normalized := ?_
            tensor_normalized := ?_ }⟩
  · change _ = (_ ≫ _ ≫ _ ≫ CategoryTheory.inv _) ≫ _
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rfl
  · intro P Q _ _
    have h := hsq P Q
    change Functor.OplaxMonoidal.δ F (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
      (ε.app P ⊗ₘ ε.app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (E.obj P) (E.obj Q) = _ at h
    have h' := congrArg
      (Functor.LaxMonoidal.μ F (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫ ·) h
    have hcomp := Functor.mapCochainComplex_δ (extendScalars φ) P Q
    rw [← hcomp]
    simpa only [← Category.assoc, Functor.Monoidal.μ_δ, Category.id_comp] using h'.symm

/-- Fix the universal pair with its normalized tensor structure. Its universal
property determines it up to the unique counit-compatible isomorphism, which is the
notion of equality used in derived scalar extension.
Source: Stacks 06YY and 0A6A (blueprint: lem-pur-derived-change-of-rings). -/
def ordinaryDerivedChangeOfRings {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : OrdinaryDerivedChangeOfRings φ :=
  Classical.choice (nonempty_ordinaryDerivedChangeOfRings φ)

/-- Derived scalar extension for ordinary modules, with the canonical K-flat counit.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
def ordinaryDerivedExtendScalars {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  (ordinaryDerivedChangeOfRings φ).F

end ModuleCat
