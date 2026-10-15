module

public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! The Hom-equivalence data for the ringed-slice tensor projection formula. -/

@[expose] public section

universe uC u

open CategoryTheory

namespace SheafOfModules

noncomputable def ringedSliceTensorLeft
    {C : Type uC} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}] :
    (SheafOfModules.{u} (((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R).over U) ×
      SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R)) ⥤
      SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R) :=
  letI := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  letI := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  ((forget.{u} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)).prod
      (overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ⋙ forget.{u}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ⋙
    MonoidalCategory.tensor
      (C := PresheafOfModules.{u} ((R.over U).obj ⋙
        forget₂ CommRingCat RingCat)) ⋙
    PresheafOfModules.sheafification (J := J.over U)
      (R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U) (𝟙 _) ⋙
    extensionByZeroPresheaf.{u} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R) U ⋙
    PresheafOfModules.sheafification (𝟙 ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R).obj))

noncomputable def ringedSliceTensorRight
    {C : Type uC} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}] :
    (SheafOfModules.{u} (((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R).over U) ×
      SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R)) ⥤
      SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj R) :=
  letI := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  letI := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  (((extensionByZeroPresheaf.{u} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R) U ⋙
        PresheafOfModules.sheafification (𝟙 ((sheafCompose J
          (forget₂ CommRingCat RingCat)).obj R).obj) ⋙
        forget.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).prod
      (forget.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ⋙
    MonoidalCategory.tensor
      (C := PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) ⋙
    PresheafOfModules.sheafification (𝟙 ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R).obj))

/--
The Hom-equivalence family underlying the ringed-slice projection formula.

Source: Stacks Project, Modules on Sites, Tag 0E8I, lemma-j-shriek-and-tensor.
(blueprint: new-ringed-slice-extension-tensor-hom-data)

Proof: For a test module H, use the extension-by-zero adjunction, the sectionwise
tensor-Hom equivalences on the two sites, and the restriction comparison for internal
Hom.  Compose these equivalences in the order described in the parent projection
formula.  Naturality in H is the naturality of each adjunction and tensor-Hom
equivalence; naturality in the parameter pair follows from the corresponding
parameter naturality of those same constructions.  The statement records precisely
this Hom-level data, leaving the Yoneda reconstruction to the parent theorem.
-/
theorem ringedSlice_extension_tensor_hom_data
    {C : Type uC} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}] :
    let S := SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)
    let T := SheafOfModules.{u} (((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R).over U)
    ∃ e : ∀ X : T × S, ∀ H : S,
      (((ringedSliceTensorLeft J R U).obj X ⟶ H) ≃
        ((ringedSliceTensorRight J R U).obj X ⟶ H)),
      (∀ (X : T × S) (H K : S)
          (φ : (ringedSliceTensorLeft J R U).obj X ⟶ H) (h : H ⟶ K),
        e X K (φ ≫ h) = e X H φ ≫ h) ∧
      (∀ (X Y : T × S) (H : S) (f : X ⟶ Y)
          (φ : (ringedSliceTensorLeft J R U).obj Y ⟶ H),
        e X H ((ringedSliceTensorLeft J R U).map f ≫ φ) =
          (ringedSliceTensorRight J R U).map f ≫ e Y H φ) := by
  sorry

end SheafOfModules
