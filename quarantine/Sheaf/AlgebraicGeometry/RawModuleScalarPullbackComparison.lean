/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ConstantModuleSheavesForgetColimits

/-! # The canonical scalar-forgetting inverse-image comparison

Source: Stacks Project, Tags 03D3 and 03D7.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
namespace RawModuleScalarComparison

/-- Forget scalar operations on a module sheaf.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable abbrev forget (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- Scalar forgetting is additive, section by section.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_additive (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (forget Λ X).Additive where
  map_add := by intros; rfl

/-- Scalar forgetting preserves finite limits, as does its presheaf composite.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_preservesFiniteLimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (forget Λ X) := by
  have : PreservesFiniteLimits (forget Λ X ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- Scalar forgetting preserves finite colimits by the constant-coefficient theorem.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_preservesFiniteColimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteColimits (forget Λ X) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1} (forget Λ X) :=
    constantModuleSheaves_forget_preservesColimits X Λ
  infer_instance

/-- The canonical Kan-extension and sheafification scalar comparison.
Its construction is the one in `exists_upperStar_forget₂_natIso`, with no choice
of an arbitrary isomorphism. Source: Stacks Project, Tags 03D3 and 03D7.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable def pullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar (ModuleCat.{u + 1} Λ) f ⋙ forget Λ X ≅
      forget Λ Y ⋙ upperStar AddCommGrpCat.{u + 1} f := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let Z := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  have : Z.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (Int.castRingHom Λ)).isLeftAdjoint
  have : (Z ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    inferInstance
  have : U.IsLeftAdjoint :=
    inferInstanceAs (Z ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  have : X.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification X.smallEtaleTopology U
  let L := (MorphismProperty.Over.pullback @Etale ⊤ f).op
  let P := sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let Q := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let R := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let W := (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj U
  have : U.PreservesLeftKanExtensions L := by
    intro F
    have : U.PreservesPointwiseLeftKanExtension F L := by
      intro c
      let : PreservesColimitsOfShape (CostructuredArrow L c) U :=
        (Adjunction.ofIsLeftAdjoint U).leftAdjoint_preservesColimits.preservesColimitsOfShape
      let : PreservesColimit (CostructuredArrow.proj L c ⋙ F) U :=
        PreservesColimitsOfShape.preservesColimit
      exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit U F L c
    exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise U F L
  let e := sheafComposeNatIso X.smallEtaleTopology U
    (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)
  let e' := U.lanCompIsoOfPreserves L
  change (P ⋙ L.lan ⋙ Q) ⋙ sheafCompose _ U ≅ _
  refine (Functor.associator P (L.lan ⋙ Q) (sheafCompose _ U)) ≪≫ ?_
  refine Functor.isoWhiskerLeft P
    ((Functor.associator L.lan Q (sheafCompose _ U)) ≪≫
      Functor.isoWhiskerLeft L.lan e.symm ≪≫
      (Functor.associator L.lan W R).symm ≪≫
      Functor.isoWhiskerRight e' R) ≪≫ ?_
  exact Iso.refl _

/-- The inverse comparison on a module sheaf.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable abbrev pullback (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (pullbackIso Λ f).inv.app G

/-- The free abelian represented sheaf of an etale object.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable abbrev freeAbelian (S : Scheme.{u}) (U : S.Etale) :=
  (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free)

/-- Send the represented abelian generator to the represented module generator.
Source: Stacks Project, Tag 03FD, the equality of section complexes.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable def freeMap (Λ : Type (u + 1)) [CommRing Λ]
    (S : Scheme.{u}) (U : S.Etale) :
    freeAbelian S U ⟶ (forget Λ S).obj ((freeSheaf Λ S).obj U) := by
  let e : (freeAbelian S U ⟶ (forget Λ S).obj ((freeSheaf Λ S).obj U)) ≃
      ((forget Λ S).obj ((freeSheaf Λ S).obj U)).obj.obj (op U) :=
    ((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free) _).trans
      ((((AddCommGrpCat.adj).whiskerRight S.Etaleᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv)
  exact e.symm ((freeSheafHomEquiv Λ U ((freeSheaf Λ S).obj U)) (𝟙 _))

end RawModuleScalarComparison
end AlgebraicGeometry.Etale
