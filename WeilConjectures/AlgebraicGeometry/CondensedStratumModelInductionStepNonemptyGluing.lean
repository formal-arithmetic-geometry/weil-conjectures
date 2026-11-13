/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleOpenClosedImages
import WeilConjectures.AlgebraicGeometry.CondensedFiniteCoefficientLocalization
import WeilConjectures.AlgebraicGeometry.CondensedFiniteModelExtensions

/-! Intermediate support-induction branch. -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option linter.style.haveILetI false

set_option backward.isDefEq.respectTransparency true in
private theorem modelOfLocalizedTriangle
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F))
    (hP : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E) P)
    (hQ : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ F) Q)
    (h : ∃ D : Pretriangulated.Triangle (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))),
      D ∈ @Pretriangulated.distinguishedTriangles _ _ _ _ _ _ _ ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj P) ≅ D.obj₁) ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).obj Q) ≅ D.obj₃) ∧
      Nonempty ((DerivedCategory.homologyFunctor _ 0).obj D.obj₂ ≅ N)) :
    ∃ (H : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (R : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObj X ℓ H)),
      IsConstructibleModuleObject (padicSubfieldRingObj X ℓ H) R ∧
      Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ H)).obj R ≅ N) := by
  obtain ⟨D, hD, h₁, h₃, ⟨eN⟩⟩ := h
  obtain ⟨H, R, hR, ⟨eR⟩⟩ := exists_finiteCoefficient_model_of_triangle X ℓ D hD
    ⟨E, P, hP, h₁⟩ ⟨F, Q, hQ, h₃⟩
  exact ⟨H, R, hR, ⟨eR ≪≫ eN⟩⟩

set_option backward.isDefEq.respectTransparency true in
private theorem pullbackModelComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (h : Nonempty (P ≅ (CondensedRing.upperStar Λ (f ≫ g)).obj M)) :
    Nonempty (P ≅ (CondensedRing.upperStar Λ f).obj
      ((CondensedRing.upperStar Λ g).obj M)) := by
  obtain ⟨e⟩ := h
  exact ⟨e ≪≫ (CondensedRing.upperStarComp Λ f g).app M⟩

/- The imported interfaces separate constructibility, geometric localization, and
  extension-class descent in the support induction argument. -/

set_option backward.isDefEq.respectTransparency true in
/-- Glue compatible open/closed models by finite-stage extension classification.
-/
theorem glue_nonempty_support_open_closed_models
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ))
    {Y : Scheme.{u}} (i : Y ⟶ T) [IsClosedImmersion i] [Nonempty Y]
    {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    {Z : Scheme.{u}} (k : Z ⟶ Y) [IsClosedImmersion k]
    (hcover : Set.range j ∪ Set.range k = Set.univ)
    (hdisj : Disjoint (Set.range j) (Set.range k))
    (EU : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (PU : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (padicSubfieldRingObj U ℓ EU))
    (EZ : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (PZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (padicSubfieldRingObj Z ℓ EZ))
    (hPU : IsConstructibleModuleObject (padicSubfieldRingObj U ℓ EU) PU)
    (hPZ : IsConstructibleModuleObject (padicSubfieldRingObj Z ℓ EZ) PZ)
    (eU : Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl U ℓ EU)).obj PU ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (j ≫ i)).obj M))
    (eZ : Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Z ℓ EZ)).obj PZ ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (k ≫ i)).obj M)) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (padicSubfieldRingObj Y ℓ E)),
      IsConstructibleModuleObject (padicSubfieldRingObj Y ℓ E) P ∧
      Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).obj P ≅
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) i).obj M) := by
  haveI : TopologicalSpace.NoetherianSpace Y :=
    i.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  have hjk : Set.range j = (Set.range k)ᶜ := by
    ext y
    constructor
    · intro hy hz
      exact Set.disjoint_left.mp hdisj hy hz
    · intro hy
      have hy' : y ∈ Set.range j ∪ Set.range k := hcover.symm ▸ Set.mem_univ y
      exact hy'.resolve_right hy
  have eU' := pullbackModelComp (Profinite.padicAlgClRingObj ℓ) j i _ M eU
  have eZ' := pullbackModelComp (Profinite.padicAlgClRingObj ℓ) k i _ M eZ
  -- Keep the pullback object abstract during the coefficient-model argument.
  generalize hN : (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) i).obj M = N
    at eU' eZ' ⊢
  have : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hU := (CondensedRing.constructible_open_closed_images
    (Profinite.continuousMapRingObj.{u} EU) j k hjk).1 PU hPU
  have hZ := (CondensedRing.constructible_open_closed_images
    (Profinite.continuousMapRingObj.{u} EZ) j k hjk).2 PZ hPZ
  have h := exists_finiteCoefficient_localization_triangle Y ℓ N j k hjk EU PU EZ PZ
    eU' eZ'
  apply modelOfLocalizedTriangle Y ℓ N EU EZ
    ((CondensedRing.openImmersionLowerShriek
      (Profinite.continuousMapRingObj.{u} EU) j).obj PU)
    ((CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} EZ) k).obj PZ)
    hU hZ
  exact h

end AlgebraicGeometry.ProEtale
