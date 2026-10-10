/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Global sections of the constant sheaf on a connected scheme, derived form

Let `k` be a separably closed field and `a : X ⟶ Spec k` with `X` connected. The global sections
of the constant sheaf are `H⁰(X, Λ) = Λ`. In derived form: the unit `Λ_k ⟶ Ra_* La^* Λ_k` of
`La^* ⊣ Ra_*` induces an isomorphism on `H⁰`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

section

variable {X Y : Scheme.{u}} (a : X ⟶ Y)

/-- The constant sheaf `N` placed in degree `0` of `D(X_ét, Λ)`. -/
noncomputable abbrev singleConstantSheaf (X : Scheme.{u}) (N : ModuleCat.{u + 1} Λ) :
    DerivedCategoryModule Λ X :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)

/-- The derived pullback of the constant sheaf `N` in degree `0` is the constant sheaf `N` in
degree `0`. -/
noncomputable def leftDerivedUpperStarSingleConstantSheafIso (N : ModuleCat.{u + 1} Λ) :
    (L((a)^*[ModuleCat.{u + 1} Λ])).obj (singleConstantSheaf Y N) ≅ singleConstantSheaf X N :=
  (singleFunctorCompLeftDerivedUpperStarIso _ a).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso ((upperStarConstantSheafIso _ a).app N)

lemma leftDerivedUpperStar_map_singleConstantSheaf (N N' : ModuleCat.{u + 1} Λ) (g : N ⟶ N') :
    (L((a)^*[ModuleCat.{u + 1} Λ])).map ((DerivedCategory.singleFunctor _ 0).map
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g)) ≫
      (leftDerivedUpperStarSingleConstantSheafIso a N').hom =
    (leftDerivedUpperStarSingleConstantSheafIso a N).hom ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g) := by
  have h₁ := (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) a).hom.naturality
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g)
  have h₂ := (upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) a).hom.naturality g
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂
  simp only [leftDerivedUpperStarSingleConstantSheafIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% h₁, ← Functor.map_comp, h₂, Functor.map_comp]

end

/-- For a connected scheme `Z`, `N ↦ N_Z[0]` is fully faithful from `Λ`-modules to `D(Z_ét, Λ)`:
the global sections of the constant sheaf are `N`. -/
lemma bijective_map_singleConstantSheaf (Z : Scheme.{u}) [ConnectedSpace Z]
    (N N' : ModuleCat.{u + 1} Λ) :
    Function.Bijective (fun g : N ⟶ N' ↦ (DerivedCategory.singleFunctor _ 0).map
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g)) := by
  have : IsIso (constantSheafAdj Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).unit :=
    have := fun M ↦ isIso_constantSheafAdj_unit_app Z (Λ := Λ) terminalIsTerminal M
    NatIso.isIso_of_isIso_app _
  exact (((constantSheafAdj Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    terminalIsTerminal).fullyFaithfulLOfIsIsoUnit).comp
      (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor _ 0))).map_bijective _ _

/-- For a morphism `a : X ⟶ Y` of connected schemes, the derived pullback is bijective on
morphisms between constant sheaves placed in degree `0`. -/
lemma bijective_leftDerivedUpperStar_map_singleConstantSheaf {X Y : Scheme.{u}} (a : X ⟶ Y)
    [ConnectedSpace X] [ConnectedSpace Y] (N N' : ModuleCat.{u + 1} Λ) :
    Function.Bijective (fun f : singleConstantSheaf Y N ⟶ singleConstantSheaf Y N' ↦
      (L((a)^*[ModuleCat.{u + 1} Λ])).map f) := by
  obtain ⟨hinj, hsurj⟩ := bijective_map_singleConstantSheaf Y N N'
  have hX := bijective_map_singleConstantSheaf X N N'
  have hcomp : ∀ g : N ⟶ N', (L((a)^*[ModuleCat.{u + 1} Λ])).map ((DerivedCategory.singleFunctor _
      0).map ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g)) =
      (leftDerivedUpperStarSingleConstantSheafIso a N).hom ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g) ≫
          (leftDerivedUpperStarSingleConstantSheafIso a N').inv := fun g ↦ by
    rw [← reassoc_of% leftDerivedUpperStar_map_singleConstantSheaf, Iso.hom_inv_id,
      Category.comp_id]
  refine ⟨fun f₁ f₂ h ↦ ?_, fun f ↦ ?_⟩
  · obtain ⟨g₁, rfl⟩ := hsurj f₁
    obtain ⟨g₂, rfl⟩ := hsurj f₂
    simp only [hcomp] at h
    have : (DerivedCategory.singleFunctor _ 0).map
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g₁) =
      (DerivedCategory.singleFunctor _ 0).map
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g₂) := by
      simpa using h
    rw [hX.1 this]
  · obtain ⟨g, hg⟩ := hX.2 ((leftDerivedUpperStarSingleConstantSheafIso a N).inv ≫ f ≫
      (leftDerivedUpperStarSingleConstantSheafIso a N').hom)
    refine ⟨(DerivedCategory.singleFunctor _ 0).map
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g), ?_⟩
    simp only [hcomp]
    simp only at hg
    rw [hg]
    simp

section Point

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))

omit [IsSepClosed k] in
/-- The map `G(k) ⟶ Hom(Λ_k, G)` of global sections of an étale sheaf on `Spec k` is bijective. -/
lemma bijective_homOfGlobalSection
    (G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (fun s : G.obj.obj (op (etalePoint k)) ↦ homOfGlobalSection s) := by
  refine ((constantSheafAdj _ _ isTerminalEtalePoint).homEquiv _ _).symm.bijective.comp
    ⟨fun s t h ↦ ?_, fun φ ↦ ⟨φ.hom 1, ?_⟩⟩
  · simpa using congrArg (fun φ : ModuleCat.of Λ Λ ⟶ _ ↦ φ.hom 1) h
  · ext
    simp [← map_smul]

/-- **`H⁰(X, Λ) = Λ`.** Let `k` be separably closed and `a : X ⟶ Spec k` with `X` connected. The
unit `Λ_k ⟶ Ra_* La^* Λ_k` of `La^* ⊣ Ra_*`, for `Λ_k` the constant sheaf in degree `0`, induces
an isomorphism on `H⁰`. -/
theorem isIso_homologyFunctor_map_unit_singleConstantSheaf [ConnectedSpace X] :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.app
        (singleConstantSheaf (Spec (.of k)) (ModuleCat.of Λ Λ)))) := by
  set S := singleConstantSheaf (Spec (.of k)) (ModuleCat.of Λ Λ) (Λ := Λ)
  set adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a
  set H := DerivedCategory.homologyFunctor (Sheaf (Spec (.of k)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0
  have := Functor.isGE_rightDerivedFunctor_obj_singleFunctor ((a)_*[ModuleCat.{u + 1} Λ])
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))
  have hP : ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((L((a)^*[ModuleCat.{u + 1} Λ])).obj S)).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso
      ((R((a)_*[ModuleCat.{u + 1} Λ])).mapIso
        (leftDerivedUpperStarSingleConstantSheafIso a (ModuleCat.of Λ Λ))).symm 0
  -- composing with the unit is bijective on `Hom(S, S)`
  have h₁ : Function.Bijective (fun f : S ⟶ S ↦ f ≫ adj.unit.app S) := by
    have : (fun f : S ⟶ S ↦ f ≫ adj.unit.app S) =
        (adj.homEquiv S _) ∘ (fun f ↦ (L((a)^*[ModuleCat.{u + 1} Λ])).map f) := by
      funext f
      simp [Adjunction.homEquiv_unit]
    rw [this]
    exact (adj.homEquiv S _).bijective.comp
      (bijective_leftDerivedUpperStar_map_singleConstantSheaf a _ _)
  -- hence composing with `H⁰` of the unit is bijective on `Hom(H⁰ S, H⁰ S)`
  have h₂ : Function.Bijective (fun φ : H.obj S ⟶ H.obj S ↦ φ ≫ H.map (adj.unit.app S)) := by
    have e₁ := DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE (X := S) (Y := S) 0
    have e₂ := DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE (X := S)
      (Y := (R((a)_*[ModuleCat.{u + 1} Λ])).obj ((L((a)^*[ModuleCat.{u + 1} Λ])).obj S)) 0
    have : (fun φ : H.obj S ⟶ H.obj S ↦ φ ≫ H.map (adj.unit.app S)) ∘ (fun f ↦ H.map f) =
        (fun f ↦ H.map f) ∘ (fun f : S ⟶ S ↦ f ≫ adj.unit.app S) := by
      funext f
      simp
    exact (Function.Bijective.of_comp_iff _ e₁).1 (this ▸ e₂.comp h₁)
  -- hence on `Hom(Λ_k, H⁰ S)`, and so on global sections
  set ψ := H.map (adj.unit.app S)
  set c := (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
    ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))
  have h₃ : Function.Bijective (fun φ : (constantSheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) ⟶ H.obj S ↦ φ ≫ ψ) := by
    have : (fun φ : (constantSheaf (Spec (.of k)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) ⟶ H.obj S ↦ φ ≫ ψ) =
        (fun φ ↦ c.inv ≫ φ) ∘ (fun φ : H.obj S ⟶ H.obj S ↦ φ ≫ ψ) ∘ (fun φ ↦ c.hom ≫ φ) := by
      funext φ
      simp
    rw [this]
    exact (c.homFromEquiv.bijective.comp h₂).comp c.homFromEquiv.symm.bijective
  refine isIso_of_bijective_app_etalePoint ψ ?_
  have : (fun s ↦ homOfGlobalSection s) ∘ (ψ.hom.app (op (etalePoint k))) =
      (fun φ ↦ φ ≫ ψ) ∘ (fun s : (H.obj S).obj.obj (op (etalePoint k)) ↦ homOfGlobalSection s) := by
    funext s
    exact (homOfGlobalSection_comp s ψ).symm
  exact (Function.Bijective.of_comp_iff' (bijective_homOfGlobalSection _) _).1
    (this ▸ h₃.comp (bijective_homOfGlobalSection _))

end Point

end AlgebraicGeometry.Etale
