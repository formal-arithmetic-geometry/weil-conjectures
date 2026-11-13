/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.CategoryTheory.Presentable.Limits
import WeilConjectures.AlgebraicGeometry.ConstructibleAffineFreePresentationGeneral
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFilteredColimit
import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardLimit
import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FiniteApproximation

/-! # Finite-stage factorization with Noetherian coefficients

Source: Stacks Project, Tags 09Z6, 09Z4, 09YZ and 09Z1.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Etale

private noncomputable def affineFreeHomEquiv
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (W : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ⟶ F) ≃
      F.obj.obj (Opposite.op W) :=
  ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).homEquiv _ _).trans
    (((ModuleCat.adj Λ).whiskerRight X.Etaleᵒᵖ).homEquiv _ _ |>.trans uliftYonedaEquiv)

private theorem affineFreeHomEquiv_comp
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (W : X.Etale) {F H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (p : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ⟶ F) (f : F ⟶ H) :
    affineFreeHomEquiv W H (p ≫ f) = f.hom.app (Opposite.op W) (affineFreeHomEquiv W F p) := by
  simp only [affineFreeHomEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def affineFreeCoyonedaIso
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] (W : X.Etale) :
    coyoneda.obj (Opposite.op ((presheafToSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ))) ≅
      (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (Opposite.op W) ⋙
        CategoryTheory.forget (ModuleCat.{u + 1} Λ) :=
  NatIso.ofComponents (fun F ↦ (affineFreeHomEquiv W F).toIso) (by
    intro F H f
    ext p
    exact affineFreeHomEquiv_comp W p f)

private theorem affineFree_finitelyPresentable
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (W : X.Etale) [IsAffine W.left] :
    IsFinitelyPresentable.{u}
      ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)) := by
  let := Cardinal.fact_isRegular_aleph0.{u}
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let E := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (Opposite.op W)
  have : PreservesFilteredColimitsOfSize.{u, u} E := by
    refine ⟨fun I _ _ ↦ ⟨fun {D} ↦ ?_⟩⟩
    have : IsIso ((colimit.isColimit (D ⋙ E)).desc (E.mapCocone (colimit.cocone D))) :=
      (ConcreteCategory.isIso_iff_bijective _).2
      (etale_sections_filtered_colimit X Λ W I D (colimit.cocone D) (colimit.isColimit D))
    exact preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
      ((colimit.isColimit (D ⋙ E)).ofPointIso)
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  refine ⟨fun I _ _ ↦ ?_⟩
  exact preservesColimitsOfShape_of_natIso (affineFreeCoyonedaIso W).symm

private theorem finitelyPresentable_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    IsFinitelyPresentable.{u} F := by
  let := Cardinal.fact_isRegular_aleph0.{u}
  classical
  let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W ↦
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
  obtain ⟨n, m, U, V, hU, hV, f, g, w, ⟨hg⟩⟩ :=
    Scheme.exists_affine_free_etale_presentation_general X Λ F
  have hfree (W : X.Etale) (hW : IsAffine W.left) : IsFinitelyPresentable.{u} (P W) := by
    have := hW
    exact affineFree_finitelyPresentable W
  have hsum (k : ℕ) (W : Fin k → X.Etale) (hW : ∀ i, IsAffine (W i).left) :
      IsFinitelyPresentable.{u} (∐ fun i ↦ P (W i)) := by
    have (i : Discrete (Fin k)) : IsFinitelyPresentable.{u}
        ((Discrete.functor (fun i ↦ P (W i))).obj i) := hfree (W i.as) (hW i.as)
    exact isCardinalPresentable_of_isColimit' _
      (colimit.isColimit (Discrete.functor (fun i ↦ P (W i)))) Cardinal.aleph0.{u}
      ((hasCardinalLT_aleph0_iff _).2 inferInstance)
  have (i : WalkingParallelPair) : IsFinitelyPresentable.{u} ((parallelPair f 0).obj i) := by
    cases i
    · exact hsum m V hV
    · exact hsum n U hU
  exact isCardinalPresentable_of_isColimit' _ hg Cardinal.aleph0.{u}
    ((hasCardinalLT_aleph0_iff _).2 inferInstance)


/-- A map from a constructible module sheaf to an integral pushforward of a finite constant
module factors through a finite pushforward of that same constant module.
(Stacks, Tags 09Z6, 09YZ, 09Z1 and 09Z4) -/
theorem exists_finite_lowerStar_factorization_noetherian
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F]
    {Y : Scheme.{u}} (ν : Y ⟶ X) [IsIntegralHom ν]
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (φ : F ⟶ (lowerStar (ModuleCat.{u + 1} Λ) ν).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X), IsFinite f ∧
      ∃ (ψ : F ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
        (κ : (lowerStar (ModuleCat.{u + 1} Λ) f).obj
          ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ⟶
          (lowerStar (ModuleCat.{u + 1} Λ) ν).obj
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)),
        ψ ≫ κ = φ := by
  classical
  have : IsFinitelyPresentable.{u} F := finitelyPresentable_constructible Λ F
  obtain ⟨A⟩ := ν.nonempty_finiteApproximation_of_isIntegralHom
  let D := constantModulePushforwardDiagram Λ M A.D A.p A.map_p
  let c := constantModulePushforwardCocone Λ M A.D A.p A.map_p ν A.π A.π_p
  obtain ⟨hc⟩ := isColimit_constantModulePushforwardCocone Λ M A.D A.p A.map_p
    ν A.π A.π_p A.isLimit
  obtain ⟨i, p, hp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc φ
  exact ⟨A.D.obj i.unop, A.p i.unop, A.isFinite_p i.unop,
    p, c.ι.app i, hp⟩

end AlgebraicGeometry.Etale
