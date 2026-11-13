/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.FiniteConstantAbelianNeighborhood

/-!
# Refining a finite set trivialization to an abelian trivialization

## References

* Stacks Project, Tag 03RU.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- An abelian sheaf whose underlying restriction has a specified finite constant value
admits abelian constant trivializations after an etale refinement of that member.
(Stacks, Tag 03RU.) -/
theorem finite_constant_abelian_refinement {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : Y.Etale)
    (S : Type (u + 1)) [Finite S]
    (e : ((sheafCompose Y.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).over U ≅
        (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1))).obj S) :
    ∃ 𝒱 : Cover.{u} etalePrecoverage U.left, ∀ j : 𝒱.I₀,
      (G.over ((MorphismProperty.Over.map ⊤ U.prop).obj
        (𝒱.etalePrecoverageToEtale j))).IsConstant
          (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj
            (𝒱.etalePrecoverageToEtale j))) := by
  classical
  choose V v hv M hM e' α hα using
    finite_constant_abelian_neighborhood G U S e
  let 𝒱 : Cover.{u} etalePrecoverage U.left :=
    Cover.mkOfCovers U.left (fun x ↦ (V x).left) (fun x ↦ (V x).hom)
      (fun x ↦ ⟨x, v x, hv x⟩) (fun x ↦ (V x).prop)
  refine ⟨𝒱, fun x ↦ ?_⟩
  let W : Y.Etale := (MorphismProperty.Over.map ⊤ U.prop).obj (V x)
  let J := Y.smallEtaleTopology.over W
  let F := G.over W
  have : IsIso (e' x).hom.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf J (Type (u + 1))).map (e' x).hom))
  have hi : Presheaf.IsLocallyInjective J (α x) := by
    rw [← Presheaf.isLocallyInjective_forget_iff, hα x]
    have ht : Presheaf.IsLocallyInjective J (toSheafify J
        ((Functor.const (Over W)ᵒᵖ).obj (M x : Type (u + 1)))) := inferInstance
    exact Presheaf.isLocallyInjective_comp J _ _
  have hs : Presheaf.IsLocallySurjective J (α x) := by
    rw [Presheaf.isLocallySurjective_iff_whisker_forget, hα x]
    have ht : Presheaf.IsLocallySurjective J (toSheafify J
        ((Functor.const (Over W)ᵒᵖ).obj (M x : Type (u + 1)))) := inferInstance
    exact Presheaf.isLocallySurjective_comp (J := J)
      (toSheafify J ((Functor.const (Over W)ᵒᵖ).obj (M x : Type (u + 1))))
      (e' x).hom.hom
  have hw : J.W (α x) := J.W_of_isLocallyBijective (α x)
  have : IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map (α x)) :=
    (J.W_iff (α x)).mp hw
  exact Sheaf.isConstant_of_iso J
    ((asIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map (α x))) ≪≫
      asIso ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit.app F)).symm

end AlgebraicGeometry.Scheme
