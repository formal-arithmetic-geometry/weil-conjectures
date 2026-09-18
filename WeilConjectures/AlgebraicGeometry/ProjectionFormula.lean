/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.IntersectionNumber
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal

/-!
# The generic rank and the projection formula for intersection numbers
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (P : X.Modules)

/-- The sections of a direct image over an open whose preimage is empty vanish. -/
lemma subsingleton_sections_pushforward_of_preimage_eq_bot {W : Y.Opens} (hW : f ⁻¹ᵁ W = ⊥) :
    Subsingleton Γ((pushforward f).obj P, W) := by
  have h : Γ((pushforward f).obj P, W) = Γ(P, ⊥) := by
    rw [pushforward_obj_obj f P W, hW]
  rw [h]
  infer_instance

/-- **The stalks of a direct image vanish away from the image**, in the form in which the
dévissage argument uses it: at a point with a neighbourhood whose preimage is empty. -/
lemma subsingleton_stalk_pushforward {y : Y} {W : Y.Opens} (hy : y ∈ W) (hW : f ⁻¹ᵁ W = ⊥) :
    Subsingleton (((pushforward f).obj P).presheaf.stalk y) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨U, hyU, s, rfl⟩ := ((pushforward f).obj P).presheaf.exists_germ_eq a
  obtain ⟨V, hyV, t, rfl⟩ := ((pushforward f).obj P).presheaf.exists_germ_eq b
  have hyW : y ∈ U ⊓ V ⊓ W := ⟨⟨hyU, hyV⟩, hy⟩
  have hbot : f ⁻¹ᵁ (U ⊓ V ⊓ W) = ⊥ := by
    rw [← le_bot_iff, ← hW]
    exact fun x hx ↦ hx.2
  have : Subsingleton Γ((pushforward f).obj P, U ⊓ V ⊓ W) :=
    subsingleton_sections_pushforward_of_preimage_eq_bot f P hbot
  rw [← TopCat.Presheaf.germ_res_apply ((pushforward f).obj P).presheaf
      (homOfLE (inf_le_left.trans inf_le_left) : U ⊓ V ⊓ W ⟶ U) y hyW s,
    ← TopCat.Presheaf.germ_res_apply ((pushforward f).obj P).presheaf
      (homOfLE (inf_le_left.trans inf_le_right) : U ⊓ V ⊓ W ⟶ V) y hyW t]
  exact congrArg _ (Subsingleton.elim _ _)

/-- **The stalk of a direct image along a closed immersion vanishes off the image.** -/
lemma subsingleton_stalk_pushforward_of_notMem_range (hf : IsClosed (Set.range f.base)) {y : Y}
    (hy : y ∉ Set.range f.base) :
    Subsingleton (((pushforward f).obj P).presheaf.stalk y) :=
  subsingleton_stalk_pushforward f P (W := ⟨(Set.range f.base)ᶜ, hf.isOpen_compl⟩) hy
    (by ext x; simp)

end Pushforward

section GenericRank

variable {X : Scheme.{u}}

/-- **The stalk of a coherent sheaf at the generic point of an integral scheme is a
finite-dimensional vector space over the function field**, so that the generic rank is the
dimension of a finite-dimensional space. -/
instance finiteDimensional_stalk_genericPoint [IsIntegral X] (F : X.Modules) [F.IsCoherent] :
    FiniteDimensional X.functionField (F.presheaf.stalk (genericPoint X)) :=
  finite_stalk F (genericPoint X)

/-- **The generic rank of a coherent sheaf vanishes exactly when the generic point is not in its
support.** -/
lemma genericRank_eq_zero_iff [IsIntegral X] (F : X.Modules) [F.IsCoherent] :
    genericRank F = 0 ↔ genericPoint X ∉ F.support := by
  rw [genericRank, Module.finrank_zero_iff, support, Set.mem_ofPred_eq,
    not_nontrivial_iff_subsingleton]

/-- **The generic rank is monotone along a monomorphism** of sheaves of modules on an integral
scheme. -/
lemma genericRank_le_of_mono [IsIntegral X] {G H : X.Modules} (u : G ⟶ H) [Mono u]
    [H.IsCoherent] : genericRank G ≤ genericRank H := by
  have hmono : Mono (C := SheafOfModules.{u} X.ringCatSheaf) u := inferInstance
  have hm : Mono ((SheafOfModules.stalkFunctor X.ringCatSheaf (genericPoint X)).map u) :=
    (SheafOfModules.stalkFunctor X.ringCatSheaf (genericPoint X)).map_mono _
  have hinj : Function.Injective (PresheafOfModules.stalkMapₗ u.val (genericPoint X)) :=
    (AddCommGrpCat.mono_iff_injective _).1 hm
  exact LinearMap.finrank_le_finrank_of_injective hinj

end GenericRank

end AlgebraicGeometry.Scheme.Modules
