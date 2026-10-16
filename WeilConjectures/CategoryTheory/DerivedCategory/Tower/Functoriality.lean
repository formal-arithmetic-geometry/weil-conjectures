/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Formalism
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Levelwise functors on derived categories of towers

Let `A` and `B` be Grothendieck abelian categories and let `F ⊣ G` be an adjunction between
them with `F : A ⥤ B` exact (for instance the inverse image `g^*` and the direct image `g_*` of
sheaves along a morphism of sites). Applying `F` and `G` levelwise to towers gives an adjunction
`F^Tow ⊣ G^Tow` between `ℕᵒᵖ ⥤ A` and `ℕᵒᵖ ⥤ B`, with `F^Tow` exact. This file defines the
induced functors on the derived categories of towers,

* `DerivedCategory.towerUpper F : D(ℕᵒᵖ ⥤ A) ⥤ D(ℕᵒᵖ ⥤ B)`, induced by the exact `F^Tow`
  (`Lg^*_Tow` for `F = g^*`);
* `DerivedCategory.towerLower G : D(ℕᵒᵖ ⥤ B) ⥤ D(ℕᵒᵖ ⥤ A)`, the total right derived functor of
  `G^Tow` (`Rg_*^Tow` for `G = g_*`);

the derived adjunction `DerivedCategory.towerAdjunction adj : towerUpper F ⊣ towerLower G`, and
their compatibility with the derived evaluations `evₙ`
(`DerivedCategory.towerUpperCompTowerEvalIso`, `DerivedCategory.towerLowerCompTowerEvalIso`) and,
for the direct image, with the derived limit `R lim`
(`DerivedCategory.towerLowerCompRlimIso : Rg_*^Tow ⋙ R lim ≅ R lim ⋙ Rg_*`).
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Limits Opposite

namespace DerivedCategory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]

/-- The levelwise application `F^Tow` of a functor `F : A ⥤ B` to towers. -/
abbrev towerMap (F : A ⥤ B) : (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ B) :=
  (Functor.whiskeringRight ℕᵒᵖ A B).obj F

/-- Applying a functor levelwise commutes with the evaluation of towers. -/
def towerMapCompEvaluationIso (F : A ⥤ B) (n : ℕᵒᵖ) :
    towerMap F ⋙ (evaluation ℕᵒᵖ B).obj n ≅ (evaluation ℕᵒᵖ A).obj n ⋙ F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

section Upper

variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

instance : PreservesFiniteLimits (towerMap F) := ⟨fun _ _ _ ↦ inferInstance⟩

instance : PreservesFiniteColimits (towerMap F) := ⟨fun _ _ _ ↦ inferInstance⟩

/-- The functor `F^Tow : D(ℕᵒᵖ ⥤ A) ⥤ D(ℕᵒᵖ ⥤ B)` induced by an exact functor `F` applied
levelwise to towers (for `F = g^*` this is the levelwise inverse image `Lg^*_Tow` of
Blueprint `def-weil-pbc-completed-pullback`). -/
noncomputable def towerUpper : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B) :=
  (towerMap F).mapDerivedCategory

/-- The `n`-th derived evaluation of `F^Tow M` is `F` applied to the `n`-th derived evaluation
of `M`: `evₙ ∘ F^Tow ≅ F ∘ evₙ`. -/
noncomputable def towerUpperCompTowerEvalIso (n : ℕᵒᵖ) :
    towerUpper F ⋙ (towerEval B).obj n ≅ (towerEval A).obj n ⋙ F.mapDerivedCategory :=
  Functor.isoWhiskerLeft (towerUpper F)
      ((evaluation ℕᵒᵖ B).obj n).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (towerMapCompEvaluationIso F n) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      ((evaluation ℕᵒᵖ A).obj n).rightDerivedFunctorIsoMapDerivedCategory.symm
      F.mapDerivedCategory

end Upper

section Lower

variable (G : B ⥤ A) [G.Additive]

/-- The total right derived functor `R(G^Tow) : D(ℕᵒᵖ ⥤ B) ⥤ D(ℕᵒᵖ ⥤ A)` of a functor `G`
applied levelwise to towers (for `G = g_*` this is the levelwise direct image `Rg_*^Tow`). -/
noncomputable def towerLower : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory (ℕᵒᵖ ⥤ A) :=
  (towerMap G).rightDerivedFunctor

variable {F : A ⥤ B} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The derived adjunction `F^Tow ⊣ R(G^Tow)` on the derived categories of towers induced by an
adjunction `F ⊣ G` with `F` exact. -/
noncomputable def towerAdjunction (adj : F ⊣ G) : towerUpper F ⊣ towerLower G :=
  (adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction

/-- The levelwise application of a right adjoint of an exact functor preserves K-injective
complexes of towers. -/
lemma preservesKInjectiveComplexes_towerMap (adj : F ⊣ G) :
    (towerMap G).PreservesKInjectiveComplexes :=
  (adj.whiskerRight ℕᵒᵖ).preservesKInjectiveComplexes

/-- A right adjoint of an exact functor preserves K-injective complexes. -/
lemma preservesKInjectiveComplexes_of_adjunction (adj : F ⊣ G) :
    G.PreservesKInjectiveComplexes :=
  adj.preservesKInjectiveComplexes

/-- The `n`-th derived evaluation of `R(G^Tow) M` is `RG` applied to the `n`-th derived
evaluation of `M`: `evₙ ∘ R(G^Tow) ≅ RG ∘ evₙ`. -/
noncomputable def towerLowerCompTowerEvalIso (adj : F ⊣ G) (n : ℕᵒᵖ) :
    towerLower G ⋙ (towerEval A).obj n ≅ (towerEval B).obj n ⋙ G.rightDerivedFunctor :=
  have := preservesKInjectiveComplexes_towerMap G adj
  (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (towerMapCompEvaluationIso G n) ≪≫
    Functor.rightDerivedFunctorCompIso _ _

/-- Applying a functor preserving limits levelwise commutes with limits of towers. -/
noncomputable def towerMapCompLimIso [PreservesLimitsOfShape ℕᵒᵖ G] :
    towerMap G ⋙ (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ≅ lim ⋙ G :=
  (preservesLimitNatIso G).symm

instance : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).Additive where

/-- The limit functor on towers preserves K-injective complexes, being right adjoint to the
exact constant tower functor. -/
lemma preservesKInjectiveComplexes_lim :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).PreservesKInjectiveComplexes :=
  constLimAdj.preservesKInjectiveComplexes

/-- The derived limit commutes with the levelwise derived direct image:
`R lim ∘ R(G^Tow) ≅ RG ∘ R lim`, for `G` right adjoint to an exact functor. -/
noncomputable def towerLowerCompRlimIso (adj : F ⊣ G) :
    towerLower G ⋙ rlim A ≅ rlim B ⋙ G.rightDerivedFunctor :=
  have := preservesKInjectiveComplexes_towerMap G adj
  have := preservesKInjectiveComplexes_lim (A := B)
  have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
  (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (towerMapCompLimIso G) ≪≫
    Functor.rightDerivedFunctorCompIso _ _

end Lower

end DerivedCategory
