/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Strict constant-coefficient tower operations

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (auxiliary; not a blueprint node).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

-- These elementary factorization calculations follow the proved helpers of
-- ProEtaleRingSheafChangeAdjunction, without importing its unrelated comparisons.
variable (B : Type (u + 1)) [CommRing B]

/-- The existing constant-sheaf construction in the site's coefficient universe.
Source: Stacks, Tag 0H7J (auxiliary; not a blueprint node). -/
noncomputable abbrev coefficients (X : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of B)

/-- Constant coefficients pull back canonically for arbitrary rings, including infinite ones.
Source: Stacks, Tag 0H7J and the blueprint's first proof step
(auxiliary; not a blueprint node).
Proof: maps out of a constant sheaf are maps out of its constant presheaf. Compose
this universal property with the inverse-image adjunction. The resulting comparison
preserves constant sections and is inverse to the canonical constant-section map. -/
theorem constantRing_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B)) := by
  let A := CommRingCat.of B
  let T := ⊤_ Y.ProEt
  let hT := terminalIsTerminal (C := Y.ProEt)
  let hGT := hT.isTerminalObj (Scheme.proEtaleBaseChange f)
  let adjY := constantSheafAdj (Scheme.ProEt.topology Y) CommRingCat.{u + 1} hT
  let adjX := constantSheafAdj (Scheme.ProEt.topology X) CommRingCat.{u + 1} hGT
  let adj := (adjY.comp (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1})).ofNatIsoRight
    ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuousCompSheafSectionsObjIso
      CommRingCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) (op T))
  have he : Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A =
      (adj.leftAdjointUniq adjX).hom.app A := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change (adjY.comp (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1})).homEquiv _ _
      (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change adjY.homEquiv _ _
      ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
        (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
          (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A))) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj CommRingCat.{u + 1} hT).comp
      (sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1})).homEquiv _ _
        (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{u + 1} hT).homEquiv _ _
      ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv _ _
        (((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    change 𝟙 A ≫ _ = _
    rw [Category.id_comp]
    rfl
  rw [he]
  infer_instance

/-- The canonical constant-ring identification, retaining its constant-section map.
Source: Stacks, Tag 0H7J (auxiliary; not a blueprint node). -/
noncomputable def constantRingIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      ((coefficients B Y)) ≅ (coefficients B X) :=
  @asIso _ _ _ _ (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B))
    (constantRing_isIso B f)

/-- The derived adjunction induced from the normalized sheaf adjunction, termwise.
Source: Stacks, Tag 0DVC (auxiliary; not a blueprint node). -/
noncomputable def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : G B f ⊣ R B f :=
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
    ((Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)).whiskerRight ℕᵒᵖ)

end AlgebraicGeometry.ProEtale.StrictTower
