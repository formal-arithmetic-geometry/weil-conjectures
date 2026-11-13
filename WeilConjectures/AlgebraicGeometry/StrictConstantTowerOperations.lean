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
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-!
# Strict constant-coefficient tower operations

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.

## References

* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0F7C](https://stacks.math.columbia.edu/tag/0F7C)
* [Stacks Project, Tag 0F7D](https://stacks.math.columbia.edu/tag/0F7D)
* [Stacks Project, Tag 0F7F](https://stacks.math.columbia.edu/tag/0F7F)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 09AE](https://stacks.math.columbia.edu/tag/09AE)
* [Stacks Project, Tag 0H7J](https://stacks.math.columbia.edu/tag/0H7J)
* [Stacks Project, Tag 098K](https://stacks.math.columbia.edu/tag/098K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 05RU](https://stacks.math.columbia.edu/tag/05RU)
* [Stacks Project, Tag 03EK](https://stacks.math.columbia.edu/tag/03EK)
* [Stacks Project, Tag 03DA](https://stacks.math.columbia.edu/tag/03DA)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
* [Stacks Project, Tag 0DVC](https://stacks.math.columbia.edu/tag/0DVC)
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

/-- The existing constant-sheaf construction in the site's coefficient universe. -/
noncomputable abbrev coefficients (X : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of B)

/-- Modules over the actual constant ring sheaf. -/
abbrev Modules (X : Scheme.{u}) :=
  Scheme.proEtaleRingModules X ((coefficients B X))

/-- The module category is Grothendieck abelian at the site's original universes. -/
noncomputable instance modules_grothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Modules B X) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u,
      u + 1}
    (Scheme.ProEt.topology X) (coefficients B X)).1

/-- Strict inverse systems, with index `n` representing level `n+1`. -/
abbrev Towers (X : Scheme.{u}) := ℕᵒᵖ ⥤ Modules B X

/-- Standard unbounded localization of the strict tower category. -/
noncomputable instance towers_hasDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory (Towers B X) := HasDerivedCategory.standard _

/-- The ordinary unbounded derived category of strict towers. -/
abbrev Derived (X : Scheme.{u}) := DerivedCategory (Towers B X)

/-- Constant coefficients pull back canonically for arbitrary rings, including infinite ones. -/
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

/-- The canonical constant-ring identification, retaining its constant-section map. -/
noncomputable def constantRingIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      ((coefficients B Y)) ≅ (coefficients B X) :=
  @asIso _ _ _ _ (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B))
    (constantRing_isIso B f)

/-- Exact module inverse image through the canonical constant-ring identification. -/
noncomputable def modulePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Modules B Y ⥤ Modules B X :=
  Scheme.proEtaleRingModulePullback f ((coefficients B Y))
    ((coefficients B X)) (constantRingIso B f)

/-- Module direct image with the adjoint constant-ring map. -/
noncomputable def moduleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Modules B X ⥤ Modules B Y :=
  Scheme.proEtaleRingModuleDirectImage f ((coefficients B Y))
    ((coefficients B X)) (constantRingIso B f)

/-- The recorded module-operation instance, specialized to canonical constant coefficients. -/
noncomputable instance modulePullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (modulePullback B f).Additive :=
  (Scheme.proEtaleRingModuleOperations_properties f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).1

/-- The recorded module-operation instance, specialized to canonical constant coefficients. -/
noncomputable instance moduleDirectImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleDirectImage B f).Additive :=
  (Scheme.proEtaleRingModuleOperations_properties f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).2.1

/-- The recorded module-operation instance, specialized to canonical constant coefficients. -/
noncomputable instance modulePullback_finiteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (modulePullback B f) :=
  (Scheme.proEtaleRingModuleOperations_properties f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).2.2.1

/-- The recorded module-operation instance, specialized to canonical constant coefficients. -/
noncomputable instance modulePullback_finiteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (modulePullback B f) :=
  (Scheme.proEtaleRingModuleOperations_properties f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).2.2.2.1

/-- Termwise inverse image on strict towers. -/
noncomputable abbrev towerPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules B Y) (Modules B X)).obj (modulePullback B f)

/-- Termwise direct image on strict towers. -/
noncomputable abbrev towerDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules B X) (Modules B Y)).obj (moduleDirectImage B f)

/-- Tower complexes admit K-injective resolutions, without a uniform levelwise bound. -/
theorem towers_hasKInjectiveResolutions (X : Scheme.{u}) :
    CategoryTheory.Abelian.HasKInjectiveResolutions (Towers B X) := by
  let M := Modules B X
  let H := separator M
  have hH := isSeparator_separator M
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint M j).obj H) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hH.def
    intro a
    let ad := evaluationAdjunctionRight M j
    apply (ad.homEquiv H F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((ad.homEquiv H F).symm a)
    exact (ad.homEquiv_naturality_right_symm a f).trans
      (h.trans (ad.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (Towers B X) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{u + 1, u + 1} (Towers B X) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{u + 1, u + 1} (Towers B X) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : IsGrothendieckAbelian.{u + 1} (Towers B X) := {}
  infer_instance

/-- K-injective existence as an instance. -/
noncomputable instance towers_kInjective (X : Scheme.{u}) :
    CategoryTheory.Abelian.HasKInjectiveResolutions (Towers B X) :=
  towers_hasKInjectiveResolutions B X

/-- Termwise exactness uses the levelwise kernels and cokernels of strict diagrams. -/
theorem towerPullback_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (towerPullback B f) ∧
      PreservesFiniteColimits (towerPullback B f) := by
  constructor
  · exact ⟨fun _ _ _ ↦ inferInstance⟩
  · exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Left exactness on strict diagrams. -/
noncomputable instance towerPullback_finiteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (towerPullback B f) := (towerPullback_exact B f).1

/-- Right exactness on strict diagrams. -/
noncomputable instance towerPullback_finiteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (towerPullback B f) := (towerPullback_exact B f).2

/-- Exact inverse image on the unbounded derived strict-tower category. -/
noncomputable def G {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived B Y ⥤ Derived B X :=
  (towerPullback B f).mapDerivedCategory

/-- Total right derived termwise direct image. -/
noncomputable def R {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived B X ⥤ Derived B Y :=
  (towerDirectImage B f).rightDerivedFunctor

/-- The derived adjunction induced from the normalized sheaf adjunction, termwise. -/
noncomputable def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : G B f ⊣ R B f :=
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
    ((Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)).whiskerRight ℕᵒᵖ)

end AlgebraicGeometry.ProEtale.StrictTower
