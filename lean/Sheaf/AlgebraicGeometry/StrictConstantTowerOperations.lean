/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Sheaf.CategoryTheory.DiagramSiteRealization

import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.Limits
/-!
# Strict constant-coefficient tower operations

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: def-cbc-strict-constant-tower-operations).

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

variable (B : Type (u + 1)) [CommRing B]

/-- The existing constant-sheaf construction in the site's coefficient universe.
Source: Stacks, Tag 0H7J (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable abbrev coefficients (X : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of B)

/-- Modules over the actual constant ring sheaf. Source: Stacks, Tags 098K and 09AE
(blueprint: def-cbc-strict-constant-tower-operations). -/
abbrev Modules (X : Scheme.{u}) :=
  Scheme.proEtaleRingModules X ((coefficients B X))

/-- The module category is Grothendieck abelian at the site's original universes.
Source: Stacks, Tag 079P (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance modules_grothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Modules B X) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u,
      u + 1}
    (Scheme.ProEt.topology X) (coefficients B X)).1

/-- Strict inverse systems, with index `n` representing level `n+1`.
Source: blueprint strict-tower refinement of Tag 0F7B
(blueprint: def-cbc-strict-constant-tower-operations). -/
abbrev Towers (X : Scheme.{u}) := ℕᵒᵖ ⥤ Modules B X

/-- Standard unbounded localization of the strict tower category.
Source: Stacks, Tag 05RU (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance towers_hasDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory (Towers B X) := HasDerivedCategory.standard _

/-- The ordinary unbounded derived category of strict towers.
Source: Stacks, Tag 05RU (blueprint: def-cbc-strict-constant-tower-operations). -/
abbrev Derived (X : Scheme.{u}) := DerivedCategory (Towers B X)

/-- Constant coefficients pull back canonically for arbitrary rings, including infinite ones.
Source: Stacks, Tag 0H7J and the blueprint's first proof step
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: maps out of a constant sheaf are maps out of its constant presheaf. Compose
this universal property with the inverse-image adjunction. The resulting comparison
preserves constant sections and is inverse to the canonical constant-section map. -/
theorem constantRing_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B)) := by
  sorry

/-- The canonical constant-ring identification, retaining its constant-section map.
Source: Stacks, Tag 0H7J (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def constantRingIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      ((coefficients B Y)) ≅ (coefficients B X) :=
  @asIso _ _ _ _ (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B))
    (constantRing_isIso B f)

/-- Exact module inverse image through the canonical constant-ring identification.
Source: Stacks, Tag 03EK (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def modulePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Modules B Y ⥤ Modules B X :=
  Scheme.proEtaleRingModulePullback f ((coefficients B Y))
    ((coefficients B X)) (constantRingIso B f)

/-- Module direct image with the adjoint constant-ring map.
Source: Stacks, Tag 03DA (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def moduleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Modules B X ⥤ Modules B Y :=
  Scheme.proEtaleRingModuleDirectImage f ((coefficients B Y))
    ((coefficients B X)) (constantRingIso B f)

/-- The recorded module-operation instance, specialized to canonical constant coefficients.
Source: Stacks, Tag 03EK (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance modulePullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (modulePullback B f).Additive :=
  (Scheme.proEtaleRingModuleOperations_properties f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).1

/-- The recorded module-operation instance, specialized to canonical constant coefficients.
Source: Stacks, Tag 03EK (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance moduleDirectImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleDirectImage B f).Additive :=
  (Scheme.proEtaleRingModuleOperations_properties f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).2.1

/-- The recorded module-operation instance, specialized to canonical constant coefficients.
Source: Stacks, Tag 03EK (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance modulePullback_finiteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (modulePullback B f) :=
  (Scheme.proEtaleRingModuleOperations_properties f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).2.2.1

/-- The recorded module-operation instance, specialized to canonical constant coefficients.
Source: Stacks, Tag 03EK (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance modulePullback_finiteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (modulePullback B f) :=
  (Scheme.proEtaleRingModuleOperations_properties f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).2.2.2.1

/-- Termwise inverse image on strict towers.
Source: blueprint, first proof step (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable abbrev towerPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules B Y) (Modules B X)).obj (modulePullback B f)

/-- Termwise direct image on strict towers.
Source: blueprint, first proof step (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable abbrev towerDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules B X) (Modules B Y)).obj (moduleDirectImage B f)

/-- Tower complexes admit K-injective resolutions, without a uniform levelwise bound.
Source: blueprint, first proof step, diagram-site realization and Stacks, Tag 079P
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: transport to the small site model, use the diagram-site realization for ℕᵒᵖ,
apply K-injective existence for its module sheaves, and transport back. -/
theorem towers_hasKInjectiveResolutions (X : Scheme.{u}) :
    CategoryTheory.Abelian.HasKInjectiveResolutions (Towers B X) := by
  sorry

/-- K-injective existence as an instance. Source: Stacks, Tag 079P
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance towers_kInjective (X : Scheme.{u}) :
    CategoryTheory.Abelian.HasKInjectiveResolutions (Towers B X) :=
  towers_hasKInjectiveResolutions B X

/-- Termwise exactness uses the levelwise kernels and cokernels of strict diagrams.
Source: blueprint, first proof step (blueprint: def-cbc-strict-constant-tower-operations).
Proof: evaluate each finite limit and colimit at an index. The module inverse image
is exact, so the pointwise comparison is invertible. Evaluation jointly reflects
isomorphisms of strict diagrams, proving both claims. -/
theorem towerPullback_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (towerPullback B f) ∧
      PreservesFiniteColimits (towerPullback B f) := by
  sorry

/-- Left exactness on strict diagrams. Source: blueprint, first proof step
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance towerPullback_finiteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (towerPullback B f) := (towerPullback_exact B f).1

/-- Right exactness on strict diagrams. Source: blueprint, first proof step
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance towerPullback_finiteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (towerPullback B f) := (towerPullback_exact B f).2

/-- Exact inverse image on the unbounded derived strict-tower category.
Source: blueprint, first proof step (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def G {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived B Y ⥤ Derived B X :=
  (towerPullback B f).mapDerivedCategory

/-- Total right derived termwise direct image.
Source: blueprint, first proof step (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def R {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived B X ⥤ Derived B Y :=
  (towerDirectImage B f).rightDerivedFunctor

/-- The derived adjunction induced from the normalized sheaf adjunction, termwise.
Source: Stacks, Tag 0DVC (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : G B f ⊣ R B f :=
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
    ((Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)).whiskerRight ℕᵒᵖ)

/-- Evaluation of the derived strict tower, keeping its actual derived-category source.
Source: blueprint, evaluation clauses (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable abbrev ev (X : Scheme.{u}) (n : ℕ) :
    Derived B X ⥤ DerivedCategory (Modules B X) :=
  ((evaluation ℕᵒᵖ (Modules B X)).obj (op n)).mapDerivedCategory


/-- Compatibility of the canonical constant-section identifications with composition.
Source: Stacks, Tag 0H7J (blueprint: def-cbc-strict-constant-tower-operations).
Proof: transpose both maps under inverse image. On every constant scalar both maps
are the same constant section; the sheafification universal property gives equality. -/
theorem constantRingIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    constantRingIso B (f ≫ g) = Scheme.proEtaleRingCompositeCoefficients f g
      (coefficients B Z) (coefficients B Y) (coefficients B X)
      (constantRingIso B g) (constantRingIso B f) := by
  sorry

/-- Fibre-product pasting uniquely normalizes ordinary direct-image composition.
Source: Stacks, Tag 0D6D
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: evaluate both direct images on a test object. Restriction along the canonical
fibre-product pasting isomorphism gives the displayed map and its inverse. These are
linear by preservation of constant sections and natural by the universal property
of pullbacks. Equality on all sections proves uniqueness. -/
theorem moduleRComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! d : moduleDirectImage B f ⋙ moduleDirectImage B g ≅ moduleDirectImage B (f ≫ g),
      ∀ (N : Modules B X) (U : Z.ProEt)
        (m : ((moduleDirectImage B f ⋙ moduleDirectImage B g).obj N).val.obj (op U)),
        (d.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m := by
  sorry

/-- The section-normalized direct-image compositor. Source: Stacks, Tag 0D6D
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def moduleRComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleDirectImage B f ⋙ moduleDirectImage B g ≅ moduleDirectImage B (f ≫ g) :=
  Classical.choose (moduleRComp_existsUnique B f g)

/-- Pullback composition is the unit-preserving conjugate of fibre-product pasting.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def moduleGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback B (f ≫ g) ≅ modulePullback B g ⋙ modulePullback B f :=
  (Adjunction.leftAdjointCompIso
    (Scheme.proEtaleRingModuleAdjunction g (coefficients B Z)
      (coefficients B Y) (constantRingIso B g))
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f))
    (Scheme.proEtaleRingModuleAdjunction (f ≫ g) (coefficients B Z)
      (coefficients B X) (constantRingIso B (f ≫ g))) (moduleRComp B f g)).symm

/-- Strict tower pullback composition is the actual whiskered module comparison.
Source: Stacks, Tag 0D6D
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def towerGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    towerPullback B (f ≫ g) ≅ towerPullback B g ⋙ towerPullback B f :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (moduleGComp B f g)) ≪≫
    Functor.whiskeringRightObjCompIso (modulePullback B g) (modulePullback B f)

/-- The pullback compositor descends from the actual termwise module compositor.
Source: Stacks, Tag 0D6D (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def gComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G B (f ≫ g) ≅ G B g ⋙ G B f :=
  Functor.mapDerivedCategoryNatIso (towerGComp B f g) ≪≫
    Functor.mapDerivedCategoryCompIso (towerPullback B g) (towerPullback B f)

/-- The direct-image compositor is the conjugate for the composition adjunction.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def rComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R B f ⋙ R B g ≅ R B (f ≫ g) :=
  conjugateIsoEquiv ((adj B g).comp (adj B f)) (adj B (f ≫ g)) (gComp B f g)

/-- The identity direct image is the sectionwise pullback-identity comparison.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-constant-tower-operations).
Proof: the inverse base-change identity sends U to U ×_X X by its graph. Restrict
sections along this map. It preserves constant scalar sections, so is linear. Its
inverse is restriction along the inverse graph. Sections determine a unique map. -/
theorem moduleRId_existsUnique (X : Scheme.{u}) :
    ∃! e : moduleDirectImage B (𝟙 X) ≅ 𝟭 (Modules B X),
      ∀ (M : Modules B X) (U : X.ProEt)
        (m : ((moduleDirectImage B (𝟙 X)).obj M).val.obj (op U)),
        (e.hom.app M).val.app (op U) m =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U).op m := by
  sorry

/-- The section-normalized identity direct-image comparison.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def moduleRId (X : Scheme.{u}) :
    moduleDirectImage B (𝟙 X) ≅ 𝟭 (Modules B X) :=
  Classical.choose (moduleRId_existsUnique B X)

/-- The inverse-image identity is the normalized conjugate of the sectionwise identity.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def gId (X : Scheme.{u}) : G B (𝟙 X) ≅ 𝟭 (Derived B X) :=
  Functor.mapDerivedCategoryNatIso
    (((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
      (Adjunction.leftAdjointIdIso
        (Scheme.proEtaleRingModuleAdjunction (𝟙 X) (coefficients B X)
          (coefficients B X) (constantRingIso B (𝟙 X))) (moduleRId B X))) ≪≫
      Functor.whiskeringRightObjIdIso) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The normalized derived direct-image identity.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def rId (X : Scheme.{u}) : R B (𝟙 X) ≅ 𝟭 (Derived B X) :=
  (conjugateIsoEquiv Adjunction.id (adj B (𝟙 X)) (gId B X)).symm


/-- Evaluation commutes with strict termwise inverse image.
Source: blueprint evaluation normalization
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: both object maps evaluate the same strict tower at n and apply the same
module functor. Their maps are the same evaluated natural transformations. -/
theorem evaluationPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    towerPullback B f ⋙ (evaluation ℕᵒᵖ (Modules B X)).obj (op n) =
      (evaluation ℕᵒᵖ (Modules B Y)).obj (op n) ⋙ modulePullback B f := by
  sorry

/-- The evaluation/pullback comparison induced by the actual termwise equality.
Source: blueprint evaluation normalization
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def evalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    G B f ⋙ ev B X n ≅ ev B Y n ⋙ (modulePullback B f).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
  Functor.mapDerivedCategoryNatIso (eqToIso (evaluationPullback B f n)) ≪≫
  Functor.mapDerivedCategoryCompIso _ _

/-- The direct-image evaluation map is its specified adjunction mate.
Source: Stacks, Tags 07A7 and 0DVC
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def evalR {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    R B f ⋙ ev B Y n ⟶ ev B X n ⋙ (moduleDirectImage B f).rightDerivedFunctor :=
  mateEquiv (adj B f)
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)).mapDerivedCategoryRightDerivedAdjunction
    (evalG B f n).inv

/-- This normalized mate is invertible, without a uniform lower bound.
Source: blueprint evaluation proof step, and Stacks, Tag 08BJ
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: a K-injective strict tower evaluates to a K-injective complex: evaluation
has an exact left adjoint given by sums over the index arrows. On such a
representative both direct images give the identical evaluated complex.
The homotopy adjunction is termwise, so the derived Hom bijection identifies
this equality with the displayed mate, including its unit and counit. -/
theorem evalR_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (evalR B f n) := by
  sorry

end AlgebraicGeometry.ProEtale.StrictTower
