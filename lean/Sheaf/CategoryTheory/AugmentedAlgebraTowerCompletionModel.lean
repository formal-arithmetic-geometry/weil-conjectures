/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit

/-! # Augmented completion along an algebra tower

Source: Stacks Project, Tags 0940, 0941 and 06YT; first paragraph of
main-20261015/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md
(blueprint: def-sfb-augmented-algebra-tower-completion-model).

The universal comparison on K-flat representatives fixes the derived completion functor.
The augmentation is fixed using the ordinary compatible-family map followed by the
right-derived-limit comparison. Products of sheaves are not assumed exact.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.AugmentedTowerCompletion

variable {A : Type a} [Category.{b} A] [Abelian A]

/-- Transpose a strict tower of complexes, degree by degree.
Source: Stacks 0941 (blueprint: def-sfb-augmented-algebra-tower-completion-model). -/
def transpose : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  obj X :=
    { X i :=
        { obj n := (X.obj n).X i
          map f := (X.map f).f i
          map_id n := by simp
          map_comp f g := by simp }
      d i j := { app n := (X.obj n).d i j }
      shape i j h := NatTrans.ext (by funext n; exact (X.obj n).shape i j h)
      d_comp_d' i j k _ _ := NatTrans.ext (by funext n; exact (X.obj n).d_comp_d i j k) }
  map f :=
    { f i :=
        { app n := (f.app n).f i
          naturality n m g := congrArg (fun h ↦ h.f i) (f.naturality g) }
      comm' i j _ := NatTrans.ext (by funext n; exact (f.app n).comm i j) }

/-- An algebra tower, viewed as its underlying modules in degree zero.
Source: Stacks 06YT, 0941
(blueprint: def-sfb-augmented-algebra-tower-completion-model). -/
def algebraComplexes [MonoidalCategory A] [BraidedCategory A]
    (B : ℕᵒᵖ ⥤ CommMon A) : ℕᵒᵖ ⥤ CochainComplex A ℤ :=
  B ⋙ CommMon.forget A ⋙ HomologicalComplex.single A (.up ℤ) 0

/-- The compatible algebra units, as an augmentation of the degree-zero tower.
Source: Stacks 06YT, 0941
(blueprint: def-sfb-augmented-algebra-tower-completion-model). -/
def algebraAugmentation [MonoidalCategory A] [BraidedCategory A]
    (B : ℕᵒᵖ ⥤ CommMon A) :
    (Functor.const ℕᵒᵖ).obj ((HomologicalComplex.single A (.up ℤ) 0).obj (𝟙_ A)) ⟶
      algebraComplexes B where
  app n := (HomologicalComplex.single A (.up ℤ) 0).map (MonObj.one (X := (B.obj n).X))
  naturality n m f := by
    dsimp [algebraComplexes]
    rw [Category.id_comp, ← Functor.map_comp]
    congr 1
    exact (inferInstance : IsMonHom (B.map f).hom.hom).one_hom.symm

variable [MonoidalCategory (CochainComplex A ℤ)]

/-- The strict functor `P ↦ (P ⊗ X_n)_n`, with all transitions retained.
Source: Stacks 06YT, 0941
(blueprint: def-sfb-augmented-algebra-tower-completion-model). -/
def tensorTower (X : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    CochainComplex A ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ :=
  curriedTensor (CochainComplex A ℤ) ⋙
    (Functor.whiskeringLeft ℕᵒᵖ (CochainComplex A ℤ) (CochainComplex A ℤ)).obj X ⋙ transpose

variable [HasLimitsOfShape ℕᵒᵖ A]

/-- The ordinary termwise inverse-limit functor on strict complexes of towers.
Source: Stacks 0941 (blueprint: def-sfb-augmented-algebra-tower-completion-model). -/
def ordinaryLimit : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)

/-- The compatible-family map of a strict augmentation into the termwise limit.
Source: Stacks 0941 (blueprint: def-sfb-augmented-algebra-tower-completion-model). -/
def augmentationToLimit (X : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (α : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ X)
    (P : CochainComplex A ℤ) : P ⟶ (ordinaryLimit.obj ((tensorTower X).obj P)) where
  f i := limit.lift (((tensorTower X).obj P).X i)
    { pt := P.X i
      π :=
        { app n := ((ρ_ P).inv ≫ P ◁ α.app n).f i
          naturality n m g := by
            have h := α.naturality g
            dsimp at h
            have h' := congrArg (fun k ↦ ((ρ_ P).inv ≫ P ◁ k).f i) h
            simpa [tensorTower, transpose] using h' } }
  comm' i j _ := by
    apply limit.hom_ext
    intro n
    simp only [ordinaryLimit, Functor.mapHomologicalComplex_obj_d,
      Category.assoc, lim_map, limMap_π, limit.lift_π, limit.lift_π_assoc]
    exact ((ρ_ P).inv ≫ P ◁ α.app n).comm i j

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

/-- A universal right-derived inverse limit, with its K-injective computation.
These data are unique up to the unique comparison preserving the universal map.
Source: Stacks 0940, 0941
(blueprint: def-sfb-augmented-algebra-tower-completion-model). -/
structure DerivedLimit where
  /-- Total right derived inverse limit. -/
  F : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A
  /-- Ordinary-limit to derived-limit comparison. -/
  comparison : ordinaryLimit ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F
  /-- The universal property of total right derivation. -/
  universal : F.IsRightDerivedFunctor comparison (HomologicalComplex.quasiIso _ (.up ℤ))
  /-- K-injective towers compute the functor. -/
  computes : ∀ I, CochainComplex.IsKInjective I → IsIso (comparison.app I)

/-- A total derived limit with its normalized evaluation tower and Milnor cone.
Source: Stacks 0941
(blueprint: def-sfb-augmented-algebra-tower-completion-model). -/
structure RoosLimit extends DerivedLimit (A := A) where
  /-- Evaluation of an entire derived tower at every level. -/
  tower : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A)
  /-- Agreement with the localized strict evaluation tower. -/
  tower_comparison : DerivedCategory.Q ⋙ tower ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ) (DerivedCategory.{w} A)).obj
        DerivedCategory.Q
  /-- The cone of natural projections from the derived limit. -/
  cone : ∀ Z, Cone (tower.obj Z)
  /-- Its point is the specified total derived inverse limit. -/
  point : ∀ Z, (cone Z).pt = F.obj Z
  /-- The cone is the fibre of one minus the transition on the derived product. -/
  milnor : ∀ Z, Pretriangulated.IsHomotopyLimit (cone Z)

/-- An augmented completion model. The localization of the K-flat subcategory and
its comparison specify `N ↦ Rlim (N ⊗ X_n)`, including the actual augmentation.
Source: Stacks 06YT and 0941
(blueprint: def-sfb-augmented-algebra-tower-completion-model). -/
structure Model (K : ObjectProperty (CochainComplex A ℤ))
    (X : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (α : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ X)
    (L : DerivedLimit (A := A)) where
  /-- The completion endofunctor of the unbounded derived category. -/
  completion : DerivedCategory.{w} A ⥤ DerivedCategory.{w} A
  /-- Its K-flat computation, natural in all maps of K-flat complexes. -/
  comparison : K.ι ⋙ DerivedCategory.Q ⋙ completion ≅
    K.ι ⋙ tensorTower X ⋙ DerivedCategory.Q ⋙ L.F
  /-- The canonical completion map. -/
  unit : 𝟭 _ ⟶ completion
  /-- Normalization of the whole augmentation, before any projection from the limit. -/
  unit_computes : ∀ (P : K.FullSubcategory),
    unit.app (DerivedCategory.Q.obj P.obj) ≫ comparison.hom.app P =
      DerivedCategory.Q.map (augmentationToLimit X α P.obj) ≫
        L.comparison.app ((tensorTower X).obj P.obj)

/-- Identify completion with the ordinary limit of any K-injective tower resolution.
This is a composite of specified maps, not a choice of an isomorphism.
Source: Stacks 0941 (blueprint: def-sfb-augmented-algebra-tower-completion-model). -/
def Model.resolutionMap {K : ObjectProperty (CochainComplex A ℤ)}
    {X : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    {α : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ X}
    {L : DerivedLimit (A := A)} (B : Model K X α L)
    (P : K.FullSubcategory) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (i : (tensorTower X).obj P.obj ⟶ I) (hI : CochainComplex.IsKInjective I) :
    B.completion.obj (DerivedCategory.Q.obj P.obj) ⟶
      DerivedCategory.Q.obj (ordinaryLimit.obj I) :=
  B.comparison.hom.app P ≫ L.F.map (DerivedCategory.Q.map i) ≫
    @inv _ _ _ _ (L.comparison.app I) (L.computes I hI)

end CategoryTheory.AugmentedTowerCompletion
