/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Canonical constructible module Hom comparison data

The tail `I_{≥ i₀}` of a directed index, the actual inverse-image Hom types
`Hom(f_{ii₀}⁻¹F₀, f_{ii₀}⁻¹G₀)` with their transition maps, the canonical map to
`Hom(f_{i₀}⁻¹F₀, f_{i₀}⁻¹G₀)` on the limit (conjugation by `Etale.upperStarComp`), and
the elementwise filtered criterion saying that this canonical comparison is a bijection.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully faithful
paragraphs (blueprint: def-weil-pbc-constructible-module-hom-data).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry

/-- The full subcategory of indices at or above the chosen stage.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully faithful
paragraphs (blueprint: def-weil-pbc-constructible-module-hom-data). -/
def ConstructibleModuleColimitAbove (I : Type u) [Preorder I] (i₀ : I) := Set.Ici i₀

/-- The induced thin category structure on the tail.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully faithful
paragraphs (blueprint: def-weil-pbc-constructible-module-hom-data). -/
instance (I : Type u) [Preorder I] (i₀ : I) : Category (ConstructibleModuleColimitAbove I i₀) :=
  inferInstance

/-- The inclusion of the tail into the original preorder.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully faithful
paragraphs (blueprint: def-weil-pbc-constructible-module-hom-data). -/
def ConstructibleModuleColimitAbove.inclusion
    {I : Type u} [Preorder I] (i₀ : I) :
    ConstructibleModuleColimitAbove I i₀ ⥤ I where
  obj i := i.1
  map f := f

/-- The inverse-system diagram restricted to the tail.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully faithful
paragraphs (blueprint: def-weil-pbc-constructible-module-hom-data). -/
def ConstructibleModuleColimitAbove.diagram
    {I : Type u} [Preorder I] (i₀ : I) (D : Iᵒᵖ ⥤ Scheme.{u}) :
    (ConstructibleModuleColimitAbove I i₀)ᵒᵖ ⥤ Scheme.{u} :=
  (ConstructibleModuleColimitAbove.inclusion i₀).op ⋙ D

/-- The actual transition morphism `f_{ii₀}` from a tail stage to the chosen stage.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully faithful
paragraphs (blueprint: def-weil-pbc-constructible-module-hom-data). -/
def ConstructibleModuleColimitStageMap
    {I : Type u} [Preorder I] (i₀ : I) (D : Iᵒᵖ ⥤ Scheme.{u})
    (i : ConstructibleModuleColimitAbove I i₀) : D.obj (op i.1) ⟶ D.obj (op i₀) :=
  D.map (homOfLE i.2).op

/-- The Hom type between the two actual inverse images at a tail stage.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully faithful
paragraphs (blueprint: def-weil-pbc-constructible-module-hom-data). -/
abbrev ConstructibleModuleColimitHomType
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (i₀ : I) (A : Type (u + 1)) [CommRing A]
    (F₀ G₀ : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A))
    (i : ConstructibleModuleColimitAbove I i₀) : Type (u + 1) :=
  (Etale.upperStar (ModuleCat.{u + 1} A)
    (ConstructibleModuleColimitStageMap i₀ D i)).obj F₀ ⟶
    (Etale.upperStar (ModuleCat.{u + 1} A)
      (ConstructibleModuleColimitStageMap i₀ D i)).obj G₀

/-- The actual inverse-image transition map on stage Hom types.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully faithful
paragraphs (blueprint: def-weil-pbc-constructible-module-hom-data). -/
noncomputable def ConstructibleModuleColimitHomMap
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (i₀ : I) (A : Type (u + 1)) [CommRing A]
    (F₀ G₀ : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A))
    {i j : ConstructibleModuleColimitAbove I i₀} (f : i ⟶ j) :
    ConstructibleModuleColimitHomType D i₀ A F₀ G₀ i →
      ConstructibleModuleColimitHomType D i₀ A F₀ G₀ j := fun φ =>
  let hi := ConstructibleModuleColimitStageMap i₀ D i
  let hj := ConstructibleModuleColimitStageMap i₀ D j
  let hij : i.1 ≤ j.1 := f.down.down
  let h := D.map (homOfLE hij).op
  let hcomp : hj = h ≫ hi := by
    dsimp [hi, hj, h, ConstructibleModuleColimitStageMap]
    rw [← D.map_comp]
    congr 1
  let e := Etale.upperStarComp (ModuleCat.{u + 1} A) h hi hj hcomp
  e.hom.app F₀ ≫ (Etale.upperStar (ModuleCat.{u + 1} A) h).map φ ≫ e.inv.app G₀

/-- The canonical map from a stage Hom to the Hom at the limit, conjugated by
`upperStarComp`.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully faithful
paragraphs (blueprint: def-weil-pbc-constructible-module-hom-data). -/
noncomputable def ConstructibleModuleColimitCanonicalMap
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D) (i₀ : I) (A : Type (u + 1)) [CommRing A]
    (F₀ G₀ : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A))
    (i : ConstructibleModuleColimitAbove I i₀) :
    ConstructibleModuleColimitHomType D i₀ A F₀ G₀ i →
      ((Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))).obj F₀ ⟶
        (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))).obj G₀) := fun φ =>
  let hi := ConstructibleModuleColimitStageMap i₀ D i
  let pi := c.π.app (op i.1)
  let p₀ := c.π.app (op i₀)
  let hcomp : p₀ = pi ≫ hi := by
    change c.π.app (op i₀) = c.π.app (op i.1) ≫ D.map (homOfLE i.2).op
    simp
  let e := Etale.upperStarComp (ModuleCat.{u + 1} A) pi hi p₀ hcomp
  e.hom.app F₀ ≫ (Etale.upperStar (ModuleCat.{u + 1} A) pi).map φ ≫ e.inv.app G₀

/-- The elementwise filtered criterion for the canonical Hom comparison: surjectivity,
equality detected at a later stage, eventual vanishing, and finite families verified at
one common later stage.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully faithful
paragraphs (blueprint: def-weil-pbc-constructible-module-hom-data). -/
def ConstructibleModuleColimitCanonicalComparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F₀ G₀ : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A))
    : Prop :=
  (∀ ψ : ((Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))).obj F₀ ⟶
      (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))).obj G₀),
    ∃ i φ, ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ i φ = ψ) ∧
  (∀ (i j : ConstructibleModuleColimitAbove I i₀)
      (φ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ i)
      (ψ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ j),
    ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ i φ =
      ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ j ψ →
    ∃ (k : ConstructibleModuleColimitAbove I i₀) (f : i ⟶ k) (g : j ⟶ k),
      ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ f φ =
        ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ g ψ) ∧
  (∀ (i : ConstructibleModuleColimitAbove I i₀)
      (φ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ i),
    ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ i φ = 0 →
    ∃ (j : ConstructibleModuleColimitAbove I i₀) (f : i ⟶ j),
      ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ f φ = 0) ∧
  (∀ (n : ℕ) (i : Fin n → ConstructibleModuleColimitAbove I i₀)
      (φ : ∀ a, ConstructibleModuleColimitHomType D i₀ A F₀ G₀ (i a))
      (R : Fin n → Fin n → Prop),
    (∀ a b, R a b →
      ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ (i a) (φ a) =
        ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ (i b) (φ b)) →
    ∃ (k : ConstructibleModuleColimitAbove I i₀) (f : ∀ a, i a ⟶ k),
      ∀ a b, R a b →
        ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ (f a) (φ a) =
          ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ (f b) (φ b))

end AlgebraicGeometry
