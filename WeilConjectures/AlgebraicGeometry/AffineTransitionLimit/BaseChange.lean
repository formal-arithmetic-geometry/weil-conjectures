/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Base change of a cofiltered limit of schemes

The base change of a cofiltered limit of schemes along a morphism to one of its stages is again a
limit (`AlgebraicGeometry.isLimitBaseChangeCone`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section BaseChangeLimit

/-!
### Base change of a cofiltered limit

A cofiltered limit `lim Dⱼ` of schemes stays a limit after base change along a morphism
`p : Y ⟶ Dᵢ` to one of the stages: `Y ×_{Dᵢ} lim Dⱼ` is the limit of the system
`{ Y ×_{Dᵢ} Dⱼ }_{j ≤ i}`. This is `AlgebraicGeometry.isLimitBaseChangeCone`; it is what
makes the results on cofiltered limits of schemes available for the descent of a scheme
over `lim Dⱼ` to a finite stage.
-/

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
variable {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) The base change `{ Y ×_{Dᵢ} Dⱼ }_{j ≤ i}` of the diagram `{ Dⱼ }` along a
morphism `p : Y ⟶ Dᵢ`. -/
@[simps] noncomputable def baseChangeDiagram : Over i ⥤ Scheme.{u} where
  obj j := pullback p (D.map j.hom)
  map {j k} f := pullback.map _ _ _ _ (𝟙 Y) (D.map f.left) (𝟙 _)
    (by simp) (by simp [← D.map_comp, Over.w f])
  map_id j := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) The projection from the base changed diagram to the original diagram. -/
@[simps] noncomputable def baseChangeDiagramπ :
    baseChangeDiagram D p ⟶ Over.forget i ⋙ D where
  app j := pullback.snd _ _

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) The cone with point `Y ×_{Dᵢ} lim Dⱼ` over the base changed diagram. -/
@[simps] noncomputable def baseChangeCone : Cone (baseChangeDiagram D p) where
  pt := pullback p (c.π.app i)
  π.app j := pullback.map _ _ _ _ (𝟙 Y) (c.π.app j.left) (𝟙 _) (by simp) (by simp)
  π.naturality {j k} f := by apply pullback.hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_fst {j k : Over i} (f : j ⟶ k) :
    (baseChangeDiagram D p).map f ≫ pullback.fst p (D.map k.hom) =
      pullback.fst p (D.map j.hom) := by
  simp [baseChangeDiagram]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_snd {j k : Over i} (f : j ⟶ k) :
    (baseChangeDiagram D p).map f ≫ pullback.snd p (D.map k.hom) =
      pullback.snd p (D.map j.hom) ≫ D.map f.left := by
  simp [baseChangeDiagram]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeCone_π_app_fst (j : Over i) :
    (baseChangeCone D c p).π.app j ≫ pullback.fst p (D.map j.hom) =
      pullback.fst p (c.π.app i) := by
  simp [baseChangeCone]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeCone_π_app_snd (j : Over i) :
    (baseChangeCone D c p).π.app j ≫ pullback.snd p (D.map j.hom) =
      pullback.snd p (c.π.app i) ≫ c.π.app j.left := by
  simp [baseChangeCone]

set_option backward.defeqAttrib.useBackward true in
lemma isPullback_baseChangeDiagram_map {j k : Over i} (f : j ⟶ k) :
    IsPullback ((baseChangeDiagram D p).map f) (pullback.snd p (D.map j.hom))
      (pullback.snd p (D.map k.hom)) (D.map f.left) :=
  isPullback_pullback_map _ _ _ _ (by rw [← D.map_comp, Over.w f])

set_option backward.defeqAttrib.useBackward true in
lemma isPullback_baseChangeCone_π (j : Over i) :
    IsPullback ((baseChangeCone D c p).π.app j) (pullback.snd p (c.π.app i))
      ((baseChangeDiagramπ D p).app j) (c.π.app j.left) :=
  isPullback_pullback_map _ _ _ _ (c.w j.hom)

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

include c in
/-- **Base change of a cofiltered limit of schemes.** If `lim Dⱼ` is a cofiltered limit and
`p : Y ⟶ Dᵢ`, then `Y ×_{Dᵢ} lim Dⱼ` is the limit of the system `{ Y ×_{Dᵢ} Dⱼ }_{j ≤ i}`. -/
noncomputable def isLimitBaseChangeCone [IsCofiltered I] (hc : IsLimit c) :
    IsLimit (baseChangeCone D c p) :=
  isLimitOfIsPullbackOfIsConnected (baseChangeDiagramπ D p) _ (c.whisker (Over.forget i))
    { hom := pullback.snd p (c.π.app i)
      w := fun j ↦ by simp }
    (isPullback_baseChangeCone_π D c p)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

instance [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((baseChangeDiagram D p).map f) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_baseChangeDiagram_map D p f).flip
    inferInstance

end BaseChangeLimit

end AlgebraicGeometry
