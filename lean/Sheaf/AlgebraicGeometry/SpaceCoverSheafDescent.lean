/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Algebraic-space descent data and locally algebraic sheaves

Source: Stacks Project, Spaces, Descent, Tag 0ADT, the two categories and the functor
from sheaves to descent data (blueprint: def-sfb-space-cover-sheaf-descent-categories).

Transitions are expressed as natural transport on generalized points of sheaves. Yoneda
identifies this with overlap isomorphisms over `Xᵢ ×_X Xⱼ`. Identity and cocycle imply
invertibility: transport in the reverse direction is the inverse. This avoids choosing
atlases, overlap models, or a global algebraic-space realization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Family descent data: algebraic local sheaves over the covering spaces and natural
transport between their fibres, with the identity and triple-overlap cocycle.
Source: Stacks, Tag 0ADT (blueprint: def-sfb-space-cover-sheaf-descent-categories).
For universal generalized points the transport is the overlap isomorphism. Naturality
recovers every other transport from it; reverse transport is inverse by the cocycle.
Thus the identity law is a consequence of the invertible cocycle, not extra data. -/
structure SpaceCoverSheafDescent {S : Scheme.{u}} {I : Type w}
    {X : AlgebraicSpace S} {Xᵢ : I → AlgebraicSpace S} (a : ∀ i, Xᵢ i ⟶ X) where
  /-- The sheaves `Vᵢ → Xᵢ`. -/
  localObject : ∀ i, Over (Xᵢ i).obj
  /-- Each local sheaf is an algebraic space. -/
  local_algebraic : ∀ i, IsAlgebraicSpace (localObject i).left
  /-- Transport along two points with the same image in `X`. -/
  transport {T : Sheaf (Scheme.fppfTopology.over S) (Type u)} {i j : I}
    (x : T ⟶ (Xᵢ i).obj) (y : T ⟶ (Xᵢ j).obj) (h : x ≫ (a i).hom = y ≫ (a j).hom) :
    (Over.mk x ⟶ localObject i) → (Over.mk y ⟶ localObject j)
  /-- Transport commutes with every change of generalized test point. -/
  naturality {T T' : Sheaf (Scheme.fppfTopology.over S) (Type u)} (g : T' ⟶ T)
    {i j : I} (x : T ⟶ (Xᵢ i).obj) (y : T ⟶ (Xᵢ j).obj)
    (h : x ≫ (a i).hom = y ≫ (a j).hom) (v : Over.mk x ⟶ localObject i) :
    transport (g ≫ x) (g ≫ y) (by simp only [Category.assoc]; rw [h])
        ((Over.homMk g rfl : Over.mk (g ≫ x) ⟶ Over.mk x) ≫ v) =
      (Over.homMk g rfl : Over.mk (g ≫ y) ⟶ Over.mk y) ≫ transport x y h v
  /-- Transport at the same point is the identity. -/
  self {T : Sheaf (Scheme.fppfTopology.over S) (Type u)} {i : I}
    (x : T ⟶ (Xᵢ i).obj) (v : Over.mk x ⟶ localObject i) : transport x x rfl v = v
  /-- The triple-overlap cocycle. -/
  cocycle {T : Sheaf (Scheme.fppfTopology.over S) (Type u)} {i j k : I}
    (x : T ⟶ (Xᵢ i).obj) (y : T ⟶ (Xᵢ j).obj) (z : T ⟶ (Xᵢ k).obj)
    (h : x ≫ (a i).hom = y ≫ (a j).hom) (h' : y ≫ (a j).hom = z ≫ (a k).hom)
    (v : Over.mk x ⟶ localObject i) :
    transport y z h' (transport x y h v) = transport x z (h.trans h') v

namespace SpaceCoverSheafDescent

variable {S : Scheme.{u}} {I : Type w} {X : AlgebraicSpace S}
  {Xᵢ : I → AlgebraicSpace S} {a : ∀ i, Xᵢ i ⟶ X}

/-- Compatible local maps over the `Xᵢ`; these are precisely morphisms of descent data.
Source: Stacks, Tag 0ADT (blueprint: def-sfb-space-cover-sheaf-descent-categories). -/
@[ext]
structure Hom (D E : SpaceCoverSheafDescent a) where
  /-- The local morphisms over the covering members. -/
  map : ∀ i, D.localObject i ⟶ E.localObject i
  /-- Compatibility with all overlap maps, expressed on generalized points. -/
  comm {T : Sheaf (Scheme.fppfTopology.over S) (Type u)} {i j : I}
    (x : T ⟶ (Xᵢ i).obj) (y : T ⟶ (Xᵢ j).obj)
    (h : x ≫ (a i).hom = y ≫ (a j).hom) (v : Over.mk x ⟶ D.localObject i) :
    D.transport x y h v ≫ map j = E.transport x y h (v ≫ map i)

/-- Componentwise identities and composition give the descent category.
Source: Stacks, Tag 0ADT (blueprint: def-sfb-space-cover-sheaf-descent-categories). -/
instance : Category (SpaceCoverSheafDescent a) where
  Hom := Hom
  id D := { map := fun i ↦ 𝟙 (D.localObject i), comm := by intros; simp }
  comp f g :=
    { map := fun i ↦ f.map i ≫ g.map i
      comm := by
        intros
        rw [← Category.assoc, f.comm, g.comm, Category.assoc] }
  id_comp f := Hom.ext (funext (fun i ↦ Category.id_comp (f.map i)))
  comp_id f := Hom.ext (funext (fun i ↦ Category.comp_id (f.map i)))
  assoc f g h := Hom.ext (funext (fun i ↦ Category.assoc (f.map i) (g.map i) (h.map i)))

end SpaceCoverSheafDescent

/-- Sheaves over `X` whose pullbacks to every `Xᵢ` are algebraic spaces. No algebraicity
of the global sheaf is required.
Source: Stacks, Tag 0ADT (blueprint: def-sfb-space-cover-sheaf-descent-categories). -/
def IsLocallyAlgebraicSpaceSheaf {S : Scheme.{u}} {I : Type w}
    {X : AlgebraicSpace S} {Xᵢ : I → AlgebraicSpace S} (a : ∀ i, Xᵢ i ⟶ X) :
    ObjectProperty (Over X.obj) :=
  fun F ↦ ∀ i, IsAlgebraicSpace (((Over.pullback (a i).hom).obj F).left)

/-- The canonical overlap transport on a sheaf pullback keeps the global-sheaf coordinate
and replaces the covering-space coordinate.
Source: Stacks, Tag 0ADT (blueprint: def-sfb-space-cover-sheaf-descent-categories). -/
def spaceCoverPullbackTransport {S : Scheme.{u}} {I : Type w}
    {X : AlgebraicSpace S} {Xᵢ : I → AlgebraicSpace S} (a : ∀ i, Xᵢ i ⟶ X)
    (F : Over X.obj) {T : Sheaf (Scheme.fppfTopology.over S) (Type u)} {i j : I}
    (x : T ⟶ (Xᵢ i).obj) (y : T ⟶ (Xᵢ j).obj)
    (h : x ≫ (a i).hom = y ≫ (a j).hom)
    (v : Over.mk x ⟶ (Over.pullback (a i).hom).obj F) :
    Over.mk y ⟶ (Over.pullback (a j).hom).obj F :=
  Over.homMk
    (pullback.lift (v.left ≫ pullback.fst F.hom (a i).hom) y (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (fun z ↦ z ≫ (a i).hom) (Over.w v) |>.trans h))
    (by simp [Over.pullback])

/-- The actual pullback functor to descent data. Objects are `F ×_X Xᵢ`, transitions keep
`F` fixed, and morphisms are pullbacks of the given map over `X`.
Source: Stacks, Tag 0ADT (blueprint: def-sfb-space-cover-sheaf-descent-categories). -/
def spaceCoverSheafRestriction {S : Scheme.{u}} {I : Type w}
    {X : AlgebraicSpace S} {Xᵢ : I → AlgebraicSpace S} (a : ∀ i, Xᵢ i ⟶ X) :
    (IsLocallyAlgebraicSpaceSheaf a).FullSubcategory ⥤ SpaceCoverSheafDescent a where
  obj F :=
    { localObject := fun i ↦ (Over.pullback (a i).hom).obj F.obj
      local_algebraic := F.property
      transport := spaceCoverPullbackTransport a F.obj
      naturality := by
        intros
        apply Over.OverMorphism.ext
        apply pullback.hom_ext <;>
          simp [spaceCoverPullbackTransport, Category.assoc]
      self := by
        intro T i x v
        apply Over.OverMorphism.ext
        apply pullback.hom_ext
        · simp [spaceCoverPullbackTransport]
        · simpa [spaceCoverPullbackTransport] using (Over.w v).symm
      cocycle := by
        intros
        apply Over.OverMorphism.ext
        apply pullback.hom_ext <;>
          simp [spaceCoverPullbackTransport] }
  map f :=
    { map := fun i ↦ (Over.pullback (a i).hom).map f.hom
      comm := by
        intros
        apply Over.OverMorphism.ext
        apply pullback.hom_ext <;>
          simp [spaceCoverPullbackTransport, Over.pullback, Category.assoc] }
  map_id F := SpaceCoverSheafDescent.Hom.ext
    (funext (fun i ↦ (Over.pullback (a i).hom).map_id F.obj))
  map_comp f g := SpaceCoverSheafDescent.Hom.ext
    (funext (fun i ↦ (Over.pullback (a i).hom).map_comp f.hom g.hom))

end AlgebraicGeometry.AlgebraicSpace
