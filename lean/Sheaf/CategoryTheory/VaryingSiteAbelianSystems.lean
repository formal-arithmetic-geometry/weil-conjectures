/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.CategoryTheory.TotalSiteSheafSystems
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits

/-! # Compatible abelian systems on a coherent diagram of sites

Source: Stacks Project, sites-cohomology.tex, Tag 0EXZ, systems in the statement;
spaces-simplicial.tex, Tag 09WF, compatible families
(blueprint: def-per-varying-site-abelian-systems).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory

namespace CategoryTheory.CoherentSitePseudofunctor

variable {I : Type u} [Category.{v} I]
  {F : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{w, w}} (D : CoherentSitePseudofunctor I F)

/-- Restrict the existing coefficient forgetful functor's filtered-colimit preservation
from the coefficient universe to the site universe. Source: Stacks 00W1
(blueprint: def-per-varying-site-abelian-systems). -/
instance abelianCoefficientForgetFiltered :
    PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{max v w}) :=
  preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max v w})

/-- Abelian sheaves, sized to admit the arrow-indexed products and sums.
Source: Stacks 0EXZ (blueprint: def-per-varying-site-abelian-systems). -/
abbrev abelianFibre (i : I) :=
  Sheaf (D.coverage i).toGrothendieck AddCommGrpCat.{max v w}

/-- The actual continuous direct image. Source: Stacks 00WW, 0EXZ
(blueprint: def-per-varying-site-abelian-systems). -/
def abelianDirect {i j : I} (a : i ⟶ j) : D.abelianFibre i ⥤ D.abelianFibre j :=
  letI := D.continuous a
  (F.map a.op.toLoc).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{max v w}
    (D.coverage j).toGrothendieck (D.coverage i).toGrothendieck

/-- Sheafified left Kan extension, rather than a chosen abstract left adjoint.
Source: Stacks 00WX, 0EXZ (blueprint: def-per-varying-site-abelian-systems). -/
def abelianInverse {i j : I} (a : i ⟶ j) : D.abelianFibre j ⥤ D.abelianFibre i :=
  letI := D.continuous a
  Functor.sheafPullbackConstruction.sheafPullback (F.map a.op.toLoc).toFunctor
    AddCommGrpCat.{max v w} (D.coverage j).toGrothendieck (D.coverage i).toGrothendieck

/-- The sheafified-Kan-extension adjunction. Source: Stacks 00WX, 0EXZ
(blueprint: def-per-varying-site-abelian-systems). -/
def abelianAdjunction {i j : I} (a : i ⟶ j) :
    D.abelianInverse a ⊣ D.abelianDirect a :=
  letI := D.continuous a
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (F.map a.op.toLoc).toFunctor AddCommGrpCat.{max v w}
    (D.coverage j).toGrothendieck (D.coverage i).toGrothendieck

/-- Direct-image identity comparison induced by the given site unitor.
Source: Stacks 03CB, 09WF (blueprint: def-per-varying-site-abelian-systems). -/
def abelianDirectId (i : I) : D.abelianDirect (𝟙 i) ≅ 𝟭 _ :=
  letI : Functor.IsContinuous (F.map (𝟙 ⟨op i⟩)).toFunctor
      (D.coverage i).toGrothendieck (D.coverage i).toGrothendieck := D.continuous (𝟙 i)
  Functor.sheafPushforwardContinuousId' (Cat.Hom.toNatIso (F.mapId ⟨op i⟩))
    AddCommGrpCat.{max v w} (D.coverage i).toGrothendieck

/-- Direct-image composition comparison induced by the site compositor.
Source: Stacks 03CB, 09WF (blueprint: def-per-varying-site-abelian-systems). -/
def abelianDirectComp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    D.abelianDirect a ⋙ D.abelianDirect b ≅ D.abelianDirect (a ≫ b) :=
  letI := D.continuous a
  letI := D.continuous b
  letI : Functor.IsContinuous (F.map (b.op.toLoc ≫ a.op.toLoc)).toFunctor
      (D.coverage k).toGrothendieck (D.coverage i).toGrothendieck := D.continuous (a ≫ b)
  Functor.sheafPushforwardContinuousComp'
    (Cat.Hom.toNatIso (F.mapComp b.op.toLoc a.op.toLoc).symm)
    AddCommGrpCat.{max v w} (D.coverage k).toGrothendieck
    (D.coverage j).toGrothendieck (D.coverage i).toGrothendieck

/-- The canonical mate unitor. Source: Stacks 03CB, 09WF
(blueprint: def-per-varying-site-abelian-systems). -/
def abelianInverseId (i : I) : D.abelianInverse (𝟙 i) ≅ 𝟭 _ :=
  Adjunction.leftAdjointIdIso (D.abelianAdjunction (𝟙 i)) (D.abelianDirectId i)

/-- The canonical mate compositor. Source: Stacks 03CB, 09WF
(blueprint: def-per-varying-site-abelian-systems). -/
def abelianInverseComp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    D.abelianInverse b ⋙ D.abelianInverse a ≅ D.abelianInverse (a ≫ b) :=
  Adjunction.leftAdjointCompIso (D.abelianAdjunction b) (D.abelianAdjunction a)
    (D.abelianAdjunction (a ≫ b)) (D.abelianDirectComp a b)

/-- All compatible abelian families, with no invertibility condition on transitions.
Source: Stacks 0EXZ, 09WF (blueprint: def-per-varying-site-abelian-systems). -/
structure AbelianSystem where
  obj : ∀ i : I, D.abelianFibre i
  transition : ∀ {i j : I} (a : i ⟶ j), (D.abelianInverse a).obj (obj j) ⟶ obj i
  transition_id : ∀ i : I, transition (𝟙 i) = (D.abelianInverseId i).hom.app (obj i)
  transition_comp : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k),
    (D.abelianInverseComp a b).hom.app (obj k) ≫ transition (a ≫ b) =
      (D.abelianInverse a).map (transition b) ≫ transition a

variable [∀ (i j : I) (a : i ⟶ j), (D.abelianInverse a).Additive]

/-- Compatible maps form a subgroup of the component Hom groups.
Source: Stacks 0EXZ, 09WF (blueprint: def-per-varying-site-abelian-systems). -/
def abelianSystemHom (X Y : D.AbelianSystem) :
    AddSubgroup (∀ i : I, X.obj i ⟶ Y.obj i) where
  carrier := {h | ∀ {i j : I} (a : i ⟶ j),
    (D.abelianInverse a).map (h j) ≫ Y.transition a = X.transition a ≫ h i}
  zero_mem' := by simp
  add_mem' := by
    intro h k hh hk i j a
    simp only [Pi.add_apply, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
    rw [hh a, hk a]
  neg_mem' := by
    intro h hh i j a
    simp only [Pi.neg_apply, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]
    rw [hh a]

/-- The category of systems has precisely the compatible component morphisms.
Source: Stacks 0EXZ, 09WF (blueprint: def-per-varying-site-abelian-systems). -/
instance abelianSystemCategory : Category D.AbelianSystem where
  Hom X Y := D.abelianSystemHom X Y
  id X := ⟨fun i => 𝟙 (X.obj i), by
    intro i j a
    simp only [Functor.map_id, Category.id_comp, Category.comp_id]⟩
  comp h k := ⟨fun i => h.val i ≫ k.val i, by
    intro i j a
    simp only [Functor.map_comp, Category.assoc]
    rw [k.property a, ← Category.assoc, h.property a, Category.assoc]⟩
  id_comp h := Subtype.ext (funext (fun i => Category.id_comp (h.val i)))
  comp_id h := Subtype.ext (funext (fun i => Category.comp_id (h.val i)))
  assoc h k l := Subtype.ext (funext (fun i => Category.assoc (h.val i) (k.val i) (l.val i)))

/-- Addition and composition are componentwise.
Source: Stacks 0EXZ, 09WF (blueprint: def-per-varying-site-abelian-systems). -/
instance abelianSystemPreadditive : Preadditive D.AbelianSystem where
  homGroup X Y := (D.abelianSystemHom X Y).toAddCommGroup
  add_comp _X _Y _Z h k l :=
    Subtype.ext (funext (fun i => Preadditive.add_comp _ _ _ (h.val i) (k.val i) (l.val i)))
  comp_add _X _Y _Z h k l :=
    Subtype.ext (funext (fun i => Preadditive.comp_add _ _ _ (h.val i) (k.val i) (l.val i)))

/-- Evaluation at a fibre, on objects and on compatible maps.
Source: Stacks 0EXZ, 09WG (blueprint: def-per-varying-site-abelian-systems). -/
def abelianEvaluation (i : I) : D.AbelianSystem ⥤ D.abelianFibre i where
  obj X := X.obj i
  map h := h.val i

/-- Evaluation is additive by its component formula.
Source: Stacks 0EXZ, 09WG (blueprint: def-per-varying-site-abelian-systems). -/
instance abelianEvaluationAdditive (i : I) : (D.abelianEvaluation i).Additive where
  map_add := rfl

end CategoryTheory.CoherentSitePseudofunctor
