/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
public import Mathlib.CategoryTheory.Core

/-! # Rigidified line modules on algebraic spaces

Source: Deligne, Le lemme de Gabber, Section 4.2, printed p.142; Stacks, Tags 03D7,
03G8 (blueprint: def-sfb-rigidified-space-lines).

Tensor inverse image and its tensor-normalized composition comparison are the existing
algebraic-space constructions. Rigidification is an actual isomorphism with the unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B X B' X' : AlgebraicSpace S}

/-- Tensor inverse image of the structure module has its unique multiplication
identification. Source: Stacks, Tags 03D7 and 03G8
(blueprint: def-sfb-rigidified-space-lines).
Proof: on each chart, send b tensor r to b f-sharp(r). Balancing makes this linear;
the inverse sends b to b tensor 1. These maps glue, commute with restriction, and
are natural. Local pure tensors generate the pullback, which proves uniqueness. -/
theorem rigidifiedUnitIso_existsUnique (f : X ⟶ B) :
    ∃! c : (moduleTensorPullback f).obj (SheafOfModules.unit B.structureSheaf) ≅
        SheafOfModules.unit X.structureSheaf,
      ∀ (V : B.EtaleSite) (q : ModuleChart f V)
        (b : X.structureSheaf.obj.obj (op q.left))
        (r : B.structureSheaf.obj.obj (op V)),
        c.hom.val.app (op q.left)
            (moduleTensorSection f (SheafOfModules.unit B.structureSheaf) V q b r) =
          b * moduleChartScalar f V q r := by
  sorry

/-- The unit comparison fixed by multiplication on local tensors.
Source: Stacks, Tag 03D7 (blueprint: def-sfb-rigidified-space-lines). -/
def rigidifiedUnitIso (f : X ⟶ B) :
    (moduleTensorPullback f).obj (SheafOfModules.unit B.structureSheaf) ≅
      SheafOfModules.unit X.structureSheaf :=
  (rigidifiedUnitIso_existsUnique f).choose

/-- The comma category of modules with a map from their identity pullback to the unit.
Source: Deligne 4.2 (blueprint: def-sfb-rigidified-space-lines). -/
abbrev RigidifiedModule (e : B ⟶ X) :=
  CostructuredArrow (moduleTensorPullback e) (SheafOfModules.unit B.structureSheaf)

/-- A rigidified line has a line as underlying module and an invertible rigidification.
Source: Deligne 4.2 (blueprint: def-sfb-rigidified-space-lines). -/
def IsRigidifiedLine (e : B ⟶ X) (L : RigidifiedModule e) : Prop :=
  X.IsLineModule L.left ∧ IsIso L.hom

/-- The groupoid of rigidified lines; its arrows are exactly module isomorphisms
preserving rigidifications. Source: Deligne 4.2
(blueprint: def-sfb-rigidified-space-lines). -/
abbrev RigidifiedLines (e : B ⟶ X) :=
  Core (ObjectProperty.FullSubcategory (IsRigidifiedLine e))

/-- Pullback of a rigidification along a commuting square, using the canonical tensor
composition comparisons, equality of the two composite maps, and unit multiplication.
Source: Deligne 4.2; Stacks, Tag 03D7 (blueprint: def-sfb-rigidified-space-lines). -/
def rigidifiedModulePullback (e : B ⟶ X) (e' : B' ⟶ X')
    (a : B' ⟶ B) (b : X' ⟶ X) (w : a ≫ e = e' ≫ b) :
    RigidifiedModule e ⥤ RigidifiedModule e' :=
  CostructuredArrow.map₂
    (moduleTensorComposition e' b ≪≫ eqToIso (congrArg moduleTensorPullback w.symm) ≪≫
      (moduleTensorComposition a e).symm).hom
    (rigidifiedUnitIso a).hom

/-- Tensor pullback preserves lines and their rigidifications.
Source: Stacks, Tag 03D7; Deligne 4.2 (blueprint: def-sfb-rigidified-space-lines).
Proof: locally a line is the unit, and tensor inverse image preserves local
trivializations by its unit multiplication isomorphism. The displayed new
rigidification is a composite of three isomorphisms, hence is invertible. -/
theorem rigidifiedModulePullback_isLine (e : B ⟶ X) (e' : B' ⟶ X')
    (a : B' ⟶ B) (b : X' ⟶ X) (w : a ≫ e = e' ≫ b)
    (L : RigidifiedModule e) (hL : IsRigidifiedLine e L) :
    IsRigidifiedLine e' ((rigidifiedModulePullback e e' a b w).obj L) := by
  sorry

/-- Canonical pullback on rigidified-line groupoids, including its map on isomorphisms.
Source: Deligne 4.2 (blueprint: def-sfb-rigidified-space-lines). -/
def rigidifiedLinePullback (e : B ⟶ X) (e' : B' ⟶ X')
    (a : B' ⟶ B) (b : X' ⟶ X) (w : a ≫ e = e' ≫ b) :
    RigidifiedLines e ⥤ RigidifiedLines e' :=
  (ObjectProperty.lift (IsRigidifiedLine e')
    (ObjectProperty.ι (IsRigidifiedLine e) ⋙ rigidifiedModulePullback e e' a b w)
    (fun L ↦ rigidifiedModulePullback_isLine e e' a b w L.obj L.property)).core

/-- Forget a rigidified line down to its underlying module, including on isomorphisms.
Source: Deligne 4.2 (blueprint: def-sfb-rigidified-space-lines). -/
def rigidifiedLineForget (e : B ⟶ X) : RigidifiedLines e ⥤ X.Modules :=
  Core.inclusion _ ⋙ ObjectProperty.ι (IsRigidifiedLine e) ⋙ CostructuredArrow.proj _ _

/-- Canonical compatibility of restriction and base pullback, specified on underlying
modules by tensor associativity. The four section squares and the two commuting
squares are actual equalities of maps, so no comparison is free to vary.
Source: Deligne 4.2; Stacks, Tag 03D7
(blueprint: def-sfb-rigidified-space-lines).
Proof: identify both iterated tensor pullbacks with pullback along the common
composite using moduleTensorComposition. Its local formula is associativity of
pure tensors. The unit multiplication maps intertwine the rigidifications, by
associativity of ring multiplication; hence this module comparison lifts to the
rigidified comma categories and their cores. Faithfulness of the forgetful functor
forces uniqueness. The same tensor formula gives coherence for successive squares. -/
theorem rigidifiedLineSquare_existsUnique
    {B₀ B₁ B₂ B₃ X₀ X₁ X₂ X₃ : AlgebraicSpace S}
    (e₀ : B₀ ⟶ X₀) (e₁ : B₁ ⟶ X₁) (e₂ : B₂ ⟶ X₂) (e₃ : B₃ ⟶ X₃)
    (a₁ : B₁ ⟶ B₀) (a₂ : B₂ ⟶ B₀) (a₃ : B₃ ⟶ B₁) (a₄ : B₃ ⟶ B₂)
    (b₁ : X₁ ⟶ X₀) (b₂ : X₂ ⟶ X₀) (b₃ : X₃ ⟶ X₁) (b₄ : X₃ ⟶ X₂)
    (w₁ : a₁ ≫ e₀ = e₁ ≫ b₁) (w₂ : a₂ ≫ e₀ = e₂ ≫ b₂)
    (w₃ : a₃ ≫ e₁ = e₃ ≫ b₃) (w₄ : a₄ ≫ e₂ = e₃ ≫ b₄)
    (ha : a₃ ≫ a₁ = a₄ ≫ a₂) (hb : b₃ ≫ b₁ = b₄ ≫ b₂) :
    ∃! c : rigidifiedLinePullback e₀ e₁ a₁ b₁ w₁ ⋙
          rigidifiedLinePullback e₁ e₃ a₃ b₃ w₃ ≅
        rigidifiedLinePullback e₀ e₂ a₂ b₂ w₂ ⋙
          rigidifiedLinePullback e₂ e₃ a₄ b₄ w₄,
      ∀ L : RigidifiedLines e₀,
        (rigidifiedLineForget e₃).map (c.hom.app L) =
          (moduleTensorComposition b₃ b₁).hom.app (rigidifiedLineForget e₀ |>.obj L) ≫
            (eqToIso (congrArg moduleTensorPullback hb)).hom.app
              (rigidifiedLineForget e₀ |>.obj L) ≫
            (moduleTensorComposition b₄ b₂).inv.app
              (rigidifiedLineForget e₀ |>.obj L) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
