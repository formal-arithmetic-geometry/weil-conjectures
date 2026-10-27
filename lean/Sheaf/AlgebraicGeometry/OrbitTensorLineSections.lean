/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
/-! # Sections and comparisons for orbit tensor descent

Source: Stacks Project, Tags 0096, 0097, 01CA and 01CD.
(blueprint: def-per-orbit-tensor-section-comparisons)

These are the unchanged section constructions and normalized comparisons extracted
from `OrbitTensorLineDescent` so its proof lemmas can use them without an import cycle.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Pull a section back to an invariant open and transport along the specified equality
of opens. Source: Stacks 0096 (blueprint: def-per-orbit-tensor-section-comparisons). -/
noncomputable def orbitInvariantPullback {X : Scheme.{u}} (b : X ⟶ X)
    (F : X.Modules) (U : X.Opens) (hU : b ⁻¹ᵁ U = U) (s : Γ(F, U)) :
    Γ((tensorPullback b).obj F, U) :=
  ((tensorPullback b).obj F).presheaf.map (eqToHom hU.symm).op
    (tensorPullbackSection b F U s)

/-- The tensor of the translates of one section over an invariant open, for the listed
factors. Source: Stacks 01CA, 01CD; the invariant-frame argument of the node
(blueprint: def-per-orbit-tensor-section-comparisons). -/
noncomputable def orbitTensorFrameList {H : Type v} {X : Scheme.{u}}
    (a : H → (X ≅ X)) (L : X.Modules) (U : X.Opens)
    (hU : ∀ h : H, (a h).hom ⁻¹ᵁ U = U) (s : Γ(L, U)) :
    (hs : List H) → Γ(pencilTranslateTensor a L hs, U)
  | [] => unitSectionsEquiv U 1
  | h :: hs => tmulSection (orbitInvariantPullback (a h).hom L U (hU h) s)
      (orbitTensorFrameList a L U hU s hs)

/-- An orbit frame is the tensor of all translates of the same section; if that section
is a frame, so is this one. Source: Stacks 01CD, 0BCY; Rydh Proposition 4.7
(blueprint: def-per-orbit-tensor-section-comparisons). -/
noncomputable def orbitTensorFrame {H : Type v} [Finite H] {X : Scheme.{u}}
    (a : H → (X ≅ X)) (L : X.Modules) (U : X.Opens)
    (hU : ∀ h : H, (a h).hom ⁻¹ᵁ U = U) (s : Γ(L, U)) :
    Γ(pencilOrbitBundle a L, U) :=
  orbitTensorFrameList a L U hU s (pencilGroupElements H)

/-- Pure tensor sections in the existing tensor power, including the section 1 in degree
zero. Source: Stacks 01CA (blueprint: def-per-orbit-tensor-section-comparisons). -/
noncomputable def orbitPowerSection {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) :
    (d : ℕ) → (Fin d → Γ(F, U)) → Γ(F.tensorPow d, U)
  | 0, _ => unitSectionsEquiv U 1
  | d + 1, s => tmulSection (s 0) (orbitPowerSection F U d (fun i ↦ s i.succ))

/-- The canonical linearization on a module pulled back from the quotient. It is the
normalized composition comparison followed by q a = q, with no choice of scalar.
Source: Stacks 0097 (blueprint: def-per-orbit-tensor-section-comparisons). -/
noncomputable def orbitQuotientPullbackIso {X Y : Scheme.{u}} (q : X ⟶ Y)
    (b : X ⟶ X) (hb : b ≫ q = q) (M : Y.Modules) :
    (tensorPullback b).obj ((tensorPullback q).obj M) ≅ (tensorPullback q).obj M :=
  ((tensorPullbackSectionComp b q).app M).symm ≪≫
    eqToIso (congrArg (fun f : X ⟶ Y ↦ (tensorPullback f).obj M) hb)

/-- The identity comparison used in the orbit linearization law.
Source: Stacks 0097 (blueprint: def-per-orbit-tensor-section-comparisons). -/
noncomputable def orbitLinearizationUnit {H : Type v} [One H] {X : Scheme.{u}}
    (a : H → (X ≅ X)) (a_one : (a 1).hom = 𝟙 X) (F : X.Modules) :
    (tensorPullback (a 1).hom).obj F ≅ F :=
  eqToIso (congrArg (fun b : X ⟶ X ↦ (tensorPullback b).obj F) a_one) ≪≫
    (tensorPullbackSectionId X).app F

/-- The composition comparison used in the orbit linearization cocycle. The order is
contravariant: a_(gh) = a_g composed with a_h.
Source: Stacks 0097 (blueprint: def-per-orbit-tensor-section-comparisons). -/
noncomputable def orbitLinearizationComp {H : Type v} [Mul H] {X : Scheme.{u}}
    (a : H → (X ≅ X))
    (a_mul : ∀ g h : H, (a (g * h)).hom = (a h).hom ≫ (a g).hom)
    (F : X.Modules) (g h : H) :
    (tensorPullback (a (g * h)).hom).obj F ≅
      (tensorPullback (a h).hom).obj ((tensorPullback (a g).hom).obj F) :=
  eqToIso (congrArg (fun b : X ⟶ X ↦ (tensorPullback b).obj F) (a_mul g h)) ≪≫
    (tensorPullbackSectionComp (a h).hom (a g).hom).app F

end AlgebraicGeometry.Scheme.Modules
