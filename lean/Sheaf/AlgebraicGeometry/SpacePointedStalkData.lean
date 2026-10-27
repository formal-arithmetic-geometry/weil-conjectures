/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Normalized pointed étale stalk data

Source: Stacks Project, Properties of Spaces, Tags 04K2, 04K5 and 05VQ;
Modules on Sites, Tags 04EQ and 05V5; Morphisms of Spaces, Tag 03MB;
More on Morphisms of Spaces, Tag 05ZS
(blueprint: def-sfb-space-pointed-stalk-data).

These structures record normalized presentations of the objects used in the
geometric stalk calculation. Their defining equations prescribe the comparisons
on germs. This definition module makes no existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace

/-- SquareZeroPoint: normalized data used by the geometric stalk calculation.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-pointed-stalk-data). -/
abbrev SquareZeroPoint {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  CostructuredArrow yoneda X.obj.obj

/-- SquareZeroNeighborhood: normalized data used by the geometric stalk calculation.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-pointed-stalk-data). -/
abbrev SquareZeroNeighborhood {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p : SquareZeroPoint X) := StructuredArrow p
    (ObjectProperty.ι (fun T : CostructuredArrow yoneda X.obj.obj ↦ IsEtale T.hom))

/-- squareZeroNeighborhoodForget: normalized data used by the geometric stalk calculation.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-pointed-stalk-data). -/
def squareZeroNeighborhoodForget {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p : SquareZeroPoint X) : SquareZeroNeighborhood p ⥤ X.EtaleSite :=
  StructuredArrow.proj _ _

/-- squareZeroStructure: normalized data used by the geometric stalk calculation.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-pointed-stalk-data). -/
def squareZeroStructure {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.EtaleSiteᵒᵖ ⥤ CommRingCat.{u} := X.etaleForget.op ⋙ Scheme.Γ

/-- SquareZeroStalk: normalized data used by the geometric stalk calculation.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-pointed-stalk-data). -/
structure SquareZeroStalk {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p : SquareZeroPoint X) (R : X.EtaleSiteᵒᵖ ⥤ CommRingCat.{u}) where
  ring : CommRingCat.{u}
  ringGerms : (squareZeroNeighborhoodForget p).op ⋙ R ⟶ (Functor.const _).obj ring
  ringColimit : IsColimit (Cocone.mk ring ringGerms)
  modules : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) ⥤ ModuleCat.{u} ring
  moduleGerms (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (squareZeroNeighborhoodForget p).op ⋙ M.presheaf ⟶
      (Functor.const _).obj ((forget₂ (ModuleCat ring) AddCommGrpCat).obj (modules.obj M))
  moduleColimit (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    IsColimit (Cocone.mk _ (moduleGerms M))
  map_germ {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ N) (n : SquareZeroNeighborhood p) (m : M.obj (op n.right)) :
    (modules.map f) ((moduleGerms M).app (op n) m) =
      (moduleGerms N).app (op n) (f.app (op n.right) m)
  smul_germ (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (n : SquareZeroNeighborhood p) (a : R.obj (op n.right)) (m : M.obj (op n.right)) :
    (moduleGerms M).app (op n) (a • m) =
      (@id ring (ringGerms.app (op n) a)) •
        (@id (modules.obj M) ((moduleGerms M).app (op n) m))

/-- SquareZeroStalkFamily: normalized data used by the geometric stalk calculation.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-pointed-stalk-data). -/
structure SquareZeroStalkFamily {S : Scheme.{u}} (X : AlgebraicSpace S)
    (R : X.EtaleSiteᵒᵖ ⥤ CommRingCat.{u}) where
  ringSheaf : Presheaf.IsSheaf X.etaleTopology (R ⋙ forget₂ CommRingCat RingCat)
  stalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
    (s : yoneda.obj (Over.mk b) ⟶ X.obj.obj) : SquareZeroStalk (CostructuredArrow.mk s) R
  exact (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
    (s : yoneda.obj (Over.mk b) ⟶ X.obj.obj) :
    PreservesFiniteLimits
      (SheafOfModules.forget (⟨_, ringSheaf⟩ : Sheaf X.etaleTopology RingCat) ⋙
        (stalk Ω b s).modules) ∧
    PreservesFiniteColimits
      (SheafOfModules.forget (⟨_, ringSheaf⟩ : Sheaf X.etaleTopology RingCat) ⋙
        (stalk Ω b s).modules)
  conservative (M N : SheafOfModules.{u}
      (⟨_, ringSheaf⟩ : Sheaf X.etaleTopology RingCat)) (f : M ⟶ N) :
    IsIso f ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (.of Ω) ⟶ S) (s : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
      IsIso ((stalk Ω b s).modules.map f.val)

end AlgebraicGeometry.AlgebraicSpace
