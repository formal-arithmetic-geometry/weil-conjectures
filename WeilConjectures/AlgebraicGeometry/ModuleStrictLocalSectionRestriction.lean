/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictLocalSectionCone
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves

/-! # Module-valued strict-local section restriction

Source: Stacks Project, Tags 03Q9 and 03QO; blueprint:
`def-pur-module-strict-local-section-restriction`.
-/

@[expose] public section

universe u
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Restriction of a module-valued section along a strict-local pointed
neighbourhood section.  The inverse-image unit is followed by the canonical
section pullback and the terminal-object/global-sections comparison.
Source: Stacks Project, Tags 03Q9 and 03QO.
(blueprint: def-pur-module-strict-local-section-restriction). -/
def moduleStrictLocalSectionRestriction
    (A : Type (u + 1)) [CommRing A] {B : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B)
    (F : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    F.obj.obj (op ((Scheme.AffineEtale.Spec B).obj
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)) ⟶
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        (ModuleCat.{u + 1} A)).obj
        ((upperStar (ModuleCat.{u + 1} A)
          (Scheme.strictHenselizationStructuralMap s)).obj F) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (Scheme.strictHenselizationStructuralMap s)).unit.app F).hom.app
      (op ((Scheme.AffineEtale.Spec B).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)) ≫
    ((upperStar (ModuleCat.{u + 1} A)
      (Scheme.strictHenselizationStructuralMap s)).obj F).obj.map
      (strictLocalNeighbourhoodSection s j).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (Scheme.strictHenselizationScheme s))
        (Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s)))
        Over.mkIdTerminal)).inv.app _

end AlgebraicGeometry.Etale
