/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups C2, F5
-/
module

public import Sheaf.Paper.SixFunctorOperationDatumStages
public import Sheaf.Paper.ProEtaleCompositionTowerDefinitions

/-! # The specified candidate compact-support compositor

This is the unchanged construction formerly in CartesianCompactSupportCompositor.
It is shared by the Cartesian assembly and its canonical site square so both use
one declaration without unfolding the four comparison factors.
Source: Stacks Project, Tags 0F7J and 0F7K
(blueprint: def-sf-cartesian-candidate-compositor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.ProjectionTriangleAssembly

/-- The canonical origin compositor at three specified candidates, with the canonical
candidate comparisons inserted on both ends. This extends the existing tower component
notation to an arbitrary retained origin object; it chooses no comparison maps.
Source: Stacks 0F7J; thm-sf-comp-composition
(blueprint: lem-sf-projection-compatible-triangle-assembly). -/
def candidateCompositor (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).FullSubcategory) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cf).obj K.obj) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cfg).obj K.obj :=
  letI := cf.hasCompactification
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg).map
      ((towerCandidateComparison Λ cf (HasCompactification.compactification f)).hom.app K) ≫
    (towerCandidateComparison Λ cg (HasCompactification.compactification g)).hom.app
      ((originCompactSupport Λ f).obj K) ≫
    (originCompositionAmbient Λ f g).hom.app K ≫
    (towerCandidateComparison Λ (HasCompactification.compactification (f ≫ g)) cfg).hom.app K

end AlgebraicGeometry.ProEtale.ProjectionTriangleAssembly
