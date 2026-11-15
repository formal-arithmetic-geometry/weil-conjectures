/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfDiagonalKernelIntegrals
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence

/-! # Transport of the diagonal-kernel trace counit through compactifications -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Transport the kernel adjunction through any compactification, retaining its trace formula. -/
theorem sfCompactificationKernelTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsProper f]
    (c : Compactification f) {B : DerivedCategoryModule A X} (d : TraceDiagonalDatum A f B)
    (adj₀ : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣
      CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B)
    (heps : adj₀.counit = SfDiagonalKernel.counit A d) :
    ∃ (t : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj B ⟶
        constantComplex A Y)
      (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣
        CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B),
      ∀ K : DerivedCategoryModule A Y,
        ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app B).app K ≫
          adj.counit.app K =
        ((derivedTensor (ModuleCat.{u + 1} A) Y).map t).app K ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y K).hom := by
  let E := rightDerivedLowerShriekIso A c
  refine ⟨E.hom.app B ≫ d.trace, adj₀.ofNatIsoLeft E.symm, ?_⟩
  intro K
  have hp := projectionMapOfCompactification_rightDerivedLowerShriekIso A c B K
  simp only [Adjunction.ofNatIsoLeft_counit, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, heps, SfDiagonalKernel.counit]
  dsimp only [E, Functor.comp_obj, CoordinateTrace.pull]
  erw [← Category.assoc, hp]
  have hproj : (projectionIso A f B).hom.app K =
      ((projectionMap (ModuleCat.{u + 1} A) f).app B).app K := rfl
  rw [← hproj]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp,
    NatTrans.comp_app]
  rfl

end AlgebraicGeometry.Etale
