/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Integral open–closed sequence with its sections normalization

Source: Stacks Project, Tags 095L and 03F3, and the Cartier proof (G1).
(blueprint: lem-sp-open-closed-integral-sections). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private theorem restrictedSectionsEquiv_apply {X : Scheme.{u}} (W : X.Opens)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : EtaleOpenComparison.integerSheaf W.toScheme ⟶
      (openImmersionRestriction AddCommGrpCat.{u + 1} W.ι).obj G) :
    EtaleOpenComparison.restrictedSectionsEquiv W.ι G f =
      G.obj.map ((MorphismProperty.Over.isoMk (Iso.refl W.toScheme)
        (Category.id_comp W.ι)).inv.op)
        (f.hom.app (op (Scheme.Etale.mk (𝟙 W.toScheme)))
          ((toSheafify W.toScheme.smallEtaleTopology
            ((Functor.const W.toScheme.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
                (op (Scheme.Etale.mk (𝟙 W.toScheme))) ⟨1⟩)) := by
  dsimp only [EtaleOpenComparison.restrictedSectionsEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_apply]
  rw [constantSheafAdj_homEquiv_apply, AddCommGrpCat.uliftZMultiplesAddEquiv_eq]
  exact Iso.addCommGroupIsoToAddEquiv_apply _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.Etale
