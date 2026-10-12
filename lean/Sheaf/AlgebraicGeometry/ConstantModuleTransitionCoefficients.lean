/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- Forgetting scalars respects the adjoint constant-sheaf transition.

Source: Stacks Project, Tags 03DB and 03CO.
(blueprint: lem-weil-pbc-constant-module-transition-coefficients).

Proof: The adjoint constant comparison sends each sheafification generator to
its base change with the same value. This follows from the unit equation for
uniqueness of left adjoints to terminal evaluation, transported to every object
by naturality. The constantCommuteCompose comparison also sends a generator to
the generator of its underlying abelian group, by the defining equation for
sheafifyComposeIso. Thus both composites agree on every constant-presheaf
generator. Since forgetting scalars preserves sheafification, the source is
canonically the sheafification of the constant underlying abelian presheaf;
the universal property of sheafification proves equality. This argument applies
to zero modules, empty schemes and arbitrary morphisms. -/
theorem constantModuleTransition_coefficients
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {Z W : Scheme.{u}} (g : W ⟶ Z)
    [Z.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
    [W.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})] :
    let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let A := AddCommGrpCat.{u + 1}
    (sheafCompose Z.smallEtaleTopology V).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
          (lowerStar (ModuleCat.{u + 1} Λ) g).map
            ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)) ≫
      (lowerStar A g).map ((constantCommuteCompose W.smallEtaleTopology V).hom.app M) =
    (constantCommuteCompose Z.smallEtaleTopology V).hom.app M ≫
      (upperStarLowerStarAdjunction A g).unit.app _ ≫
      (lowerStar A g).map ((Scheme.upperStarConstantSheafIso A g).hom.app (V.obj M)) := by
  sorry

end AlgebraicGeometry.Etale
