/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.ModuleAbelianUniverseEquiv

/-! # The resolution formula for the large module/abelian comparison

Source: Stacks Project, Tag 03FD.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj moduleAbelianCohomologyLarge

private theorem comparison_component
    {C : Type*} [Category C] {R : Type u} [Ring R]
    {K : C ⥤ ModuleCat.{u} R} {L : C ⥤ AddCommGrpCat.{u}}
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ L) (M : C) (x : K.obj M) :
    (η.app M).hom x = ExtEdgeResolution.moduleComparisonEquiv η M x := rfl

/-- Express the large module/abelian comparison through the fixed resolution equivalence.
Source: Stacks Project, Tag 03FD; the common-resolution comparison construction.
(blueprint: lem-pbc-module-abelian-large-resolution-formula).

Proof: Apply the recorded component formula for the large comparison. The fixed
resolution equivalence is the additive equivalence of that same component, whose
value equals its homomorphism applied to x. Apply universe change to this equality
and unfold its function wrapper. -/
theorem moduleAbelianCohomologyLarge_resolutionFormula (X : Scheme.{u}) (F : X.Modules) (q : ℕ)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    moduleAbelianCohomologyLarge X F q x =
      moduleAbelianUniverseMap X F q (moduleCohomologyExtResolutionEquiv X F q x) := by
  have h := comparison_component (moduleCohomologyExtResolutionNatIso X q) F x
  refine (moduleAbelianCohomologyLarge_component X F q x).trans ?_
  unfold moduleAbelianUniverseMap moduleCohomologyExtResolutionEquiv
  exact congrArg
    (@coherentExtUniverseEquiv _ _ _ (comparisonHasExt X) (HasExt.standard _) _ _ q) h

end
end AlgebraicGeometry.Scheme.Modules
