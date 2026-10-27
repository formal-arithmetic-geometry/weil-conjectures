/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.QcoherentZariskiCohomologyMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison

/-! # Evaluation of the explicit Zariski module h-map

Source: Stacks Project, Tag 01FB; the inverse-image Ext construction.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local instance] HasExt.standard
attribute [local irreducible] zariskiModuleHMap tensorPullback tensorPullbackObj

/-- Evaluate the Zariski module h-map using the recorded abelian inverse image.
Source: Stacks Project, Tag 01FB; the explicit Ext h-map construction.
(blueprint: lem-pbc-zariski-module-hmap-formula).

Proof: Unfold zariskiModuleHMap. Its inverse-image functor is invImage g, its
constant-integer comparison is constIso(g).symm, and its adjoint coefficient map
is coeff(g,phi). The underlying module morphism has exactly the components in
moduleAbelianHMap; the naturality proofs agree by proof irrelevance. Evaluation
of the composite additive homomorphisms gives the displayed formula. -/
theorem zariskiModuleHMap_formula {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (φ : F ⟶ (pushforward g).obj G)
    (q : ℕ) (x : CoherentEtale.Source X F q) :
    Sheaf.H.map.{u + 1} (coeff g φ) q
      (Sheaf.H.mapFunctor.{u + 1} (invImage g) (constIso g).symm
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q x) =
      zariskiModuleHMap g φ q x := by
  unfold zariskiModuleHMap
  rfl

end
end AlgebraicGeometry.Scheme.Modules
