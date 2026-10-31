/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private def proj (X : Scheme.{u}) (H : X.Modules) (x : X) :
    moduleCup_godementObject X H ⟶ skyscraper x (H.presheaf.stalk x) :=
  CategoryTheory.Limits.Pi.π (fun y : X ↦ skyscraper y (H.presheaf.stalk y)) x

private def eval (X : Scheme.{u}) (H : X.Modules) (x : X) :
    (moduleCup_godementObject X H).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      H.presheaf.stalk x :=
  skyscraperStalkEval x (H.presheaf.stalk x) ∘ₗ (proj X H x).stalkLinearMap x

end
end AlgebraicGeometry.Scheme.Modules
