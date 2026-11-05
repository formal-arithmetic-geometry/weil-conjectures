/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Tensor-power maps into an algebra sheaf

Source: Stacks Project, Modules, Section 01CF; Tag 09MS.
(blueprint: lem-sc-algebra-sheaf-tensor-power-maps).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

@[irreducible] private noncomputable def sectionProduct {X : Scheme.{u}} {M N : X.Modules}
    (B : X.CommAlgebraSheaf) (f : M ⟶ commAlgebraSheafModule X.sheaf B)
    (g : N ⟶ commAlgebraSheafModule X.sheaf B) :
    M ⊗ N ⟶ commAlgebraSheafModule X.sheaf B :=
  (SheafOfModules.tensorObjIsoSheafification M N).hom ≫
    ((sheafificationAdjunction X).homEquiv _ _).symm (presheafProduct B f g)

end
end AlgebraicGeometry.Scheme.Modules
