/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSections
public import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf

/-! # The normalized restriction equation for the structure module

Source: Stacks Project, Tags 0096, 01CA and 03DR, equation (35.8.1).
(blueprint: lem-sc-etale-tensor-unit-restriction-equation)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The normalized restriction followed by the adjoint structure-module map is the
structure-sheaf restriction followed after the source structure-module map.
Source: Stacks Project, Tags 0096, 01CA and 03DR, equation (35.8.1).
(blueprint: lem-sc-etale-tensor-unit-restriction-equation)

Proof: Write epsilon_f for tensorPullbackObjUnitToUnit f. Apply the composite
adjunction Hom equivalence to the two maps from g^*u^*O_X to O_V. The unit equation
of tensorSectionsComp and naturality of the adjunction unit identify the image of
c_{g,u} followed by epsilon_{g >> u} with the image of g^*(epsilon_u) followed by
epsilon_g. Both images are the composite structure-sheaf map, by the defining
equations eta_f followed by f_*(epsilon_f) = f-sharp. Injectivity of the Hom
bijection proves equality. Transport along g >> u = v by equality elimination.
Evaluate on the top open. Unit naturality moves epsilon_u through section pullback;
the adjunction-unit equation for epsilon_g makes the resulting map g-sharp.
The restriction from the inverse image of top to top is the identity. These
identities give the stated equality of additive homomorphisms, including on the
empty scheme and for identity or composite site arrows. -/
theorem etaleTensorUnitRestriction_equation {X : Scheme.{u}} {U V : X.Etale}
    (g : V ⟶ U) (x : Γ((tensorPullback U.hom).obj
      (SheafOfModules.unit X.ringCatSheaf), ⊤)) :
    (tensorPullbackObjUnitToUnit V.hom).app ⊤
        (etaleTensorSectionsRestriction (SheafOfModules.unit X.ringCatSheaf) g x) =
      g.left.appTop ((tensorPullbackObjUnitToUnit U.hom).app ⊤ x) := by sorry

end AlgebraicGeometry.Scheme.Modules
