/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Topology.InverseImageModule
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.Additive
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRings
import Sheaf.Topology.InverseImageStalk

/-!
# The stalk complex of termwise tensor pullback

Source: Stacks Project, Sheaves, Tag 0098; Cohomology, Tag 06YC.
(blueprint: lem-pc-tensor-pullback-stalk-complex)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace CochainComplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A complex with the termwise tensor pullback formula has the expected stalk complex.
Source: Stacks Project, Sheaves, Tag 0098; Cohomology, Tag 06YC, stalk comparison.
(blueprint: lem-pc-tensor-pullback-stalk-complex)

Proof: at `x`, the natural inverse-image stalk isomorphisms identify the source
ring and module stalks with those at `f x`. Their formulas on adjunction-unit germs,
and semilinearity of that unit, show that the module comparison respects the ring
comparison. Compose the inverse ring-stalk isomorphism with the stalk of `α` to get
`ρ`. Change of rings commutes with stalks: apply `stalkChangeOfRingsIso` termwise,
then the preceding inverse-image module comparison. These linear isomorphisms give
extension of scalars of the original stalk terms. Naturality on module morphisms
identifies the differentials with extension of the stalk differentials. Finally
compose with the stalks of `e`; the assumed differential square gives a chain
isomorphism to the stalk of `P`. This argument imposes no boundedness or flatness
assumption; if `X` is empty there is no `x`, and zero stalk rings cause no exception. -/
theorem exists_tensorPullback_stalk_complex_iso
    (X Y : RingedSpace.{u}) (f : X.carrier ⟶ Y.carrier)
    (α : TopCat.Sheaf.inverseImageRing f Y.sheaf ⟶ X.sheaf)
    (K : CochainComplex (RingedSpace.Modules Y) ℤ)
    (P : CochainComplex (RingedSpace.Modules X) ℤ)
    (e : ∀ i : ℤ, P.X i ≅
      SheafOfModules.changeOfRings.{u, u, u} α
        (TopCat.Sheaf.inverseImageModule f Y.sheaf (K.X i)))
    (he : ∀ i j : ℤ, P.d i j ≫ (e j).hom =
      (e i).hom ≫ SheafOfModules.changeOfRingsHom.{u, u, u} α
        (TopCat.Sheaf.inverseImageModule f Y.sheaf (K.X i))
        (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf (K.X i) (K.d i j)))
    (x : X) :
    ∃ ρ : Y.presheaf.stalk (f x) →+* X.presheaf.stalk x,
      Nonempty
        ((((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj
          (((RingedSpace.moduleStalkFunctor Y (f x)).mapHomologicalComplex (.up ℤ)).obj K)) ≅
        (((RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)).obj P)) :=
  by sorry

end
end CochainComplex
