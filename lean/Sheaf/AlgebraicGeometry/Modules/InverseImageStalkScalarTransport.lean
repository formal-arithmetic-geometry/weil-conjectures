/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.Topology.InverseImageStalk

/-!
# Scalar transport for inverse-image module stalks

Source: Stacks Project, Sheaves, Tags 008H and 0098.
(blueprint: lem-pc-inverse-image-stalk-scalar-transport).

This identifies two tensors of stalks before applying the stalk-of-change-of-rings
isomorphism. No tensor sheaf or pullback-module stalk occurs in the conclusion.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Scalar transport through the inverse-image stalk isomorphisms.
Source: Stacks Project, Sheaves, Tag 0098, proof using Tag 008H.
(blueprint: lem-pc-inverse-image-stalk-scalar-transport).
Proof: identify inverse-image ring and abelian stalks by Tag 008H. On germs the
inverse-image unit is semilinear, so the abelian identification is semilinear over
the ring identification. The adjunction identity on ring sections proves that the
stalk map of the adjoint ring morphism composed with the ring identification is
f.stalkMap x. The balanced map b tensor m maps to b tensor c(m), where c is the
abelian identification. For a in the original ring stalk, c(a m) = c_R(a)c(m), so
b tensor c(a m) = (ψ_x(c_R(a)) b) tensor c(m) = (f.stalkMap x(a) b) tensor c(m).
This proves balancing. Its inverse uses
c inverse and the inverse ring identification: for r in the inverse-image ring stalk,
c inverse(r n) = c_R inverse(r) c inverse(n), and
f.stalkMap x(c_R inverse(r)) = ψ_x(r), proving its balancing. Both composites are identities on
pure tensors and hence on the tensor products. The map and inverse are linear over
the target stalk ring. The inverse-image stalk germ formula gives the stated formula. -/
theorem exists_inverseImage_stalk_scalar_transport {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    ∃ β : ∀ G : Y.Modules,
      (ModuleCat.extendScalars (f.stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x)).obj G) ≅
        (ModuleCat.extendScalars
          ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
            (tensorPullbackRingMap f).hom).hom).obj
          (ModuleCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.toTopCat)
            (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toTopCat)
              (TopCat.Sheaf.inverseImageModule f.base Y.sheaf G).val.presheaf x)),
      ∀ (G : Y.Modules) (V : Y.Opens) (hx : f x ∈ V) (s : G.val.obj (op V)),
        (β G).hom ((1 : X.presheaf.stalk x) ⊗ₜ[_, (f.stalkMap x).hom]
          (TopCat.Presheaf.germ G.val.presheaf V (f x) hx s)) =
        (1 : (TopCat.Presheaf.stalkFunctor CommRingCat x).obj X.sheaf.obj) ⊗ₜ[
          TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.toTopCat)
          (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj x,
          ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
            (tensorPullbackRingMap f).hom).hom]
          (TopCat.Presheaf.germ
            (TopCat.Sheaf.inverseImageModule f.base Y.sheaf G).val.presheaf
            (f ⁻¹ᵁ V) x hx
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map f.base) AddCommGrpCat.{u}
              (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app
                ((SheafOfModules.toSheaf _).obj G)).hom.app (op V) s)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
