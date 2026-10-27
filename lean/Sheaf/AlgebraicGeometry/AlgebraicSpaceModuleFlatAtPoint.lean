module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.RingHom.Flat

/-! # Pointwise relative flatness of algebraic-space modules

Source: Stacks Project, Morphisms of Spaces, Tag 05VU and definition-flat-module
(blueprint: def-sfb-space-module-flat-at-point).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Relative flatness at a point, tested on every compatible pair of etale scheme charts.
The module is restricted to Zariski opens of the source chart. Its ordinary stalk is
regarded as a module over the base-chart local ring through the actual scheme stalk map.
For quasi-coherent modules this is the flatness of Tag 05VU and definition-flat-module.
Source: Stacks Project, Morphisms of Spaces, Tag 05VU and definition-flat-module
(blueprint: def-sfb-space-module-flat-at-point). -/
def ModuleIsFlatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (M : X.Modules) (x : Point X.obj.obj) : Prop :=
  ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (h : U.obj.left ⟶ V.obj.left),
    U.obj.hom ≫ f.hom.hom = yoneda.map h ≫ V.obj.hom →
      ∀ u : U.obj.left.left, schemePointMap U.obj.hom u = x →
        Module.Flat (V.obj.left.left.presheaf.stalk (h.left u))
          ((ModuleCat.restrictScalars (h.left.stalkMap u).hom).obj
            ((RingedSpace.moduleStalkFunctor U.obj.left.left.toRingedSpace u).obj
              ((schemeRestriction X U).obj M)))

end AlgebraicGeometry.AlgebraicSpace
