module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The resolution map admits a semilinear lift over the map on global functions.
Source: Stacks Project, Cohomology of Sheaves, Equation 01F9 and Remark 01FB.
(blueprint: lem-weil-pbc-module-cohomology-fmap-semilinear-lift)

The lift is obtained by checking scalar compatibility on the section, cycle and
homology maps in the defining resolution comparison. -/
theorem ModuleCohomologyFMapData.map_semilinear
    {X Y : Scheme.{u}} {h : X ⟶ Y}
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    {φ : G ⟶ (pushforward h).obj F} (D : ModuleCohomologyFMapData h G F φ) (p : ℕ) :
    ∃ f : ((Y.toRingedSpace.moduleCohomology p).obj G) →ₛₗ[h.appTop.hom]
      ((X.toRingedSpace.moduleCohomology p).obj F),
      ∀ x, f x = D.map p x := by
  sorry

end AlgebraicGeometry.Scheme.Modules
