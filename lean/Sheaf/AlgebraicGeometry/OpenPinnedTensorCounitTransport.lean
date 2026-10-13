/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.OpenPinnedTargetCounitTriangle
public import Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle

/-! # Counit comparison for one open leg
Source: Stacks Project, Tags 08DW and 0D5S. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]

/-- Transport and termwise tensor composition in a commuting open square.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-tensor-counit-transport).
Proof: the source and target homotopy comparison isomorphisms are the two
termwise paths from tensor pullback along the composite to restriction
followed by tensor pullback. Expand openPinnedTensorRestrictionIso into its
four factors. The target comparison cancels its inverse composition and
inverse open tensor comparison, leaving the source comparison, with transport
along hj. The functor from additive functors to homotopy functors preserves
these compositions and inverses, as does Qh. The counit family respects
transport along equality of scheme morphisms by equality induction. Combine
that transport identity with the termwise comparison identity. No derived
composition comparison, derived open-pullback comparison, or flatness of P
is used. Empty opens and zero complexes obey the same functor identities. -/
theorem open_pinned_tensor_counit_transport
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    eqToHom (congrArg (fun f ↦ (derivedPullback f).obj (DerivedCategory.Qh.obj P)) hj) ≫
      (pinnedPullbackCounit.{u, w} (U'.ι ≫ k)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTargetCompositionIso k U').hom.app P) ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P) =
    (pinnedPullbackCounit.{u, w} (j ≫ U.ι)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopySourceCompositionIso U j).hom.app P) := by
  sorry

end AlgebraicGeometry
