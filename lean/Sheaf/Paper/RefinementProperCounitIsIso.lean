module

public import Sheaf.Paper.RefinementOpenRestrictionData
import Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit
import Sheaf.AlgebraicGeometry.ProEtaleOpenPullbackKInjective
import Sheaf.AlgebraicGeometry.ProEtaleIdentifiedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.IntegralFinitePullbackComposition

/-! Isomorphism of the proper counit after restriction to the distinguished open. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurCompactSupport

variable (R : Coefficients.{u})
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
  (hi : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
    (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))

/--
Source: Stacks 0F7B and 0F7I, clopen distinguished-section calculation.
The proper counit becomes invertible after pulling back along the distinguished
open immersion because the refinement fibre product decomposes into that clopen
section and its complement; extension by zero has zero restriction to the
complement and the counit is the identity on the section.
(blueprint: lem-sf-refinement-open-restriction-is-iso-components).
-/
theorem refinementProperCounit_isIso
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    IsIso ((pull R c.i).map ((proEtaleRingDerivedAdjunction r.hom
      (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)).counit.app
      ((openExtension R c.i).mapDerivedCategory.obj M))) := by
  sorry


/--
Source: the definition of `refinementRestriction` in the coefficient comparison
construction, with the pullback compositor of Tags 03D8 and 0D6D.
The specified component is exactly the compositor followed by the pulled-back
proper counit; this is the formal factorization used to reduce the component
isomorphism to the geometric counit calculation.
(blueprint: lem-sf-refinement-open-restriction-is-iso-components).
-/
theorem refinementRestriction_factorization
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    refinementRestriction R r hi M =
      (refinementPull R r hi).hom.app
          ((push R r.hom).obj ((openExtension R c.i).mapDerivedCategory.obj M)) ≫
        (pull R c.i).map ((proEtaleRingDerivedAdjunction r.hom
          (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)).counit.app
          ((openExtension R c.i).mapDerivedCategory.obj M)) := by
  sorry

end WeilConjectures.PurCompactSupport
