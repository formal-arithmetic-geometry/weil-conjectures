module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Base change commutes with relative restriction along one inclusion of opens.
Source: Stacks Project, Cohomology, Tags 08HY, 08BV and 08HZ.
(blueprint: new-relative-mv-second).
Proof: Expand relativeMVRestriction as the mate of the restricted counit and
cancel the right-adjoint composition comparisons on both paths. Transpose under
the adjunction for W and its inverse-image open. The resulting maps are
composites of pullbacks of the same counit. Naturality of that counit and of φ
identifies their middle factors; associativity of the pinned pullback
composition comparisons identifies the outside factors. The lift identities
for relativeMVOpenLift give equality of the two projections, hence the equality
transport appearing in the local comparison is precisely the one in the
restriction. Injectivity of the adjunction Hom equivalence gives the claimed
square. No strictness of the inclusion is used, so equality and empty opens
are included. -/
theorem relativeMV_restriction_naturality
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (W U : X.Opens) (i : W ≤ U) :
    (derivedPullback g).map
        (relativeMVRestriction (X.homOfLE i) U.ι W.ι (Scheme.homOfLE_ι X i) f K) ≫
      (relativeMVLocalArrow f f' g g' hpull K K' φ W).hom =
      (relativeMVLocalArrow f f' g g' hpull K K' φ U).hom ≫
        relativeMVRestriction (relativeMVOpenLift g' i) (pullback.fst g' U.ι)
          (pullback.fst g' W.ι) (pullback.lift_fst _ _ _) f' K' := by
  sorry

end AlgebraicGeometry
