module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Base change commutes with the relative unit of one open.
Source: Stacks Project, Cohomology, Tags 08HY and 08HZ.
(blueprint: new-relative-mv-first).
Proof: Transpose the two paths under the adjunction for the inverse-image open
followed by f'. Expand base change as the transpose of the pulled-back counit.
The unit of the composite adjunction and the right-adjoint mate defining
relativeMVImageComp cancel by the triangle identities. The pullback composition
coherence identifies the two remaining comparisons, using the pullback
projection equality. Naturality of the counit moves the object map φ through
the comparison. Both paths therefore have the same transpose. This works for
all opens, including the empty open, and for arbitrary φ. -/
theorem relativeMV_restriction_unit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (W : X.Opens) :
    (derivedPullback g).map (relativeMVUnit W.ι f K) ≫
      (relativeMVLocalArrow f f' g g' hpull K K' φ W).hom =
      (relativeMVGlobalArrow f f' g g' hpull K K' φ).hom ≫
        relativeMVUnit (pullback.fst g' W.ι) f' K' := by
  sorry

end AlgebraicGeometry
