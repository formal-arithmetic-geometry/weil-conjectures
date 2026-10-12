module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.SmoothStageAffineModel
import Sheaf.RingTheory.SmoothAlgebraFilteredColimitDescent

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The locality/gluing part of eventual smoothness.  A smooth finite-stage model
for the finitely many affine charts, together with comparison isomorphisms, yields
smoothness of the original pullback morphism at a common later stage.
Source: Stacks Project, Tag 0C0C, limits.tex, locality of smoothness after a common
cofiltered refinement.
(blueprint: lem-sbc-noetherian-approximation-smooth-stage-gluing) -/
theorem Scheme.NoetherianApproximation.smooth_stage_of_affine_models
    {S : Scheme.{u}} (N : S.NoetherianApproximation) {i : N.I}
    {Y X : Scheme.{u}} (p : Y ⟶ N.D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (f : X ⟶ S) [Smooth f] (a : X ⟶ Y)
    (H : IsPullback a f p (N.π.app i))
    (hmodel : ∃ (j : Over i) (Z : Scheme.{u}) (q : Z ⟶ N.D.obj j.left)
      (_ : LocallyOfFinitePresentation q) (_ : QuasiCompact q) (_ : QuasiSeparated q),
      Smooth q ∧ Nonempty (Z ≅ Limits.pullback p (N.D.map j.hom))) :
    ∃ j : Over i, Smooth (pullback.snd p (N.D.map j.hom)) := by
  sorry

end AlgebraicGeometry
