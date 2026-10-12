module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.RingTheory.SmoothAlgebraFilteredColimitDescent

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The affine-chart part of eventual smoothness: after passing to a later stage,
the pullback morphism admits a finitely presented smooth model and a comparison
isomorphism.  This is the affine descent argument of Tags 0CAQ and 01ZM(2)-(3).
Source: Stacks Project, Tag 0C0C, limits.tex, affine reduction of lemma-descend-smooth.
(blueprint: lem-sbc-noetherian-approximation-smooth-stage-affine-model) -/
theorem Scheme.NoetherianApproximation.exists_smooth_affine_model
    {S : Scheme.{u}} (N : S.NoetherianApproximation) {i : N.I}
    {Y X : Scheme.{u}} (p : Y ⟶ N.D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (f : X ⟶ S) [Smooth f] (a : X ⟶ Y)
    (H : IsPullback a f p (N.π.app i)) :
    ∃ (j : Over i) (Z : Scheme.{u}) (q : Z ⟶ N.D.obj j.left)
      (_ : LocallyOfFinitePresentation q) (_ : QuasiCompact q) (_ : QuasiSeparated q),
      Smooth q ∧ Nonempty (Z ≅ Limits.pullback p (N.D.map j.hom)) := by
  sorry

end AlgebraicGeometry
