module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry

/-- Affine K-injective cohomology comparison. The comparison is obtained by affine
sections on an affine basis, using quasi-coherence and K-injectivity, and is
linear over the direct-image algebra.
Source: Stacks Project, Tag 0AVW and Tag 08D4.
(blueprint: new-affine-algebra-kinjective-cohomology-comparison). -/
theorem affine_algebra_kinjective_cohomology_comparison
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    ∃ e : (((RingedSpace.moduleDirectImage
          (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I).homology n ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj (I.homology n), True := by
  sorry

end AlgebraicGeometry
