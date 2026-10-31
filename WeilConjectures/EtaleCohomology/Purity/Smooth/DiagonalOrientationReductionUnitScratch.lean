module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitPullback

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] (X : Scheme.{u})

set_option profiler true in
theorem t0 : 𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) =
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) := rfl

end AlgebraicGeometry.Etale
