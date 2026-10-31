module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitPullback
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClassCoefficientChange

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] (X : Scheme.{u})

#synth BraidedCategory (ModuleCat.{u + 1} Λ)
#synth BraidedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
#synth MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
#synth MonoidalCategory (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
#synth MonoidalCategory (HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ))

section
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
#synth BraidedCategory (ModuleCat.{u + 1} Λ)
#synth BraidedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
#synth MonoidalCategory (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
end

end AlgebraicGeometry.Etale
