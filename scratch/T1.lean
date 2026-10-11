import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
open CategoryTheory MonoidalCategory AlgebraicGeometry Etale
universe u
variable {Λ : Type (u + 1)} [CommRing Λ] {Y : Scheme.{u}}
set_option pp.explicit true in
#check (𝟙_ (DerivedCategoryModule Λ Y))
set_option pp.explicit true in
#check (𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
set_option pp.explicit true in
#check fun (h : Y ⟶ Y) => ((leftDerivedUpperStarTensorComparison (ModuleCat.{u+1} Λ) h).app (𝟙_ _))
