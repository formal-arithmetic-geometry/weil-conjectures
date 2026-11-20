import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

open CategoryTheory Limits MonoidalCategory Opposite

universe w v' u' u

namespace HistoricalR2

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)

noncomputable def inlineConeExplicit
    [MC : MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))]
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) := sorry

end HistoricalR2
