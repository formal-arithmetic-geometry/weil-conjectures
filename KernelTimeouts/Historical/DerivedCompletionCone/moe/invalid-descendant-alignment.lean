import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

open CategoryTheory Limits MonoidalCategory Opposite

universe w v' u' u

namespace HistoricalAD

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)

set_option debug.skipKernelTC true in
noncomputable def coneLetProvider
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) := by
  letI : MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
    inferInstance
  exact sorry

end HistoricalAD
