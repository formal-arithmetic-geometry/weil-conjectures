import MOEStage
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

open CategoryTheory Limits MonoidalCategory Opposite
universe u
set_option moe.maxDepth 80

#moe_elab (fun {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]
  [MC : MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))]
  (I : Ideal R) (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) =>
  Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K))
