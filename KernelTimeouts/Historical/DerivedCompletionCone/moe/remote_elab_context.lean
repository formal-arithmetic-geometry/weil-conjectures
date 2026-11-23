import MOEStage
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

open CategoryTheory Limits MonoidalCategory Opposite
universe u
set_option moe.maxDepth 80

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)
  (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))

#moe_elab (Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K))
#moe_elab (Cone (DerivedCategory.derivedCompletionDiagram J I K))
