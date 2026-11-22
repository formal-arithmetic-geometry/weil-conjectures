import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

open CategoryTheory Limits MonoidalCategory Opposite

universe w v' u' u

namespace HistoricalR2
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)
noncomputable abbrev abbrevDiagram (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K
noncomputable def defDiagram (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K
@[reducible] noncomputable def reducibleDiagram
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K
noncomputable def namedAbbrev
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) : Cone (abbrevDiagram J I K) := sorry
noncomputable def namedDef
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) : Cone (defDiagram J I K) := sorry
noncomputable def namedReducible
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) : Cone (reducibleDiagram J I K) := sorry
noncomputable def sharedUnnamed
    [MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))]
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) := sorry
noncomputable def namedExplicit
    [MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))]
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (DerivedCategory.derivedCompletionDiagram J I K) := sorry
end HistoricalR2
