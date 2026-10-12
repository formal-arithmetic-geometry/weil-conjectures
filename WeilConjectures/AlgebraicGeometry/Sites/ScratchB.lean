module

public import WeilConjectures.AlgebraicGeometry.Sites.FilteredColimitSections

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] {K : Type (u + 1)} [SmallCategory K]
  {F : K ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {c : Cocone F}

set_option pp.universes true in
example (hc : IsColimit c) : True := by
  let E := colimit.cocone (F ⋙ sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let hE : IsColimit E := colimit.isColimit _
  let e := (Sheaf.isColimitSheafifyCocone E hE).coconePointUniqueUpToIso hc
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology (toSheafify X.smallEtaleTopology E.pt) := inferInstance
  have : IsIso e.hom.hom := inferInstance
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology e.hom.hom := inferInstance
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology (toSheafify X.smallEtaleTopology E.pt ≫ e.hom.hom) := inferInstance
  trivial

end AlgebraicGeometry.Scheme
