import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
import WeilConjectures.ConstructibleSheaf.MonoidalParts
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry
variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
  {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
#check (Scheme.pointSmallEtale s)
example : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).Monoidal := inferInstance
example (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) := F ⊗ G
end AlgebraicGeometry
