module
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme
variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
example : HasColimitsOfShape ℕ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := inferInstance
example : HasColimitsOfShape ℕ (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) := inferInstance
end AlgebraicGeometry
