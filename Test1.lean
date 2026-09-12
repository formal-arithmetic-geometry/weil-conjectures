module
public import WeilConjectures.AlgebraicGeometry.Modules.Monoidal
public import WeilConjectures.AlgebraicGeometry.TwistingSheaf
@[expose] public section
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry
variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (d e : ℤ)

-- does the monoidal structure exist on the `ringCatSheaf` spelling?
example : MonoidalCategory (PresheafOfModules.{0} (Proj 𝒜).ringCatSheaf.obj) := by infer_instance

end AlgebraicGeometry
