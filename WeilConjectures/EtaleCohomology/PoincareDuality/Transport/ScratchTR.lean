import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
open CategoryTheory
universe u
variable (Λ : Type (u+1)) [CommRing Λ] (X : AlgebraicGeometry.Scheme.{u})
#synth Linear Λ (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ))
#synth (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ)).Linear Λ
#synth (constantSheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ)).Linear Λ
example : (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u+1} Λ)).Linear Λ := by infer_instance
