module
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData

open AlgebraicGeometry
namespace SheafOfModules.OpenTensorNormalization

universe u

example (X : Scheme.{u}) : Site .ordinary X = X.ProEt := rfl

end SheafOfModules.OpenTensorNormalization
