module

public import WeilConjectures.AlgebraicGeometry.Modules.Determinant

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules} {Y : X.Opens} {I : Type u} [Fintype I] [DecidableEq I]
  (e : M.over Y ≅ SheafOfModules.free I)

example {W : X.Opens} (h : W ≤ Y) (a : Γ(X, W)) (s : Γ(M, W)) :
    sectionsLinearEquivOfOverIsoFree e h (a • s) = a • sectionsLinearEquivOfOverIsoFree e h s := by
  rw [map_smul]

end AlgebraicGeometry.Scheme.Modules
