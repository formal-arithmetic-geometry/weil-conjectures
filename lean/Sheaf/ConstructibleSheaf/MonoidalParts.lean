module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
variable {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

/-- The tensor product of locally constant module sheaves is locally constant.
(blueprint: lem-weil-pbc-flc-tensor-locally-constant-part) -/
theorem IsLocallyConstantSheaf.tensorObj_part
    (hF : IsLocallyConstantSheaf F) (hG : IsLocallyConstantSheaf G) :
    IsLocallyConstantSheaf (F ⊗ G) := by sorry

/-- The tensor product of finite module sheaves is finite on geometric stalks.
(blueprint: lem-weil-pbc-flc-tensor-finite-part) -/
theorem IsFiniteSheaf.tensorObj_part
    (hF : IsFiniteSheaf F) (hG : IsFiniteSheaf G) :
    IsFiniteSheaf (F ⊗ G) := by sorry

end AlgebraicGeometry.Scheme
#print AlgebraicGeometry.Scheme.IsFiniteSheaf.tensorObj_part
#print AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.tensorObj_part
