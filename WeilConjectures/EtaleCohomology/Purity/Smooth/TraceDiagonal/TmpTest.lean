module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme
namespace Etale
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
  [IsSeparated f]
namespace TraceDiagonalDatum

noncomputable def t4 := projectionUnitIso Λ (pullback.diagonal f)

noncomputable def ty3 := (L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ])) ⋙
      (R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ]) ≅
      (derivedTensor (ModuleCat.{u + 1} Λ) (pullback f f)).obj
        ((R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ]).obj (derivedTensorUnit _ X))

set_option pp.explicit true
set_option pp.proofs false
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.width 100000
#check t4
#print ty3

end TraceDiagonalDatum
end Etale
end AlgebraicGeometry
