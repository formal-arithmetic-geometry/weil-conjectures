module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeProper

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [IsProper f.left] [IsProper f'.left]

set_option profiler true in
example (sq : IsPullback g' f' f g) :
    boundedConstructibleBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ
      (isPullback_ofIsProper_overG sq).toCommSq =
    boundedConstructibleBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq := rfl

end AlgebraicGeometry.ProEtale.CondensedRing
