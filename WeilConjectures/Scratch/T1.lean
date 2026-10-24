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
  [IsOpenImmersion f.left] [IsOpenImmersion f'.left]

/-- test -/
noncomputable abbrev hU : (Compactification.ofIsOpenImmersion f'.left).overObj ⟶
      (Compactification.ofIsOpenImmersion f.left).overObj :=
  Over.homMk g.left (by
    change g.left ≫ 𝟙 Y.left ≫ Y.hom = 𝟙 Y'.left ≫ Y'.hom
    simp [Over.w g])

set_option profiler true in
example (sq : IsPullback g' f' f g)
    (hi : CommSq g' (Compactification.ofIsOpenImmersion f'.left).overI
      (Compactification.ofIsOpenImmersion f.left).overI (hU (f := f) (f' := f') (g := g))) :
    Adjunction.exchangeLeft
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ (Compactification.ofIsOpenImmersion f.left).overI)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ (Compactification.ofIsOpenImmersion f'.left).overI)
        (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ hi.flip) =
      Adjunction.exchangeLeft
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f')
        (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq.flip) := rfl

end AlgebraicGeometry.ProEtale.CondensedRing
