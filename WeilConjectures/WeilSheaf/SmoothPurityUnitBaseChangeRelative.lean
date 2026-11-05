module

public import WeilConjectures.WeilSheaf.SmoothPurityRelativeUnitIso

/-! Relative exceptional base change through the chosen Nagata compactification. -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The open factor in the chosen compactification of a relative morphism. -/
abbrev relativeNagataOpen : X ⟶ (compactificationOverField f).overObj :=
  (compactificationOverField f).overI

/-- The proper factor in the chosen compactification of a relative morphism. -/
abbrev relativeNagataProper : (compactificationOverField f).overObj ⟶ Y :=
  (compactificationOverField f).overG

lemma relativeNagata_comp : relativeNagataOpen f ≫ relativeNagataProper f = f :=
  (compactificationOverField f).overI_overG

lemma relativeNagata_geometricFiber_comp :
    geometricFiberOverMap (relativeNagataOpen f) ≫
      geometricFiberOverMap (relativeNagataProper f) = geometricFiberOverMap f := by
  rw [← geometricFiberOverMap_comp, relativeNagata_comp]

/-- The canonical compact-support exchange obtained by pasting the specified open exchange
and proper base change for the compactification defining the relative lower shriek. -/
def geometricFiberLowerShriekBaseChangeRelative :
    boundedConstructibleLowerShriek l f ⋙
        boundedConstructibleUpperStarOfMap l (X := Y) (Y := geometricFiberOver Y)
          Y.hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l (X := X) (Y := geometricFiberOver X)
        X.hom.geometricFiberProj ⋙ boundedConstructibleLowerShriek l (geometricFiberOverMap f) :=
  transportLowerShriekBaseChange l (relativeNagata_comp f) (relativeNagata_geometricFiber_comp f)
    (pasteLowerShriekBaseChange l (relativeNagataOpen f) (relativeNagataProper f)
      (geometricFiberOverMap (relativeNagataOpen f))
      (geometricFiberOverMap (relativeNagataProper f))
      (openImmersionLowerShriekBaseChangeOfMap l
        (isPullback_geometricFiberOverMap (relativeNagataOpen f)))
      (properLowerShriekBaseChangeOfMap l (relativeNagataProper f)
        (geometricFiberOverMap (relativeNagataProper f))
        (isPullback_geometricFiberOverMap (relativeNagataProper f))))

/-- Relative A1': the exceptional base change at the unit is invertible over an arbitrary
finite-type separated base scheme, for the exchange of the chosen compactification. -/
theorem isIso_smoothUnitBaseChange_geometricFiberLowerShriekBaseChangeRelative
    (e : (boundedConstructibleUpperStarOfMap l (X := Y) (Y := geometricFiberOver Y)
      Y.hom.geometricFiberProj).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l f (geometricFiberOverMap f)
      (geometricFiberLowerShriekBaseChangeRelative l f) e) := by
  have := purity_isIso_upperShriekBaseChangeOfMap_unit_geometricFiber l (relativeNagataProper f)
  have := isIso_smoothUnitBaseChange_of_isIso_upperShriekBaseChangeOfMap l
    (relativeNagataProper f) (geometricFiberOverMap (relativeNagataProper f))
    (isPullback_geometricFiberOverMap (relativeNagataProper f)) e
  have := isIso_upperShriekMateOfMap_app_of_isOpenImmersion' l (relativeNagataOpen f)
    (geometricFiberOverMap (relativeNagataOpen f))
    (openImmersionLowerShriekBaseChangeOfMap l
      (isPullback_geometricFiberOverMap (relativeNagataOpen f)))
    (isPullback_geometricFiberOverMap (relativeNagataOpen f)).w
    ((boundedConstructibleUpperShriek l (relativeNagataProper f)).obj (𝟙_ _))
  rw [geometricFiberLowerShriekBaseChangeRelative, isIso_smoothUnitBaseChange_transport_iff]
  exact isIso_smoothUnitBaseChange_paste l _ _ _ _ _ _ e

end AlgebraicGeometry.ProEtale.CondensedRing
