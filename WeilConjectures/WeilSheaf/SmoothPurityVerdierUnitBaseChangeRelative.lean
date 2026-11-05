/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityVerdierUnitIso

/-!
# The exceptional base change map at the unit over an arbitrary base, through Nagata (relative A1')

Let `k` be a finite field with algebraic closure `k̄`, and `f : X ⟶ Y` a morphism of separated
`k`-schemes of finite type, with geometric fibre `f̄ : X̄ ⟶ Ȳ`. Factor `f` through the
compactification `X --j--> X^c --p--> Y` defining `Rf_!` (`compactificationOverField f`): `j` is
an open immersion and `p` is proper over `Y`. The pasting of the base change of the extension by
zero along `j` with proper base change for `p` is a compact-support base change isomorphism for
`f` (`geometricFiberLowerShriekBaseChangeVerdier`), and its exceptional base change map at the
unit `πX^* Rf^! ℚ̄_ℓ ⟶ Rf̄^! ℚ̄_ℓ` is invertible
(`isIso_smoothUnitBaseChange_geometricFiberLowerShriekBaseChangeVerdier`): this is
`WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangePoint` with the point replaced by `Y`,
the proper piece being supplied by Verdier duality and the endomorphism trick
(`isIso_upperShriekBaseChangeOfMap_app_unit_geometricFiber`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Relative

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The open immersion `j : X ⟶ X^c` of the compactification of `f` over `Y` defining `Rf_!`. -/
abbrev verdierNagataOpenImmersion : X ⟶ (compactificationOverField f).overObj :=
  (compactificationOverField f).overI

/-- The proper morphism `p : X^c ⟶ Y` of the compactification of `f` over `Y` defining `Rf_!`. -/
abbrev verdierNagataProper : (compactificationOverField f).overObj ⟶ Y :=
  (compactificationOverField f).overG

omit [Finite k] [Fact (ringChar k).Prime] in
lemma verdierNagataOpenImmersion_comp_verdierNagataProper :
    verdierNagataOpenImmersion f ≫ verdierNagataProper f = f :=
  (compactificationOverField f).overI_overG

omit [Fact (ringChar k).Prime] in
lemma geometricFiberOverMap_verdierNagataOpenImmersion_comp_verdierNagataProper :
    geometricFiberOverMap (verdierNagataOpenImmersion f) ≫
        geometricFiberOverMap (verdierNagataProper f) =
      geometricFiberOverMap f := by
  rw [← geometricFiberOverMap_comp, verdierNagataOpenImmersion_comp_verdierNagataProper]

/-- **The compact-support base change isomorphism of `f : X ⟶ Y` along `k ⟶ k̄`**, through the
compactification `X --j--> X^c --p--> Y` defining `Rf_!`: the pasting of the base change of the
extension by zero along `j` (`openImmersionLowerShriekBaseChangeOfMap`) with proper base change
along `p` (`properLowerShriekBaseChangeOfMap`), transported along `j ≫ p = f`. -/
def geometricFiberLowerShriekBaseChangeVerdier :
    boundedConstructibleLowerShriek l f ⋙
        boundedConstructibleUpperStarOfMap l (X := Y) (Y := geometricFiberOver Y)
          Y.hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l (X := X) (Y := geometricFiberOver X)
        X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l (geometricFiberOverMap f) :=
  transportLowerShriekBaseChange l (verdierNagataOpenImmersion_comp_verdierNagataProper f)
    (geometricFiberOverMap_verdierNagataOpenImmersion_comp_verdierNagataProper f)
    (pasteLowerShriekBaseChange l (verdierNagataOpenImmersion f) (verdierNagataProper f)
      (geometricFiberOverMap (verdierNagataOpenImmersion f))
      (geometricFiberOverMap (verdierNagataProper f))
      (openImmersionLowerShriekBaseChangeOfMap l
        (isPullback_geometricFiberOverMap (verdierNagataOpenImmersion f)))
      (properLowerShriekBaseChangeOfMap l (verdierNagataProper f)
        (geometricFiberOverMap (verdierNagataProper f))
        (isPullback_geometricFiberOverMap (verdierNagataProper f))))

/-- **Relative A1'.** For a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type (`k`
finite) and the compact-support base change isomorphism along `k ⟶ k̄` attached to the
compactification defining `Rf_!` (`geometricFiberLowerShriekBaseChangeVerdier`), the exceptional
base change map at the unit `πX^* Rf^! ℚ̄_ℓ ⟶ Rf̄^! ℚ̄_ℓ` is invertible, for any isomorphism
`e : πY^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`. No smoothness or properness of `f` is needed. -/
theorem isIso_smoothUnitBaseChange_geometricFiberLowerShriekBaseChangeVerdier
    (e : (boundedConstructibleUpperStarOfMap l (X := Y) (Y := geometricFiberOver Y)
      Y.hom.geometricFiberProj).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l f (geometricFiberOverMap f)
      (geometricFiberLowerShriekBaseChangeVerdier l f) e) := by
  -- the proper piece: Verdier duality and the endomorphism trick
  have := isIso_upperShriekBaseChangeOfMap_app_unit_geometricFiber l (verdierNagataProper f)
  have : IsIso (smoothUnitBaseChange l (verdierNagataProper f)
      (geometricFiberOverMap (verdierNagataProper f))
      (properLowerShriekBaseChangeOfMap l (verdierNagataProper f)
        (geometricFiberOverMap (verdierNagataProper f))
        (isPullback_geometricFiberOverMap (verdierNagataProper f))) e) :=
    isIso_smoothUnitBaseChange_of_isIso_upperShriekBaseChangeOfMap l (verdierNagataProper f)
      (geometricFiberOverMap (verdierNagataProper f))
      (isPullback_geometricFiberOverMap (verdierNagataProper f)) e
  -- the open-immersion piece
  have := isIso_upperShriekMateOfMap_app_of_isOpenImmersion' l (verdierNagataOpenImmersion f)
    (geometricFiberOverMap (verdierNagataOpenImmersion f))
    (openImmersionLowerShriekBaseChangeOfMap l
      (isPullback_geometricFiberOverMap (verdierNagataOpenImmersion f)))
    (isPullback_geometricFiberOverMap (verdierNagataOpenImmersion f)).w
    ((boundedConstructibleUpperShriek l (verdierNagataProper f)).obj (𝟙_ _))
  rw [geometricFiberLowerShriekBaseChangeVerdier, isIso_smoothUnitBaseChange_transport_iff]
  exact isIso_smoothUnitBaseChange_paste l _ _ _ _ _ _ e

end Relative

end AlgebraicGeometry.ProEtale.CondensedRing
