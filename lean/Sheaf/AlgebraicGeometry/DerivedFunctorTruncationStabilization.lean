/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Sheaf.Algebra.Homology.LowerTruncationStepTriangle
import Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Stabilization of derived cohomology on the lower truncation tower

Source: Stacks Project, Derived Categories of Schemes, Tag 08D4, proof of (2)
(blueprint: lem-pc-derived-functor-truncation-stabilization).
-/

@[expose] public section

universe u w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An additive functor with right derived functors vanishing in degrees at least `N`
on quasi-coherent modules induces isomorphisms on degree-`i` cohomology between successive
lower truncations whenever `n ≥ N - i`. The source truncation is `τ≥(-n) E` and the target
is `τ≥(-n+1) E = τ≥(-(n-1)) E`; the map is the standard t-structure's canonical one.
Source: Stacks Project, Tag 08D4, proof of (2)
(blueprint: lem-pc-derived-functor-truncation-stabilization).

Proof:
1. The successive lower-truncation triangle is
`H^(-n)(E)[n] → E_n → E_(n-1) → H^(-n)(E)[n+1]`
(`lem-pc-derived-lower-truncation-step-triangle`).
2. All three terms are bounded below. Apply the triangulated right derived functor
(`lem-weil-pbc-derived-direct-image-triangulated`) and the long exact cohomology sequence
(`lem-sf-derived-homology-long-exact`). The segment around the transition map has endpoint
terms `H^i(RF(H^(-n)(E)[n]))` and `H^(i+1)(RF(H^(-n)(E)[n]))`.
3. By `lem-sp-shift-identification`, these endpoints are respectively
`R^(i+n)F(H^(-n)(E))` and `R^(i+n+1)F(H^(-n)(E))`. Both indices are at least `N` because
`n ≥ N - i`. The cohomology sheaf is quasi-coherent since `E` belongs to `D_QCoh`, so both
endpoints vanish by the assumed uniform bound.
4. Exactness (`lem-sf-derived-homology-long-exact`) makes the transition map both monic
and epic, hence an isomorphism of abelian groups. -/
theorem isIso_rightDerivedFunctor_lowerTruncation_step
    (X : Scheme.{u})
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} AddCommGrpCat.{u}]
    [Abelian.HasKInjectiveResolutions (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasInjectiveResolutions (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤ AddCommGrpCat.{u})
    [F.Additive] (N : ℕ)
    (hvan : ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      M.IsQuasicoherent → ∀ p : ℕ, N ≤ p → IsZero ((F.rightDerived p).obj M))
    (E : schemeDerivedQCohCategory X) (i n : ℤ) (hn : (N : ℤ) - i ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
      (F.rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
          (-n) (-n + 1) (Int.le_add_one (le_refl (-n)))).app E.obj))) :=
  sorry

end AlgebraicGeometry
