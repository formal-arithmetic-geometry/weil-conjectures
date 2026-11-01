/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Sections
public import WeilConjectures.WeilObject.Sheaf.Stalk

/-!
# The Galois action on sections of module objects

The Galois action `x^* M ⟶ σ^* x^* M ≅ (σ ≫ x)^* M = x^* M`, for a trivialization `σ^*
≅ 𝟭` which is the unit comparison at the unit, pulls back global sections.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {S T : Scheme.{u}}

/-- The Galois action `x̄^* M ⟶ σ^* x̄^* M ≅ (σ ≫ x̄)^* M = x̄^* M`,
for a trivialization
`τ : σ^* ≅ 𝟭` which is the unit comparison at the unit,
sends a global section to its pullback
along `σ`. -/
lemma comp_inv_app_comp_upperStarComp_inv_app_eq_upperStarSectionMap
    (σ : S ⟶ S) (x : S ⟶ T) (h : σ ≫ x = x)
    (τ : (σ)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _)
    (hτ : τ.inv.app 𝟙ₘ = (Functor.Monoidal.εIso (σ)^*⟦Profinite.padicAlgClRingObj
        ℓ⟧).hom)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))
    (v : 𝟙ₘ ⟶ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) :
    v ≫ τ.inv.app ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x).inv.app M ≫
        (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) h).hom.app M =
      upperStarSectionMap (Profinite.padicAlgClRingObj ℓ) σ h M v := by
  have hn := τ.inv.naturality v
  rw [Functor.id_map] at hn
  rw [reassoc_of% hn, hτ, upperStarEqToIso_hom_app, upperStarSectionMap]

end AlgebraicGeometry.ProEtale.CondensedRing
