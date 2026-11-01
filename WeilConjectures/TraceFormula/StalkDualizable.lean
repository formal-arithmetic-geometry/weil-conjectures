/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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

/-!

# Stalks of homology sheaves of bounded constructible complexes are dualizable

Let `K` be a bounded constructible complex of `ℚ̄_ℓ`-sheaves on a separated scheme `X` of finite
type over a field `k`, and `x̄ : Spec Ω ⟶ X` a geometric point, `Ω` algebraically closed. The
stalk `x̄^* Hʲ(K)` of each homology sheaf is a dualizable object of the symmetric monoidal
category `Mod_{Spec Ω}` of `ℚ̲̄_ℓ`-modules on the pro-étale site of `Spec Ω`
(`ProEtale.CondensedRing.nonempty_hasRightDual_upperStar_homology`): `Hʲ(K)` is constructible,
so its stalk `x̄^* Hʲ(K)` is a finite direct sum of copies of the unit `ℚ̲̄_ℓ`
(`ProEtale.CondensedRing.isFiniteFree_upperStar_homology`), and an object with a basis of copies
of the unit is its own right dual (`CategoryTheory.MonoidalCategory.UnitBasis.exactPairing`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Stalks of homology sheaves of bounded constructible complexes are dualizable**: for a
bounded constructible complex `K` of `ℚ̄_ℓ`-sheaves on `X` and a geometric point
`x̄ : Spec Ω ⟶ X`, `Ω` algebraically closed, the stalk `x̄^* Hʲ(K)` has a right dual in
`Mod_{Spec Ω}`: it is finite free (`ProEtale.CondensedRing.isFiniteFree_upperStar_homology`),
hence its own right dual. -/
theorem nonempty_hasRightDual_upperStar_homology
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (j : ℤ) {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.left) :
    Nonempty (HasRightDual ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
      ((DerivedCategory.homologyFunctor _ j).obj K.obj))) := by
  obtain ⟨n, ⟨b⟩⟩ := (isFiniteFree_upperStar_homology ℓ (Field.toIsField Ω)
    IsField.isSepClosed_toField K j x).exists_unitBasis
  exact ⟨{ rightDual := _, exact := b.exactPairing }⟩

end AlgebraicGeometry.ProEtale.CondensedRing
