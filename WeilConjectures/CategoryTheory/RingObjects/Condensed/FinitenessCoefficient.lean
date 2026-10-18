/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-!

# Coefficient rings of Deligne's finiteness theorems

The derived pushforward `Rf_*` along a morphism of separated schemes of finite type over a field
`k` of characteristic `p ≠ ℓ` carries bounded constructible complexes to bounded constructible
complexes only for suitable coefficient rings: for the constant discrete ring `𝔽_p` and the
affine line over an algebraically closed field of characteristic `p`, the Artin–Schreier sequence
gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`, which is infinite. The class
`IsFinitenessCoefficient ℓ Λ` singles out the coefficient rings for which it holds (Deligne's
finiteness theorems, SGA 4½ [Th. finitude]; Bhatt–Scholze, Section 6.8):

* the `ℓ`-adic rings of the blueprint, `E̲` for a finite extension `E` of `ℚ_ℓ`
  (`Profinite.continuousMapRingObj E`), `𝒪̲_E` for a finite subextension `E ⊆ ℚ̄_ℓ`
  (`Profinite.padicIntegersRingObj ℓ E`) and `ℚ̲̄_ℓ` (`Profinite.padicAlgClRingObj ℓ`);
* `𝒪̲_E` given as the closed unit ball `O` of a finite normed extension `E` of `ℚ_ℓ`
  (`Profinite.continuousMapRingObj O`);
* the torsion rings `T̲` of a finite discrete ring `T` killed by a power of `ℓ`.

The subclass `IsEllAdicFinitenessCoefficient ℓ Λ` leaves out the torsion rings: it singles out the
`ℓ`-adic rings, for which the bounded constructible complexes are moreover stable under the
derived tensor product and the derived internal hom.

The ring object structure is an index of the class, so that an instance cannot certify another
multiplication on the same condensed abelian group.

-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The commutative condensed rings `Λ` for which the derived pushforward along morphisms of
separated schemes of finite type over a field of characteristic `≠ ℓ` preserves bounded
constructible complexes (Deligne's finiteness theorems): `E̲`, `𝒪̲_E` and `ℚ̲̄_ℓ` for finite
extensions `E` of `ℚ_ℓ`, and `T̲` for a finite discrete ring `T` killed by a power of `ℓ`. -/
class inductive IsFinitenessCoefficient (ℓ : ℕ) [Fact ℓ.Prime] :
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) → [MonObj Λ] → Prop
  /-- `E̲` for a finite extension `E` of `ℚ_ℓ`. -/
  | continuous (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
      IsFinitenessCoefficient ℓ (Profinite.continuousMapRingObj E)
  /-- `𝒪̲_E` for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
  | integral (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
      [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
      IsFinitenessCoefficient ℓ (Profinite.padicIntegersRingObj ℓ E)
  /-- `ℚ̲̄_ℓ`. -/
  | algebraicClosure : IsFinitenessCoefficient ℓ (Profinite.padicAlgClRingObj ℓ)
  /-- `𝒪̲_E` for the closed unit ball `O` of a finite normed extension `E` of `ℚ_ℓ`. -/
  | unitBall (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
      (O : Subring E) (hO : ∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1) :
      IsFinitenessCoefficient ℓ (Profinite.continuousMapRingObj O)
  /-- `T̲` for a finite discrete ring `T` with `ℓ ^ n = 0` in `T`. -/
  | torsion (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
      [DiscreteTopology T] [Finite T] (n : ℕ) (h : (ℓ : T) ^ n = 0) :
      IsFinitenessCoefficient ℓ (Profinite.continuousMapRingObj T)

attribute [instance] IsFinitenessCoefficient.continuous IsFinitenessCoefficient.integral
  IsFinitenessCoefficient.algebraicClosure

/-- The `ℓ`-adic coefficient rings of the blueprint: `E̲` and `𝒪̲_E` for a finite extension `E` of
`ℚ_ℓ`, and `ℚ̲̄_ℓ`. For them, and unlike for the torsion rings of `IsFinitenessCoefficient`, the
bounded constructible complexes are also stable under the derived tensor product and the derived
internal hom (for `Λ = ℤ/4` and `ℓ = 2`, `Tor` and `Ext` of `ℤ/2` over `ℤ/4` are nonzero in every
degree). The prime `ℓ` is an `outParam`: it is determined by `Λ`. -/
class inductive IsEllAdicFinitenessCoefficient (ℓ : outParam ℕ) :
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) → [MonObj Λ] → Prop
  /-- `E̲` for a finite extension `E` of `ℚ_ℓ`. -/
  | continuous [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
      [FiniteDimensional ℚ_[ℓ] E] :
      IsEllAdicFinitenessCoefficient ℓ (Profinite.continuousMapRingObj E)
  /-- `𝒪̲_E` for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
  | integral [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
      [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
      IsEllAdicFinitenessCoefficient ℓ (Profinite.padicIntegersRingObj ℓ E)
  /-- `ℚ̲̄_ℓ`. -/
  | algebraicClosure [Fact ℓ.Prime] :
      IsEllAdicFinitenessCoefficient ℓ (Profinite.padicAlgClRingObj ℓ)
  /-- `𝒪̲_E` for the closed unit ball `O` of a finite normed extension `E` of `ℚ_ℓ`. -/
  | unitBall [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
      [FiniteDimensional ℚ_[ℓ] E] (O : Subring E) (hO : ∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1) :
      IsEllAdicFinitenessCoefficient ℓ (Profinite.continuousMapRingObj O)

attribute [instance] IsEllAdicFinitenessCoefficient.integral
  IsEllAdicFinitenessCoefficient.algebraicClosure

-- The prime `ℓ` of `E̲` occurs only in the instance `NormedAlgebra ℚ_[ℓ] E`; it is found from the
-- local instance `Fact ℓ.Prime`, so the synthesis order is not the default one.
set_option synthInstance.checkSynthOrder false in
attribute [instance] IsEllAdicFinitenessCoefficient.continuous

/-- An `ℓ`-adic coefficient ring is a coefficient ring of Deligne's finiteness theorems. -/
instance (priority := 100) IsEllAdicFinitenessCoefficient.isFinitenessCoefficient (ℓ : ℕ)
    [Fact ℓ.Prime] (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [h : IsEllAdicFinitenessCoefficient ℓ Λ] : IsFinitenessCoefficient ℓ Λ := by
  cases h with
  | continuous E => exact .continuous E
  | integral E => exact .integral E
  | algebraicClosure => exact .algebraicClosure
  | unitBall E O hO => exact .unitBall E O hO

end AlgebraicGeometry.ProEtale.CondensedRing
