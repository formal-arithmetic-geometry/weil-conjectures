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
gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`, which is infinite. Already the bounded constructible
complexes form a triangulated subcategory only for coherent coefficient rings. The class
`IsFinitenessCoefficient ℓ Λ` singles out the coefficient rings for which these hold (Deligne's
finiteness theorems, SGA 4½ [Th. finitude]; Bhatt–Scholze, Section 6.8):

* the `ℓ`-adic rings of the blueprint, `E̲` for a finite extension `E` of `ℚ_ℓ`
  (`Profinite.continuousMapRingObj E`), `𝒪̲_E` for a finite subextension `E ⊆ ℚ̄_ℓ`
  (`Profinite.padicIntegersRingObj ℓ E`) and `ℚ̲̄_ℓ` (`Profinite.padicAlgClRingObj ℓ`);
* `𝒪̲_E` given as the closed unit ball `O` of a finite normed extension `E` of `ℚ_ℓ`
  (`Profinite.continuousMapRingObj O`);
* the torsion rings `T̲` of a finite discrete ring `T` killed by a power of `ℓ`.

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

end AlgebraicGeometry.ProEtale.CondensedRing
