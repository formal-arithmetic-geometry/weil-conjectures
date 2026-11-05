/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion

/-!

# Reduction modulo `ℓⁿ` commutes with the pushforward along a closed immersion

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`k` a field of characteristic `p ≠ ℓ`. For a separated `k`-scheme of finite type `X` write
`red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧` for the reduction modulo `ℓⁿ`
(`ProEtale.boundedConstructibleIntegersModPowReduction`). For a morphism `d : Z ⟶ Y` this file
defines the comparison
```
γ : Rd_*^{𝒪_E} ⋙ red_Y ⟶ red_Z ⋙ Rd_*^{𝒪_E ⧸ ℓⁿ}
```
(`ProEtale.CondensedRing.boundedConstructibleLowerStarIntegersModPowReduction`), the mate of the
inverse of the pullback comparison
(`ProEtale.CondensedRing.boundedConstructibleUpperStarIntegersModPowReductionIso`) under the
adjunctions `d^* ⊣ Rd_*`, and proves that it is an isomorphism when `d` is a closed immersion
(`ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarIntegersModPowReduction`).

The proof checks the isomorphism after the jointly conservative pair of restrictions `d^*` and
`j^*`, where `j : U ⟶ Y` is the open complement of `d` (`AlgebraicGeometry.overOpenComplement`):

* after `d^*`, composing with the counit `d^* Rd_* ⟶ 𝟭` (an isomorphism, as `Rd_*` is fully
  faithful) gives the pullback comparison followed by the reduction of the counit;
* after `j^*`, both sides vanish, since `j^* Rd_* = 0` and the reduction commutes with `j^*` and
  preserves zero objects.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-! ### The open complement of a closed immersion -/

section OpenComplement

variable {S : Scheme.{u}} {Z Y : Over S} (d : Z ⟶ Y) [IsClosedImmersion d.left]

end OpenComplement

section OverField

variable {k : Type u} [Field k] {Z Y : Over (Spec (.of k))} (d : Z ⟶ Y) [IsClosedImmersion d.left]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

end OverField

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section ClosedImmersion

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

end ClosedImmersion

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [TopologicalSpace.NoetherianSpace Z.left]
  [TopologicalSpace.NoetherianSpace Y.left] (d : Z ⟶ Y)

/-- **Reduction modulo `ℓⁿ` and the pushforward** on bounded constructible complexes: the
comparison `γ : Rd_*^{𝒪_E} ⋙ red_Y ⟶ red_Z ⋙ Rd_*^{𝒪_E ⧸ ℓⁿ}`, the mate of the inverse of the
pullback comparison `boundedConstructibleUpperStarIntegersModPowReductionIso` under the
adjunctions `d^* ⊣ Rd_*`. -/
noncomputable def boundedConstructibleLowerStarIntegersModPowReduction :
    PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E d ⋙
        boundedConstructibleIntegersModPowReduction Y.left ℓ E n ⟶
      boundedConstructibleIntegersModPowReduction Z.left ℓ E n ⋙
        IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n d :=
  mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E d)
    (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n d)
    (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n d).inv

end AlgebraicGeometry.ProEtale.CondensedRing
