/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-!

# The `ℓ`-adic coefficient rings

The `ℓ`-adic coefficient rings of the six-functor formalism on bounded constructible complexes
(Bhatt–Scholze, Section 6.8) are the condensed rings

* `𝒪̲_E` for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (`Profinite.padicIntegersRingObj ℓ E`);
* `E̲` for a finite extension `E` of `ℚ_ℓ` (`Profinite.continuousMapRingObj E`);
* `ℚ̲̄_ℓ` (`Profinite.padicAlgClRingObj ℓ`).

The type `Profinite.EllAdicCoefficient ℓ` lists them, and `Profinite.EllAdicCoefficient.ringObj`
is the corresponding commutative ring object of condensed abelian groups. The derived pushforward,
the derived tensor product and the derived hom preserve bounded constructible complexes for these
rings, and not for a general condensed ring, so the six functors on bounded constructible
complexes are defined for an `ℓ`-adic coefficient ring `Λ : Profinite.EllAdicCoefficient ℓ`.

-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace Profinite

/-- The `ℓ`-adic coefficient rings: `𝒪̲_E` and `E̲` for a finite extension `E` of `ℚ_ℓ`, and
`ℚ̲̄_ℓ`. The ring object itself is `EllAdicCoefficient.ringObj`. -/
inductive EllAdicCoefficient : ℕ → Type 1
  /-- `𝒪̲_E` for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
  | integers (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
      [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
      EllAdicCoefficient ℓ
  /-- `E̲` for a finite extension `E` of `ℚ_ℓ`. -/
  | field (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
      [FiniteDimensional ℚ_[ℓ] E] : EllAdicCoefficient ℓ
  /-- `ℚ̲̄_ℓ`. -/
  | algClosure (ℓ : ℕ) [Fact ℓ.Prime] : EllAdicCoefficient ℓ

namespace EllAdicCoefficient

variable {ℓ : ℕ}

/-- The condensed ring of an `ℓ`-adic coefficient ring, as a ring object of condensed abelian
groups. -/
@[coe]
noncomputable abbrev ringObj :
    EllAdicCoefficient ℓ → Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  | integers ℓ E => padicIntegersRingObj ℓ E
  | field _ E => continuousMapRingObj E
  | algClosure ℓ => padicAlgClRingObj ℓ

noncomputable instance : CoeOut (EllAdicCoefficient ℓ)
    (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  ⟨ringObj⟩

noncomputable instance monObj_ringObj : ∀ Λ : EllAdicCoefficient ℓ, MonObj (ringObj.{u} Λ)
  | integers ℓ E => inferInstanceAs (MonObj (padicIntegersRingObj ℓ E))
  | field _ E => inferInstanceAs (MonObj (continuousMapRingObj E))
  | algClosure ℓ => inferInstanceAs (MonObj (padicAlgClRingObj ℓ))

instance isCommMonObj_ringObj : ∀ Λ : EllAdicCoefficient ℓ, IsCommMonObj (ringObj.{u} Λ)
  | integers ℓ E => inferInstanceAs (IsCommMonObj (padicIntegersRingObj ℓ E))
  | field _ E => inferInstanceAs (IsCommMonObj (continuousMapRingObj E))
  | algClosure ℓ => inferInstanceAs (IsCommMonObj (padicAlgClRingObj ℓ))

end EllAdicCoefficient

end Profinite
