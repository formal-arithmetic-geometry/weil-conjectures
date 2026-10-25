/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.NumberTheory.Padics.IntegersModPow

/-!

# The condensed rings `(𝒪_E ⧸ ℓⁿ)̲` and the reductions `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲`

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a subfield with ring of integers `𝒪_E`. The discrete rings
`𝒪_E ⧸ ℓⁿ = PadicAlgCl.integersModPow ℓ E n` give condensed rings
```
(𝒪_E ⧸ ℓⁿ)̲(S) := C(S, 𝒪_E ⧸ ℓⁿ),
```
(`Profinite.integersModPowRingObj`), and the reduction `𝒪_E → 𝒪_E ⧸ ℓⁿ`, which is continuous
(`PadicAlgCl.continuous_integersModPowMk`), induces by postcomposition a morphism of condensed
rings `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲` (`Profinite.padicIntegersRingObjToIntegersModPow`).

For `E` finite over `ℚ_ℓ`, the ring `𝒪_E ⧸ ℓⁿ` is finite (`PadicAlgCl.finite_integersModPow`):
it is the image of the compact space `𝒪_E` under a continuous map to a discrete space. Hence
`(𝒪_E ⧸ ℓⁿ)̲` is a torsion coefficient ring of Deligne's finiteness theorems
(`ProEtale.CondensedRing.isFinitenessCoefficient_integersModPowRingObj`).

## Main definitions

* `Profinite.integersModPowRingObj`: the condensed ring `(𝒪_E ⧸ ℓⁿ)̲`, as a commutative ring
  object of condensed abelian groups.
* `Profinite.padicIntegersRingObjToIntegersModPow`: the reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲`, a
  morphism of ring objects.

-/

@[expose] public section

universe u

open CategoryTheory MonObj

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- `ℓⁿ = 0` in `𝒪_E ⧸ ℓⁿ`. -/
lemma natCast_pow_eq_zero_integersModPow (n : ℕ) : (ℓ : integersModPow ℓ E n) ^ n = 0 := by
  rw [← map_natCast (integersModPowMk ℓ E n), ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

/-- For `E` finite over `ℚ_ℓ`, the ring `𝒪_E ⧸ ℓⁿ` is finite: it is the image of the compact
space `𝒪_E` under the continuous reduction map to a discrete space. -/
instance finite_integersModPow [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] (n : ℕ) : Finite (integersModPow ℓ E n) := by
  let := normedFieldOfAlgebra ℓ E
  have := compactSpace_integers ℓ E
  rw [← Set.finite_univ_iff, ← (integersModPowMk_surjective ℓ E n).range_eq]
  exact (isCompact_range (continuous_integersModPowMk ℓ E n)).finite_of_discrete

end PadicAlgCl

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ)

/-- The condensed ring `(𝒪_E ⧸ ℓⁿ)̲`, with sections `C(S, 𝒪_E ⧸ ℓⁿ)` for the discrete topology,
as a ring object of condensed abelian groups. -/
noncomputable abbrev integersModPowRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  continuousMapRingObj (PadicAlgCl.integersModPow ℓ E n)

/-- The condensed ring `(𝒪_E ⧸ ℓⁿ)̲` is a commutative ring object of condensed abelian groups. -/
instance isCommMonObj_integersModPowRingObj : IsCommMonObj (integersModPowRingObj.{u} ℓ E n) :=
  isCommMonObj_continuousMapRingObj (PadicAlgCl.integersModPow ℓ E n)

/-- The reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲`, a morphism of condensed rings: postcomposition with the
continuous reduction map `𝒪_E → 𝒪_E ⧸ ℓⁿ`. -/
noncomputable def padicIntegersCondensedRingToIntegersModPow :
    padicIntegersCondensedRing.{u} ℓ E ⟶
      continuousMapRingSheaf (PadicAlgCl.integersModPow ℓ E n) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (PadicAlgCl.integersModPowMk ℓ E n)
    (PadicAlgCl.continuous_integersModPowMk ℓ E n)

/-- The reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲` of ring objects of condensed abelian groups: the abelian
sheaf morphism underlying `Profinite.padicIntegersCondensedRingToIntegersModPow`. -/
noncomputable def padicIntegersRingObjToIntegersModPow :
    padicIntegersRingObj.{u} ℓ E ⟶ integersModPowRingObj ℓ E n :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicIntegersCondensedRingToIntegersModPow ℓ E n)

instance : IsMonHom (padicIntegersRingObjToIntegersModPow.{u} ℓ E n) :=
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (padicIntegersCondensedRingToIntegersModPow.{u} ℓ E n)))

/-- On sections over a profinite set `S`, the reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲` is
postcomposition with the reduction map. -/
lemma padicIntegersRingObjToIntegersModPow_hom_app_apply (S : Profinite.{u}ᵒᵖ) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    ∀ a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E),
      (padicIntegersRingObjToIntegersModPow ℓ E n).hom.app S a =
        ULift.up ((⟨PadicAlgCl.integersModPowMk ℓ E n,
          PadicAlgCl.continuous_integersModPowMk ℓ E n⟩ :
            C(PadicAlgCl.integers ℓ E, PadicAlgCl.integersModPow ℓ E n)).comp a.down) :=
  fun _ ↦ rfl

end Profinite

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- For `E` finite over `ℚ_ℓ`, the condensed ring `(𝒪_E ⧸ ℓⁿ)̲` is a torsion coefficient ring of
Deligne's finiteness theorems: `𝒪_E ⧸ ℓⁿ` is a finite discrete ring killed by `ℓⁿ`. -/
instance isFinitenessCoefficient_integersModPowRingObj (n : ℕ) :
    IsFinitenessCoefficient ℓ (Profinite.integersModPowRingObj.{u} ℓ E n) :=
  .torsion (PadicAlgCl.integersModPow ℓ E n) n
    (PadicAlgCl.natCast_pow_eq_zero_integersModPow ℓ E n)

end AlgebraicGeometry.ProEtale.CondensedRing
