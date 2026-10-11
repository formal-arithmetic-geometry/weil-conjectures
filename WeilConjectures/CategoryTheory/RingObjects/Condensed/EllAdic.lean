/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic

/-!

# The condensed coefficient rings `ℤ_ℓ`, `ℚ_ℓ`, `𝒪_E` and `E`

Fix a prime `ℓ`. The four *topological* `ℓ`-adic coefficient rings are defined as condensed
rings by their sections on profinite sets, following Section 3 of
`WeilConjectures/RefactorInstruction.tex`:
```
ℤ̲_ℓ(S) := C(S, ℤ_ℓ),   ℚ̲_ℓ(S) := C(S, ℚ_ℓ),   𝒪̲_E(S) := C(S, 𝒪_E),   E̲(S) := C(S, E),
```
with restriction by precomposition and the pointwise ring operations: each is
`Profinite.continuousMapRingSheaf` of the corresponding topological ring. Here `E` is a subfield
of `ℚ̄_ℓ = PadicAlgCl ℓ`, given by an embedding `E → ℚ̄_ℓ`, with the topology restricted from
`ℚ̄_ℓ` (`PadicAlgCl.normedFieldOfAlgebra`), and `𝒪_E = PadicAlgCl.integers ℓ E` is its ring of
integers.

The familiar descriptions `ℤ̲_ℓ ≅ lim_n ℤ/ℓⁿ`, `ℚ̲_ℓ ≅ ℤ̲_ℓ[1/ℓ]`, `𝒪̲_E ≅ lim_n 𝒪_E/ϖⁿ` and
`E̲ ≅ 𝒪̲_E[1/ϖ]` are *not* definitions; they are comparison isomorphisms, to be proved later.
The condensed `ℚ̄_ℓ` is not of the form `C(-, T)` and is not treated here.

The inclusions `ℤ_ℓ → ℚ_ℓ → E`, `ℤ_ℓ → 𝒪_E → E` are continuous ring homomorphisms, so
postcomposition with them gives morphisms of condensed rings.

## Main definitions

* `Profinite.padicIntCondensedRing`, `Profinite.padicCondensedRing`: the condensed rings
  `ℤ̲_ℓ` and `ℚ̲_ℓ`.
* `Profinite.padicSubfieldCondensedRing`, `Profinite.padicIntegersCondensedRing`: the condensed
  rings `E̲` and `𝒪̲_E`.
* `Profinite.padicIntCondensedRingToPadicCondensedRing`,
  `Profinite.padicCondensedRingToPadicSubfieldCondensedRing`,
  `Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing` and
  `Profinite.padicIntCondensedRingToPadicIntegersCondensedRing`: the inclusions, as morphisms of
  condensed rings.

-/

@[expose] public section

universe u

open CategoryTheory

namespace Profinite

open AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### `ℤ_ℓ` and `ℚ_ℓ` -/

/-- The condensed ring `ℤ̲_ℓ`, with sections `ℤ̲_ℓ(S) = C(S, ℤ_ℓ)` for the `ℓ`-adic topology. -/
noncomputable abbrev padicIntCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  continuousMapRingSheaf ℤ_[ℓ]

/-- The condensed ring `ℚ̲_ℓ`, with sections `ℚ̲_ℓ(S) = C(S, ℚ_ℓ)` for the `ℓ`-adic topology. -/
noncomputable abbrev padicCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  continuousMapRingSheaf ℚ_[ℓ]

/-- The inclusion `ℤ̲_ℓ ⟶ ℚ̲_ℓ`, a morphism of condensed rings. -/
noncomputable def padicIntCondensedRingToPadicCondensedRing :
    padicIntCondensedRing.{u} ℓ ⟶ padicCondensedRing ℓ :=
  continuousMapRingSheafMap PadicInt.Coe.ringHom continuous_subtype_val

/-! ### Subfields `E` of `ℚ̄_ℓ` -/

section Subfield

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The condensed ring `E̲`, for a subfield `E` of `ℚ̄_ℓ` given by an embedding `E → ℚ̄_ℓ`, with
sections `E̲(S) = C(S, E)` for the topology of `E` restricted from `ℚ̄_ℓ`. -/
noncomputable abbrev padicSubfieldCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheaf E

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- The inclusion `ℚ̲_ℓ ⟶ E̲`, a morphism of condensed rings. -/
noncomputable def padicCondensedRingToPadicSubfieldCondensedRing :
    padicCondensedRing.{u} ℓ ⟶ padicSubfieldCondensedRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (algebraMap ℚ_[ℓ] E) (continuous_algebraMap_padic_of_algebra ℓ E)

end Subfield

/-! ### The rings of integers `𝒪_E` -/

section Integers

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The condensed ring `𝒪̲_E`, for a subfield `E` of `ℚ̄_ℓ` given by an embedding `E → ℚ̄_ℓ`,
with sections `𝒪̲_E(S) = C(S, 𝒪_E)` into the ring of integers `𝒪_E = PadicAlgCl.integers ℓ E`,
for the topology restricted from `ℚ̄_ℓ`. -/
noncomputable abbrev padicIntegersCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheaf (PadicAlgCl.integers ℓ E)

/-- The inclusion `𝒪̲_E ⟶ E̲`, a morphism of condensed rings. -/
noncomputable def padicIntegersCondensedRingToPadicSubfieldCondensedRing :
    padicIntegersCondensedRing.{u} ℓ E ⟶ padicSubfieldCondensedRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (PadicAlgCl.integers ℓ E).subtype continuous_subtype_val

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- The inclusion `ℤ̲_ℓ ⟶ 𝒪̲_E`, a morphism of condensed rings. -/
noncomputable def padicIntCondensedRingToPadicIntegersCondensedRing :
    padicIntCondensedRing.{u} ℓ ⟶ padicIntegersCondensedRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (padicIntToIntegers ℓ E) (continuous_padicIntToIntegers ℓ E)

end Integers

end Profinite
