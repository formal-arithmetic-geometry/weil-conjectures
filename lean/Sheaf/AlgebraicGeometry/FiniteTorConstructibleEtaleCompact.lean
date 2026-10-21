/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.CategoryTheory.CompactObject

import Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Compactness of finite-Tor constructible étale complexes

Source: Weil conjectures blueprint, main-20261015, `sec-six-functors-basics`,
`sk-prop-ctf-finite-compact/sk-prop-ctf-finite-compact-etale.md` and its proof,
Generators, Formula and Sums (blueprint: det-ctf-finite-compact-etale).

The category is the ordinary unbounded derived category of constant-coefficient module
sheaves. Coproducts use the module-value indexing universe `u + 1`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Every bounded constructible complex of finite Tor amplitude over a finite commutative
ℓ-primary coefficient ring is compact on a finite-type scheme over the standing field.
Compactness is bijectivity of the canonical direct-sum comparison on Hom groups for every
family indexed by a type in universe `u + 1`, including the empty family.

Proof: apply the compactness clause of `lem-pur-etale-finite-ring-compact-generators`
(`AlgebraicGeometry.Etale.finiteRing_compactGenerators`) with `k = D.k`, `T = X`, `C = A`.
The field `D.k` is algebraically closed. Since ℓ is prime and distinct from the
characteristic `D.p`, it is invertible in `D.k`. The two structure-morphism instances
express finite type; separatedness is not needed. The coefficient ring is finite,
commutative, and killed by a power of ℓ. The bounded constructibility and Tor-amplitude
predicates are exactly those in that theorem. Its coproduct structure and compactness
clause give the assertion, also for the empty scheme, zero ring, and zero complex.

Source: blueprint main-20261015, `sk-prop-ctf-finite-compact-etale.md` and its proof,
Generators, Formula and Sums; Stacks Project, Tags 0F11 and 0D6J
(blueprint: det-ctf-finite-compact-etale). -/
theorem finiteTorConstructible_etale_compact
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) (hℓprime : Nat.Prime ℓ) (hℓne : ℓ ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ℓ : A) ^ r = 0) :
    ∃ hcoprod : HasCoproducts.{u + 1} (DerivedCategoryModule A X),
      ∀ C : DerivedCategoryModule A X,
        DerivedCategory.isBoundedConstructible A X C →
        (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b C) →
        @IsCompactObject (DerivedCategoryModule A X) _ _ hcoprod C := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hcard : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hcard
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hunit : IsUnit (ℓ : D.k) := by
    apply isUnit_iff_ne_zero.mpr
    exact CharP.cast_ne_zero_of_ne_of_prime D.k hℓprime hℓne.symm
  obtain ⟨hcoprod, _, hcompact, _⟩ :=
    finiteRing_compactGenerators ℓ hℓprime hunit (X ↘ Spec (CommRingCat.of D.k)) hA
  exact ⟨hcoprod, fun C hC hTor ↦ hcompact C ⟨hC, hTor⟩⟩

end AlgebraicGeometry.Etale
