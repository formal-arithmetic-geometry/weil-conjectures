/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc

/-! # Sharp Tor amplitude at field coefficients on qcqs schemes

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-coefficients-constructible/sec-n-constructible/
sec-local-structure-of-integral-constructible-complexes/sk-prop-integral-criterion/
lem-integral-ctf-equals-bc.md, clause (2), field cases;
used for the bounded constructible input of Fourier inversion, lem-fd-inversion.
(blueprint: lem-weil-field-tor-amplitude).

The constructibility convention is finite constant scalar local models. All objects
belong to the ordinary uncompleted derived category of internal coefficient modules.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Over either condensed field coefficient, a bounded constructible complex on a qcqs
scheme has Tor amplitude in every ordered interval containing its cohomology. In
particular it has finite Tor amplitude, and Dctf equals Dbc as full subcategories.
The degree-zero modules tested by `torAmplitudeIn` are arbitrary coefficient modules.

Source: latest blueprint lem-integral-ctf-equals-bc, clause (2), field cases, and
its proof, Complexes paragraph (blueprint: lem-weil-field-tor-amplitude).

Proof:
1. Apply the field clause of lem-integral-ctf-equals-bc with X = Y. The qcqs hypothesis,
condensed E or finite-subextension-valued Qlb, and finite constant local-model convention
are exactly those of that theorem. Its sharp field interval is [a,b] for every test
module in degree zero, without a completeness or constructibility restriction.
2. By det-def-sfb-constructible-tor-amplitude, clause (2), boundedness encloses all
nonzero cohomology in an ordered finite integer interval [a,b]. If there is no nonzero
cohomology, take a = b = 0. Step 1 gives Tor amplitude in that interval, hence finite
Tor amplitude by clause (3).
3. Clause (4) of det-def-sfb-constructible-tor-amplitude defines Dctf as the full
subcategory of Dbc cut out by finite Tor amplitude. Step 2 makes this condition hold
for every Dbc object; the converse inclusion is definitional. Equality of the object
predicates gives equality of the full subcategories with their ambient morphisms. -/
theorem field_tor_amplitude_qcqs
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ)) :
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)))
      (a b : ℤ), a ≤ b → constantModelBoundedConstructible Λ.X Y K →
      DerivedCategory.homologyConcentratedIn a b K →
        DerivedCategory.torAmplitudeIn _ a b K) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y))),
      constantModelBoundedConstructible Λ.X Y K →
        ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn _ a b K) ∧
    (constantModelBoundedConstructible Λ.X Y ⊓ DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ.X Y := by
  have hgeneral := integral_ctf_equals_bc ℓ Y Λ (by
    rcases hΛ with ⟨E, hE⟩ | hQ
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨eqToIso hE⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨eqToIso hQ⟩)))
  have hsharp := (hgeneral.2.2.1 (by
    rcases hΛ with ⟨E, hE⟩ | hQ
    · exact Or.inr (Or.inl ⟨E, ⟨eqToIso hE⟩⟩)
    · exact Or.inr (Or.inr ⟨eqToIso hQ⟩))).2
  have hfinite : ∀ K, constantModelBoundedConstructible Λ.X Y K →
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn _ a b K := by
    intro K hK
    obtain ⟨a, b, hbound⟩ :=
      (DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).2 hK.1
    exact ⟨min a b, b, min_le_right _ _,
      hsharp K (min a b) b (min_le_right _ _) hK
        (hbound.mono (min_le_left _ _) le_rfl)⟩
  refine ⟨hsharp, hfinite, le_antisymm (fun K hK ↦ hK.1) ?_⟩
  intro K hK
  obtain ⟨a, b, _, htor⟩ := hfinite K hK
  exact ⟨hK, a, b, htor⟩

end WeilConjectures
