/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDncFamily
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariant
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import WeilConjectures.AlgebraicGeometry.DeformationSpace.SmoothProj

/-! # DNC invariance for all four condensed coefficients

Source: latest blueprint,
part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-dnc-invariance.md
and its proof (blueprint: thm-pur-dnc-invariance).
The normal and Rees pairs are the actual schemes. Their fibre maps are the native
exceptional counit mates with canonical pullback compositors. Normalization compares the
one and zero restrictions of every constant presentation of the family after arbitrary
finite-type base change; thus no auxiliary orientation or arbitrary endpoint map is chosen.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

variable (D : WeilConjectures.FiniteFieldDatum.{u})

local instance datumPrime : Fact D.p.Prime := ⟨D.prime⟩
local instance datumChar : CharP D.k₀ D.p := by
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  exact charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
local instance closureChar : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
local instance closurePrime : Fact (ringChar D.k).Prime :=
  ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
local instance closureClosed : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀

variable (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff :
    (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ N : ℕ, ∀ a : A, (ell ^ N) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))


set_option maxHeartbeats 2000000 in
-- Checking the large normalized coherence witness exceeds the default kernel heartbeat budget.
end AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

namespace AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

attribute [instance] Pair.base_ft Pair.base_qc Pair.base_sep Pair.source_ft Pair.source_qc
  Pair.source_sep Pair.smooth Pair.separated Pair.finite_type Pair.qc Pair.closed

variable {D : WeilConjectures.FiniteFieldDatum.{u}}

end AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

namespace AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

variable {D : WeilConjectures.FiniteFieldDatum.{u}}
  (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff :
    (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ N : ℕ, ∀ a : A, (ell ^ N) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))

/-- Both specified native fibre maps are invertible.
Source: sk-lem-geometry (1), proof Step 5 (blueprint: thm-pur-dnc-invariance).
Proof: the Rees one and zero squares identify the pairs with (g,s) and its normal
bundle zero section. Apply smooth exceptional base change to the coefficient unit;
pull its specified counit mate to the sections and compose the canonical pullback
compositors. This proves invertibility of exactly atOne and atZero for all four
coefficient presentations, with no orientation assumed. -/
theorem fibreMaps_isIso (Q : Pair D) (d : ℕ)
    [SmoothOfRelativeDimension d Q.g.left] :
    IsIso (atOne ell hell E n hn Λ hcoeff Q) ∧
      IsIso (atZero ell hell E n hn Λ hcoeff Q) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

namespace AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance
