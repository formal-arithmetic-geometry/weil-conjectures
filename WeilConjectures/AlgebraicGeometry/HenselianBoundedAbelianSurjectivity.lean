/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.HenselianConnectedness
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion
import WeilConjectures.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep

/-!
# Surjectivity of henselian restriction for bounded abelian coefficients

## References

* Stacks Project, Tags 09ZE, 09ZH and 09ZI.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Henselian restriction is surjective for abelian sheaves killed by one positive
integer (Stacks, Tags 09ZE, 09ZH and 09ZI). -/
theorem surjective_cohomologyMap_of_henselianRing_of_nsmul_eq_zero
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    (G : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (hn : 0 < n) (hG : n • 𝟙 G = 0) (q : ℕ) :
    Function.Surjective
      (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) G q) := by
  have hzero (G : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
      Function.Bijective
        (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) G 0) := by
    let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    have : IsClosedImmersion i :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hi : Set.range i = PrimeSpectrum.zeroLocus (I : Set A) := by
      change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    have : IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i G) := by
      apply isIso_abelian_globalSectionsUpperStarMap_of_finite_connected_closed_intersections i
      intro X' p hp C hC hC'
      rw [hi]
      exact (p.spectralSpace_and_isClosed_and_isConnected_inter I).2.2 C hC hC'
    let a := fun g : (Sheaf.Γ _ AddCommGrpCat.{u + 1}).obj G ↦
      (Sheaf.H.equiv₀ G terminalIsTerminal).symm
        ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G g)
    let G₀ := (i)^*[AddCommGrpCat.{u + 1}].obj G
    let b := fun g : (Sheaf.Γ (Spec (.of (A ⧸ I))).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj G₀ ↦
      (Sheaf.H.equiv₀ G₀ terminalIsTerminal).symm
        ((Sheaf.ΓNatIsoSheafSections _ AddCommGrpCat.{u + 1}
          terminalIsTerminal).hom.app G₀ g)
    have ha : Function.Bijective a :=
      (Sheaf.H.equiv₀ G terminalIsTerminal).symm.bijective.comp
        (ConcreteCategory.bijective_of_isIso
          ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G))
    have hb : Function.Bijective b :=
      (Sheaf.H.equiv₀ G₀ terminalIsTerminal).symm.bijective.comp
        (ConcreteCategory.bijective_of_isIso
          ((Sheaf.ΓNatIsoSheafSections _ AddCommGrpCat.{u + 1}
            terminalIsTerminal).hom.app G₀))
    have hres := ConcreteCategory.bijective_of_isIso
      (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i G)
    have hab : ∀ g, cohomologyMap i G 0 (a g) =
        b (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i G g) :=
      cohomologyMap_zero_eq_globalSectionsUpperStarMap i G
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨x, rfl⟩ := ha.2 x
      obtain ⟨y, rfl⟩ := ha.2 y
      apply congrArg a
      apply hres.1
      apply hb.1
      change cohomologyMap i G 0 (a x) = cohomologyMap i G 0 (a y) at hxy
      rw [hab, hab] at hxy
      exact hxy
    · intro y
      obtain ⟨y, rfl⟩ := hb.2 y
      obtain ⟨x, rfl⟩ := hres.2 y
      exact ⟨a x, hab x⟩
  have hcomparison : ∀ (q : ℕ)
      (G : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      n • 𝟙 G = 0 → Function.Bijective
        (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) G q) := by
    intro q
    induction q with
    | zero => exact fun G _ ↦ hzero G
    | succ q ih =>
      exact fun G hG ↦
        bijective_cohomologyMap_succ_of_henselianRing_of_nsmul_eq_zero I n hn q ih G hG
  exact (hcomparison q G hG).2

end AlgebraicGeometry.Etale
