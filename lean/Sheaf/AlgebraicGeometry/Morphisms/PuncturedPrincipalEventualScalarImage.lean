/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoPunctureGlobalSections
import Sheaf.AlgebraicGeometry.Morphisms.DepthThreePunctureHOne
import Sheaf.AlgebraicGeometry.Morphisms.PrincipalThickeningSectionsLift

/-! # Eventual scalar image on punctured principal thickenings

Source: Stacks Project, Tags 0H3E, 0BK0 and 0AVY.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Restriction across `k` consecutive thickenings, constructed by composition.

Source: the transition maps of `FiniteEtale.Adic.openThickening`.
(blueprint: lem-sbc-punctured-principal-eventual-scalar-image) -/
noncomputable def puncturedPrincipalSectionRestriction
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (W : (Spec (.of R)).Opens) (n : ℕ) :
    (k : ℕ) → Γ(FiniteEtale.Adic.openThickening f W (n + k), ⊤) →
      Γ(FiniteEtale.Adic.openThickening f W n, ⊤)
  | 0 => fun t ↦ t
  | k + 1 => fun t ↦ puncturedPrincipalSectionRestriction f W n k
      ((FiniteEtale.Adic.openThickeningTransition f W (n + k)).appTop t)

private theorem scalar_power_torsion_bound
    (R : Type u) [CommRing R] [IsNoetherianRing R] (g : R) :
    ∃ c : ℕ, ∀ (j : ℕ) (s : R), g ^ j * s = 0 → g ^ c * s = 0 := by
  let K : ℕ →o Submodule R R :=
    { toFun := fun j ↦ (LinearMap.mulLeft R (g ^ j)).ker
      monotone' := by
        intro j l h s hs
        change g ^ j * s = 0 at hs
        change g ^ l * s = 0
        rw [← Nat.sub_add_cancel h, pow_add, mul_assoc, hs, mul_zero] }
  obtain ⟨c, hc⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  refine ⟨c, ?_⟩
  intro j s hs
  by_cases h : c ≤ j
  · have hj : s ∈ K j := hs
    rw [← hc j h] at hj
    exact hj
  · have h : j ≤ c := by omega
    exact K.monotone h hs

/-- At any fixed level, sufficiently late sections restrict into the scalar image.

Source: Stacks Project, Tags 0H3E (Example 20.39.3), 0BK0 (Lemma 51.8.2)
and 0AVY (Lemma 47.11.1).
(blueprint: lem-sbc-punctured-principal-eventual-scalar-image)

Proof: Write F = O_W. The local-cohomology comparison of 0BK0 and the depth
vanishing of 0AVY give Gamma(W,F) = R, canonically, and H^1(W,F) = 0.
The ideals Ann_R(g^j) stabilize by Noetherianity. Exactness of localization
identifies their restrictions with F[g^j]. Choose c at least the stabilization
index; then g^c kills the stabilized torsion. For j >= 1 let
E_j = [F --g^j--> F] in degrees -1 and 0. The transition from E_(j+1) to E_j
is g in degree -1 and the identity in degree 0. The map E_j -> F/g^j F has
cone F[g^j][2], whose sufficiently long transitions vanish: their maps on
torsion are multiplication by the corresponding power of g. Thus these
cones form a pro-zero system, as in 0H3E. Apply derived global sections;
zero morphisms remain zero. The natural long exact cohomology sequences
show that the cokernels of H^0(R Gamma(E_j)) -> Gamma(W,F/g^j F) are pro-zero:
each embeds in H^0 of the derived global sections of the corresponding cone,
and a zero transition on that cone kills the cokernel transition.
The multiplication triangle and H^1(W,F) = 0 identify H^0(R Gamma(E_j))
with R/g^j R. The comparison is the canonical scalar restriction. The
kernel of R -> R/(g) is (g), its jth power is (g^j), and the open pullback
of the jth quotient has structure sheaf F/g^j F under pushforward to W.
Naturality of GammaSpecIso identifies this comparison with the displayed
scalar map, and quotient transitions with the recursive restriction above.
For fixed n choose a later index n+k at which the cokernel transition to
n is zero. Every section there therefore restricts into the scalar image
at n; choose a representative in R of its quotient class. This is a
finite-stage assertion about arbitrary sections, with no compatible
infinite family. For g = 0, take k = 0 and use Hartogs; for nilpotent g,
choose n+k beyond the nilpotence exponent, where the source is W. -/
theorem punctured_principal_eventual_scalar_image
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    ∀ n, ∃ k : ℕ,
      ∀ t : Γ(FiniteEtale.Adic.openThickening f W (n + k), ⊤), ∃ a : R,
        ((ΓSpecIso (.of R)).inv ≫
          (FiniteEtale.Adic.openThickeningMap f W n ≫ W.ι).appTop) a =
            puncturedPrincipalSectionRestriction f W n k t := by
  classical
  have _ := hg
  dsimp only
  let f := Ideal.Quotient.mk (Ideal.span {g})
  let ρ : CommRingCat.of R ⟶ Γ(W.toScheme, ⊤) :=
    (ΓSpecIso (.of R)).inv ≫ W.ι.appTop
  have hρ : Function.Surjective ρ :=
    ((depth_two_puncture_globalSections_bijective R
      (le_trans (by decide) hdepth) W hW).comp
        (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of R)).inv)).surjective
  obtain ⟨c, hc⟩ := scalar_power_torsion_bound R g
  have hH := depth_three_puncture_h_one R hdepth W hW
  have hlift := principal_thickening_sections_lift R g W hH c hc
    (puncturedPrincipalSectionRestriction f W) (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
  intro n
  refine ⟨c, ?_⟩
  intro t
  obtain ⟨s, hs⟩ := hlift n t
  obtain ⟨a, ha⟩ := hρ s
  refine ⟨a, ?_⟩
  rw [← ha] at hs
  simpa only [ρ, Scheme.Hom.comp_appTop, ← Category.assoc,
    ConcreteCategory.comp_apply] using hs

end AlgebraicGeometry.Scheme
