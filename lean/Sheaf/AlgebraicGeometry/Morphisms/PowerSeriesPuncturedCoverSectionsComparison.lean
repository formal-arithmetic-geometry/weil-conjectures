/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.RingTheory.Depth
import Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedGlobalSections
import Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedThickeningSections
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Sections of finite étale covers and the power-series formal neighbourhood

Source: Stacks Project, Tags 0EY9 and 0EKP.
(blueprint: lem-sbc-power-series-punctured-cover-sections-comparison)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Sections of a single finite étale cover are recovered from compatible sections
on its quotient-power thickenings.

Source: Stacks Project, Tag 0EY9, structure-sheaf comparison, followed by
Tag 0EKP, implication (1) to (3).
(blueprint: lem-sbc-power-series-punctured-cover-sections-comparison)

Proof: Put B = A[[x_1,...,x_d]], I = ker(constantCoeff), and U = Spec(A)
minus its closed point. Hartogs at depth two identifies Gamma(U,O_U) with A.
The quotients B/I^(n+1) are finite free over A on monomials of degree at most n,
so the inverse limit of the sections of the thickenings of U is B. Restriction
from Gamma(V,O_V) to this limit is injective: Krull intersection gives zero
germs along U; the associated primes of B are pB for associated primes p of A,
by flat local depth. Positive depth excludes the maximal ideal of A, and pB
specializes to pB+I on U. Every associated point of V is therefore detected,
so a section zero formally is zero. The composite B -> Gamma(V,O_V) -> B
is the canonical isomorphism, whence both arrows are isomorphisms.
The direct image E of O_P under the finite étale structure map is finite
locally free, including rank zero and variable ranks. Since V is Noetherian
and quasi-affine, choose finite global generators of E dual. Dualizing embeds
E into O^r with locally free cokernel; embed that cokernel into O^s in the same
way. This gives a universally exact sequence 0 -> E -> O^r -> O^s.
Sections and inverse limits preserve the kernel, so comparison for O implies
comparison for E. Finite affine base change identifies its restrictions with
the direct images of O_(P_n). Thus each compatible section family comes from
one and only one section of P. For the empty cover all these rings are zero;
no positive-rank or connectedness assumption is used. -/
theorem finiteEtale_powerSeries_punctured_cover_sections_comparison
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (P : V.toScheme.FiniteEtale)
    (s : ∀ n : ℕ, Γ(FiniteEtale.Adic.cover
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n, ⊤))
    (hs : ∀ n, (FiniteEtale.Adic.coverTransition
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n).appTop
        (s (n + 1)) = s n) :
    ∃! a : Γ(P.obj.left, ⊤), ∀ n, (FiniteEtale.Adic.coverMap
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n).appTop a = s n := by
  have hglobal := bijective_powerSeries_punctured_globalSections A hdepth d hd V hV
  apply finiteEtale_adic_sections_comparison_of_structureSheaf
    (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V ?_ P s hs
  intro t ht
  obtain ⟨b, hb, huniq⟩ :=
    existsUnique_powerSeries_punctured_thickening_sections A hdepth d hd V hV t ht
  let r := ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom
  refine ⟨r b, ?_, ?_⟩
  · intro n
    exact hb n
  · intro a ha
    obtain ⟨c, rfl⟩ := hglobal.2 a
    have hc : ∀ n,
        ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop ≫
          (FiniteEtale.Adic.openThickeningMap
            (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V n).appTop) c = t n :=
      ha
    exact congrArg r (huniq c hc)

end AlgebraicGeometry.Scheme
