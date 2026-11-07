/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.PrincipalThickeningSingleLift

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Lifting sections across a bounded gap of principal thickenings

Source: Stacks Project, Tags 0H3D and 0H3E (Lemma 20.39.2 and Example 20.39.3).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Vanishing of H^1 and a uniform power-torsion bound give eventual lifting
from principal thickenings to the ambient open.

Source: Stacks Project, Tags 0H3D and 0H3E (Lemma 20.39.2 and
Example 20.39.3, the pro-isomorphism of multiplication complexes with quotients).
(blueprint: lem-sbc-principal-thickening-sections-lift)

Proof: Set F = O_W and j = n+1. Exactness of localization identifies
ker(g^r : F -> F) with the restriction of Ann_R(g^r), so hkill implies
g^c kills this kernel for every r. Put T = ker(g^(j+c) : F -> F).
The complex C = [F/T --g^(j+c)--> F], in degrees -1 and 0, has injective
differential and is quasi-isomorphic to Q_(j+c) = F/g^(j+c)F. Multiplication
by g^c is well-defined from F/T to F. Together with identity in degree 0
it gives a chain map C -> E_j = [F --g^j--> F]. Its composite with
E_j -> Q_j is the canonical quotient map Q_(j+c) -> Q_j.
Applying derived global sections therefore factors the quotient restriction
on H^0 through H^0(RGamma(E_j)). The multiplication triangle and hH identify
this latter group with Gamma(W,F)/g^j Gamma(W,F): the adjacent H^1(W,F)
term vanishes. Every section at level n+c thus restricts to the image of an
ambient section at level n. This is the explicit shifted-index inverse in
Stacks Tag 0H3D used by Example 0H3E, without passing to inverse limits.
For the principal quotient f, ker f=(g), and the pushforward of the structure
sheaf of openThickening f W n is Q_(n+1). These identifications commute with
openThickeningMap and consecutive transitions. The laws hzero and hsucc
identify res with the consecutive quotient composites by induction.
When c=0, hkill makes every kernel zero, so the same argument applies at
the same level. It also applies to empty W, to g=0, to units and nilpotents,
and does not require R Noetherian or W to be a puncture. -/
theorem principal_thickening_sections_lift
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens)
    (hH : Subsingleton (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) 1))
    (c : ℕ)
    (hkill : ∀ (j : ℕ) (s : R), g ^ j * s = 0 → g ^ c * s = 0) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    ∀ (res : ∀ n k : ℕ, Γ(FiniteEtale.Adic.openThickening f W (n + k), ⊤) →
        Γ(FiniteEtale.Adic.openThickening f W n, ⊤)),
      (∀ n t, res n 0 t = t) →
      (∀ n k t, res n (k + 1) t = res n k
        ((FiniteEtale.Adic.openThickeningTransition f W (n + k)).appTop t)) →
      ∀ n (t : Γ(FiniteEtale.Adic.openThickening f W (n + c), ⊤)),
        ∃ a : Γ(W.toScheme, ⊤),
          (FiniteEtale.Adic.openThickeningMap f W n).appTop a = res n c t := by
  dsimp
  intro res hzero hsucc n t
  have hcanon : ∀ (k : ℕ) (t : Γ(FiniteEtale.Adic.openThickening
      (Ideal.Quotient.mk (Ideal.span {g})) W (n + k), ⊤)),
      res n k t = principalThickeningCanonical R g W n k t := by
    intro k
    induction k with
    | zero =>
        intro t
        simpa [principalThickeningCanonical] using (hzero n t)
    | succ k ih =>
        intro t
        rw [hsucc n k t, ih]
        rfl
  obtain ⟨a, ha⟩ := principal_thickening_single_lift R g W hH c hkill n t
  refine ⟨a, ?_⟩
  exact ha.trans (hcanon c t).symm

end AlgebraicGeometry.Scheme
