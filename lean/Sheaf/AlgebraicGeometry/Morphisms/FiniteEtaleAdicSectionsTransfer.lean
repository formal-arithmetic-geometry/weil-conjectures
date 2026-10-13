/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward

/-!
# Transfer of adic section comparison to finite étale covers

Source: Stacks Project, Tag 0EKP, implication (1) to (3).
(blueprint: lem-sbc-finite-etale-adic-sections-transfer)
-/

@[expose] public section

noncomputable section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The quotient-power thickening of an open of the ambient spectrum. -/
abbrev openThickening (f : R →+* S) (V : (Spec (.of R)).Opens) (n : ℕ) : Scheme :=
  Limits.pullback V.ι (baseMap f n)

/-- Restriction from the ambient open to its thickening. -/
abbrev openThickeningMap (f : R →+* S) (V : (Spec (.of R)).Opens) (n : ℕ) :
    openThickening f V n ⟶ V.toScheme :=
  pullback.fst V.ι (baseMap f n)

/-- Inclusion of consecutive thickenings of the ambient open. -/
noncomputable def openThickeningTransition (f : R →+* S)
    (V : (Spec (.of R)).Opens) (n : ℕ) :
    openThickening f V n ⟶ openThickening f V (n + 1) :=
  pullback.lift (openThickeningMap f V n)
    (pullback.snd V.ι (baseMap f n) ≫ baseTransition f n)
    (by rw [Category.assoc, baseTransition_comp_baseMap]; exact pullback.condition)

end AlgebraicGeometry.Scheme.FiniteEtale.Adic

namespace AlgebraicGeometry.Scheme

/-- Structure-sheaf comparison on an open of a Noetherian affine scheme implies
section comparison for every finite étale cover of that open.

Source: Stacks Project, Tag 0EKP, implication (1) to (3), and finite affine
base change for the direct image of the structure sheaf.
(blueprint: lem-sbc-finite-etale-adic-sections-transfer)

Proof: The open V is Noetherian and quasi-affine. For the finite étale map
P -> V, its direct image E of O_P is finite locally free. On a Noetherian
quasi-affine scheme the dual E dual has finitely many global generators.
Their surjection O^r -> E dual dualizes to a universally injective map
E -> O^r with locally free cokernel C. Apply the same construction to C
and compose to obtain a universally exact sequence 0 -> E -> O^r -> O^s.
It remains exact after restriction to every quotient-power thickening.
Sections identify E with the kernel between the two finite powers of
structure-sheaf sections. Compatible families also preserve this kernel:
a compatible vector lies in it if and only if each component does.
The scalar comparison hypothesis gives bijections on the two finite powers,
and commutes with their map, so gives a bijection on their kernels.
Finite affine base change identifies the restrictions of E with the direct
images of O_(P_n), and identifies their restriction maps with coverMap and
coverTransition. The resulting kernel bijection is exactly existence and
uniqueness in the conclusion. Empty opens, rank-zero covers and variable
ranks are included; none of the argument requires a positive constant rank. -/
theorem finiteEtale_adic_sections_comparison_of_structureSheaf
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (V : (Spec (.of R)).Opens)
    (hscalar : ∀ s : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening f V n, ⊤),
      (∀ n, (FiniteEtale.Adic.openThickeningTransition f V n).appTop
        (s (n + 1)) = s n) →
      ∃! a : Γ(V.toScheme, ⊤), ∀ n,
        (FiniteEtale.Adic.openThickeningMap f V n).appTop a = s n)
    (P : V.toScheme.FiniteEtale)
    (s : ∀ n : ℕ, Γ(FiniteEtale.Adic.cover f V P n, ⊤))
    (hs : ∀ n, (FiniteEtale.Adic.coverTransition f V P n).appTop
      (s (n + 1)) = s n) :
    ∃! a : Γ(P.obj.left, ⊤), ∀ n,
      (FiniteEtale.Adic.coverMap f V P n).appTop a = s n := by sorry

end AlgebraicGeometry.Scheme
