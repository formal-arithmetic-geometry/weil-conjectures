/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward

/-! # A finite kernel presentation for sections on finite étale thickenings -/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Finite étale sections admit finite scalar coordinates and finitely many linear relations,
with injective coordinates on every quotient-power thickening. This statement does not
assume any scalar adic comparison.

Source: Stacks Project, Tag 0EKP, construction in the proof of (2) to (3), with the
ample invertible module equal to the structure sheaf; finite affine base change.
(blueprint: new-finite-etale-adic-sections-kernel)

Proof: The open V is Noetherian and quasi-affine. The direct image E of the structure
sheaf of P is finite locally free, by finite flat pushforward. The dual of E has finitely
many global generators since the structure sheaf is ample. Dualize their surjection to
embed E into a finite free sheaf with locally free cokernel C. Repeat for C, obtaining
0 -> E -> O^r -> O^t, exact after every base change. Write the second map as a matrix c
of global functions. Global sections preserve kernels, giving the injective map e and
the lifting assertion hex. Pull this sequence back to each thickening. Finite affine
base change identifies the pulled back E with the direct image of the structure sheaf
of the thickened cover. Its sections give en, which is injective and satisfies the
restricted matrix relations. Naturality of pullback and of affine base change gives
the coordinate formulas for both projections and transitions. Zero ranks and the
empty open are covered by finite empty products. -/
theorem finiteEtale_adic_sections_kernel
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (V : (Spec (.of R)).Opens) (P : V.toScheme.FiniteEtale) :
    ∃ (r t : ℕ)
      (e : Γ(P.obj.left, ⊤) → Fin r → Γ(V.toScheme, ⊤))
      (en : ∀ n : ℕ, Γ(FiniteEtale.Adic.cover f V P n, ⊤) →
        Fin r → Γ(Limits.pullback V.ι (FiniteEtale.Adic.baseMap f n), ⊤))
      (c : Fin t → Fin r → Γ(V.toScheme, ⊤)),
      Function.Injective e ∧
      (∀ n, Function.Injective (en n)) ∧
      (∀ x : Fin r → Γ(V.toScheme, ⊤),
        (∀ j : Fin t, ∑ i : Fin r, c j i * x i = 0) → ∃ a, e a = x) ∧
      (∀ (n : ℕ) (a : Γ(FiniteEtale.Adic.cover f V P n, ⊤)) (j : Fin t),
        ∑ i : Fin r, (pullback.fst V.ι (FiniteEtale.Adic.baseMap f n)).appTop
          (c j i) * en n a i = 0) ∧
      (∀ (n : ℕ) (a : Γ(P.obj.left, ⊤)) (i : Fin r),
        en n ((FiniteEtale.Adic.coverMap f V P n).appTop a) i =
          (pullback.fst V.ι (FiniteEtale.Adic.baseMap f n)).appTop (e a i)) ∧
      (∀ (n : ℕ) (a : Γ(FiniteEtale.Adic.cover f V P (n + 1), ⊤)) (i : Fin r),
        en n ((FiniteEtale.Adic.coverTransition f V P n).appTop a) i =
          (pullback.lift (pullback.fst V.ι (FiniteEtale.Adic.baseMap f n))
            (pullback.snd V.ι (FiniteEtale.Adic.baseMap f n) ≫
              FiniteEtale.Adic.baseTransition f n)
            (by rw [Category.assoc, FiniteEtale.Adic.baseTransition_comp_baseMap]
                exact pullback.condition)).appTop (en (n + 1) a i)) := by sorry

end AlgebraicGeometry.Scheme
