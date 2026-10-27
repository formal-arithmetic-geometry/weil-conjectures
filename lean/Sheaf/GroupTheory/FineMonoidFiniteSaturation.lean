/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Finiteness.Defs
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup

public import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.Paper.GordanRationalCone

/-!
# Finite saturation of a fine monoid

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.17 and 3.2.9, printed pp. 101 and 104
(blueprint: lem-trf-fine-monoid-finite-saturation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open Algebra

/-- The root saturation of a finitely generated integral additive commutative monoid is fine
saturated, has the same group completion, is a finite union of translates, commutes with
localization, and induces a finite map of monoid algebras for every commutative coefficient ring.
The monoid `Q` is identified with the root subset in the canonical group completion. Both its
completion equivalence and its inclusion map `i` are normalized on elements, so they are canonical.

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.17, printed p. 101, and 3.2.9, proof,
printed p. 104 (blueprint: lem-trf-fine-monoid-finite-saturation).

Proof:
1. Choose finite generators of `P`; their classes generate its abelian group completion `G`.
   Write `T` for the torsion subgroup and `L = G/T`. This quotient is finitely generated and
   torsion-free: if a positive multiple of a class is torsion, that class is torsion. A finite
   basis exists by `Module.basisOfFiniteTypeTorsionFree'`
   (blueprint node lem-trf-fg-torsionfree-group-free). Lift the basis to split `G = T ⊕ L`.
   Then `T` is finitely generated; products of the orders of its generators bound its size,
   so `T` is finite, of order `m`.
   Apply `gordan_rational_cone_finite` (blueprint node lem-trf-gordan-rational-cone-finite)
   to the images of the generators in `L`. It gives a cone `C` and finite translates covering
   its lattice points. An element `g` belongs to the root saturation precisely when its class
   lies in `C`: clearing positive rational denominators gives `n g - p ∈ T`, hence
   `(m*n) • g ∈ P`; the reverse direction divides a positive multiple by its multiplier in
   `L ⊗ ℚ`. Lift the finite translate representatives and add all elements of `T` to obtain
   a finite set `F` in the root saturation. Every saturated element is `f + p` for `f ∈ F`
   and `p ∈ P`; the reverse inclusion follows from closure under addition (multiply the
   two positive root witnesses).
2. The finite set `F` together with generators of `P` generates the root saturation. It is
   integral as a submonoid of `G`, and its group completion is `G` because it contains `P`.
   If a positive multiple of `g` lies in the root saturation, a further positive multiple
   lies in `P`, so `g` lies in the root saturation. Thus the monoid is saturated.
3. For any submonoid `S ⊆ P`, if `n*x = p-s` with `n > 0`, then
   `n*(x+s) = p+(n-1)*s ∈ P`, giving `x ∈ P^sat-S`. Conversely, if `x=a-s` and `n*a ∈ P`,
   then `n*x = n*a-n*s ∈ P-S`. These are the two inclusions for localization compatibility.
4. Every element of the monoid algebra is a finite linear combination of monomials. The
   translate formula writes `g=f+p`, hence `z^g=z^f*z^p`. The finitely many `z^f` therefore
   generate `R[P^sat]` over `R[P]`, proving finiteness of the canonical induced ring map. -/
theorem fine_monoid_finite_saturation
    (P : Type u) [AddCommMonoid P] [AddMonoid.FG P]
    (hP : Function.Injective (GrothendieckAddGroup.of (M := P))) :
    ∃ Q : AddSubmonoid (GrothendieckAddGroup P),
      (∀ g : GrothendieckAddGroup P,
        g ∈ Q ↔ ∃ n : ℕ, 0 < n ∧ n • g ∈ Set.range (GrothendieckAddGroup.of (M := P))) ∧
      AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative Q) ∧
      (∃ e : GrothendieckAddGroup Q ≃+ GrothendieckAddGroup P,
        ∀ q : Q, e (GrothendieckAddGroup.of q) = q.1) ∧
      (∃ F : Finset (GrothendieckAddGroup P), (∀ f ∈ F, f ∈ Q) ∧
        (Q : Set (GrothendieckAddGroup P)) =
          ⋃ f ∈ (F : Set (GrothendieckAddGroup P)),
            {x | ∃ p : P, x = f + GrothendieckAddGroup.of p}) ∧
      (∀ S : AddSubmonoid P,
        {x : GrothendieckAddGroup P | ∃ n : ℕ, 0 < n ∧
          ∃ p : P, ∃ s : S,
            n • x = GrothendieckAddGroup.of p - GrothendieckAddGroup.of s.1} =
          {x : GrothendieckAddGroup P | ∃ q : Q, ∃ s : S,
            x = q.1 - GrothendieckAddGroup.of s.1}) ∧
      (∃ i : P →+ Q, (∀ p : P, (i p).1 = GrothendieckAddGroup.of p) ∧
        ∀ (R : Type v) [CommRing R], (AddMonoidAlgebra.mapDomainRingHom R i).Finite) := by
  sorry
