/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Length
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule

/-! # Smoothness from Artinian tests with a fixed residue field

Source: Stacks Project, More on Morphisms, Tag 02HX (4) implies (1), and Algebra,
Definition 02HS (blueprint: lem-sfb-smooth-fixed-residue-artinian-test).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Small Artinian extensions with residue field identified with `κ(x)` detect smoothness
on a neighbourhood of `x`. The surjection `r` specifies the residue identification for
`B`; its composite with the small extension specifies the identification for `B'`.
No coefficient-field embedding is assumed.

Source: Stacks Project, More on Morphisms, Tag 02HX (4) implies (1), and Algebra,
Definition 02HS (blueprint: lem-sfb-smooth-fixed-residue-artinian-test).

Proof following the six steps of the node:
1. Choose Noetherian affine `V = Spec R` around `f(x)` and affine `U = Spec A`
   around `x` inside its preimage, with `A` finite type over `R`
   (pqf-def-locnoeth, def-weil-finite-type-morphism). Factor the restricted map
   through `V` (lem-weil-pbc-morphism-factors-through-open-subscheme), and identify
   the residue field of the corresponding prime `q` with `κ(x)`
   (def-weil-affine-spectrum, def-weil-residue-field).
2. Turn each fixed-residue ring test into a scheme square by the affine spectrum
   correspondence (def-weil-affine-spectrum). Apply the hypothesis. The test spectra
   have just one point (lem-weil-pbc-artinian-local-unique-prime), and the lift sends
   it to `x`, so it factors through `U`. Unique factorization through `V` gives an
   `R`-compatible ring lift (lem-weil-pbc-morphism-factors-through-open-subscheme).
3. Present `A` as a quotient of a finite polynomial algebra `P` over `R` and localize
   at the preimage of `q`, obtaining a surjection `C = P_Q → A_q`. Lift numerators
   and denominators to see surjectivity. The ring `C` is Noetherian and local
   (def-weil-pbc-mv-polynomial-ring, def-weil-pbc-localization-at-prime,
   lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian).
   Write `J` for the kernel and `m` for the maximal ideal of `C`.
4. Apply lem-sfb-fixed-residue-lifts-truncated-section: the ring lifting property
   gives an `R`-algebra section of `C/(J² + m^N) → C/(J + m^N)` for every `N ≥ 1`.
   Every test still has residue field `κ(x)`.
5. Apply lem-sfb-truncated-polynomial-sections-smooth to obtain `g ∉ q` with `A_g`
   smooth over `R`.
6. The principal localization identifies `Spec A_g` with `D(g)` containing `x`
   (lem-weil-pbc-principal-localization-open-immersion). Compare affine smoothness
   with ring smoothness (lem-weil-pbc-smooth-ring-map-iff-smooth-affine) and compose
   with `V → Y` (lem-weil-pbc-smooth-restrict-open-subschemes). This gives the desired
   smooth restriction on an open neighbourhood of `x` in `X`.
-/
theorem smooth_near_of_fixed_residue_artinian_lifting
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] (x : X)
    (hlift : ∀ (B' B : CommRingCat.{u})
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (q : B' ⟶ B), Function.Surjective q.hom →
      Module.length B' (RingHom.ker q.hom) = 1 →
      ∀ (r : B ⟶ X.residueField x), Function.Surjective r.hom →
      ∀ (a : Spec B ⟶ X) (b : Spec B' ⟶ Y),
        Spec.map r ≫ a = X.fromSpecResidueField x →
        a ≫ f = Spec.map q ≫ b →
        ∃ a' : Spec B' ⟶ X, Spec.map q ≫ a' = a ∧ a' ≫ f = b) :
    ∃ N : X.Opens, x ∈ N ∧ Smooth (N.ι ≫ f) := by
  sorry

end AlgebraicGeometry
