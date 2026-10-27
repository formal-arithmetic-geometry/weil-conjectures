/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.AlgebraicGeometry.LciCotangentPresentation
public import Sheaf.AlgebraicGeometry.KoszulRegularImmersionNear

import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.Basic

/-!
# Polynomial local factorizations of Koszul lci morphisms

Source: Stacks Project, More on Morphisms, Tags 069E--069G, especially the polynomial
factorization remark preceding Definition 069F
(blueprint: lem-sfb-lci-polynomial-local-factorization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism locally admitting a Koszul-regular closed immersion into a smooth
ambient scheme locally admits a Koszul-regular immersion into finite affine space
over any prescribed open neighbourhood in its target.
Source: Stacks Project, More on Morphisms, Tags 069E--069G
(blueprint: lem-sfb-lci-polynomial-local-factorization).

Proof: Choose the given closed immersion `X₀ → P` and smooth map `P → Y` near `x`.
Choose an affine target neighbourhood `T = Spec A` inside `V`, and an affine
`W = Spec B` inside its inverse image in `P`, containing the image of `x`.
Smooth restriction and the affine smoothness criterion identify `A → B` as smooth,
hence finitely presented (lem-weil-pbc-smooth-restrict-open-subschemes,
lem-weil-pbc-smooth-ring-map-iff-smooth-affine, def-weil-pbc-finitely-presented-algebra).
The inverse image `Z` of `W` in `X₀` is `Spec (B/I)`. Restricting regular generators
on principal affine refinements preserves their Koszul homology vanishing, since
localization is exact (def-weil-pbc-koszul-regular-sequence).
Choose a finite polynomial presentation `A[t₁,…,tₙ] → B`. Its composite with `B → B/I`
is surjective, so defines a closed immersion `b : Z → 𝔸ⁿ_T`
(def-weil-closed-immersion, def-sbc-affine-space, def-weil-affine-spectrum).
In `Q = 𝔸ⁿ_W`, define `c : Z → Q` using the quotient on constants and the images
of the presentation variables. It is a closed immersion, and its composites with
`Q → W` and `Q → 𝔸ⁿ_T` are the original closed immersion and `b`, respectively.
The first projection is smooth (sbc-lem-affine-space-smooth), so
lem-sfb-koszul-immersion-smooth-lift makes `c` Koszul-regular. The second is smooth
by polynomial base change of `A → B`
(lem-weil-pbc-smooth-ring-map-base-change-composition and the affine criterion).
Then lem-sfb-koszul-immersion-smooth-push makes `b` Koszul-regular.
Finally `𝔸ⁿ_T → 𝔸ⁿ_V` is an open immersion, being the inverse image of `T → V`.
Compose `b` with it to obtain `a`, and take `U = Z`. The constants-map identities
prove the required factorization, and the closed charts for `b` give Koszul
regularity near every point of `U`. All restrictions contain `x` and lie over `V`;
no global finiteness, separation, Noetherian or flatness assumption is used. -/
theorem exists_lci_polynomial_local_factorization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ (P : Scheme.{u}) (j : U.toScheme ⟶ P) (p : P ⟶ Y),
        IsClosedImmersion j ∧ CotangentPresentation.IsKoszulImmersion j ∧
          Smooth p ∧ j ≫ p = U.ι ≫ f)
    (x : X) (V : Y.Opens) (hx : f x ∈ V) :
    ∃ U : X.Opens, x ∈ U ∧ U ≤ f ⁻¹ᵁ V ∧
      ∃ (n : ℕ) (a : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme),
        IsImmersion a ∧ (∀ z : U.toScheme, IsKoszulRegularImmersionNear a z) ∧
          a ≫ (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme) ≫ V.ι = U.ι ≫ f := by
  sorry

end AlgebraicGeometry
