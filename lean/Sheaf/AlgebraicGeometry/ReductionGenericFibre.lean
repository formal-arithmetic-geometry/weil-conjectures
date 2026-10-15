/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Reduction commutes with a generic fibre

Source: Stacks Project, Tag 054Z, `lemma-reduction-generic-fibre`
(blueprint: lem-pur-reduction-generic-fibre).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Reduction commutes with taking a fibre at a generic point of an irreducible component.
The two equations identify the composite with the reduction inclusion as the canonical
map of fibres: its projections to `Z` and to `Spec κ(η)` are the prescribed ones.
No finite type, reducedness, or flatness assumptions are needed.

Source: Stacks Project, Tag 054Z, `lemma-reduction-generic-fibre`
(blueprint: lem-pur-reduction-generic-fibre).

Proof:
1. Choose affine charts `Spec B → Spec A` above η, corresponding to a minimal prime p
   (`lem-weil-pbc-affine-open-spec-points`,
   `lem-weil-pbc-spec-irreducible-components-minimal-primes`). Their fibres cover the
   two schemes, by `lem-weil-pbc-fibre-product-affine-spectra` and
   `lem-weil-pbc-open-fibre-product`.
2. Put S = A ∖ p, L = S⁻¹B, J = (p A_p)L, and N = nilradical B.
   The fibre ring is L/J (`def-weil-pbc-localization-at-prime` and
   `lem-weil-pbc-localization-base-change`). Elements of p A_p are nilpotent by
   `lem-weil-pbc-minimal-prime-reduced-localization-field`. Every element of J is a
   finite sum of multiples of nilpotents and is nilpotent by expanding a sufficiently
   large power. No uniform nilpotence exponent is required.
3. Localization of B → B/N is surjective with kernel K = S⁻¹N. The fraction zero
   criterion shows K is exactly the nilradical of L: if (b/s)^n = 0, a denominator t
   kills b^n, so tb is nilpotent and b/s = tb/(ts). This also covers zero denominators.
4. Thus J ⊆ K. The fibre of B/N is L/K, since the image of J in L/K is zero.
   The canonical map L/J → L/K has kernel K/J, precisely the nilradical of L/J.
5. These canonical quotient identifications agree on overlaps and glue to the claimed
   isomorphism, compatibly with both projections. This uses
   `def-weil-pbc-scheme-reduction`; empty fibres and charts obey the same calculation
   with zero rings. -/
theorem Scheme.Hom.reduction_generic_fibre {Z T : Scheme.{u}} (h : Z ⟶ T)
    (η : T) (hη : closure ({η} : Set T) ∈ irreducibleComponents T) :
    ∃ e : (Z.nilradical.subschemeι ≫ h).fiber η ≅ (h.fiber η).nilradical.subscheme,
      e.hom ≫ (h.fiber η).nilradical.subschemeι ≫ h.fiberι η =
        (Z.nilradical.subschemeι ≫ h).fiberι η ≫ Z.nilradical.subschemeι ∧
      e.hom ≫ (h.fiber η).nilradical.subschemeι ≫ h.fiberToSpecResidueField η =
        (Z.nilradical.subschemeι ≫ h).fiberToSpecResidueField η := by
  sorry

end AlgebraicGeometry
