/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.AmpleIdealSection
import Sheaf.AlgebraicGeometry.AffineCapSectionOpen
import Sheaf.AlgebraicGeometry.ConductorSections

/-! # Affine power sections away from component intersections

Source: Stacks Project, Varieties, Lemma 09NX, final paragraph, and Remark 09NW.
(blueprint: lem-sc-component-supported-affine-section).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module with ample restrictions to the reduced components has an
ambient affine power-section neighbourhood at a point on exactly one component.
No ampleness near component intersections is asserted.

Source: Stacks Project, Varieties, Lemma 09NX, final paragraph, and Remark 09NW;
Properties, Proposition 01Q3 and Lemma 01PV.
(blueprint: lem-sc-component-supported-affine-section).

Proof: Choose the unique component containing x and the reduced union Z of the other
components. Let I be the ideal of Z and I_a its image on the chosen component. The point
lifting x does not belong to V(I_a). The ample-ideal-section theorem supplies a positive
power section t1 coming from I_a, nonvanishing there. Ampleness on that component also
supplies a positive-power section t2 whose affine locus contains that point. Multiply
the two sections. Its degree is the sum of two positive integers, it still comes from
I_a, and its nonvanishing locus is the intersection of their loci. Apply
lem-sc-affine-cap-section-open inside the affine locus of t2 to make this intersection
affine. Use the canonical compatibility of pullback with tensor powers, then
lem-sc-conductor-sections to extend the product to X with zero restriction on Z.
Its nonvanishing locus is the image of the component locus. It avoids Z, and away from
Z the reduced component immersion is an isomorphism: its ideal vanishes because X is
reduced and its support is empty there. Thus this image is an affine open of X
containing x. For a single component Z is empty and the same argument uses I = O_X.
With no components the hypothesis on x is impossible. -/
theorem exists_component_supported_affine_section
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] [IsReduced X]
    (r : ℕ) (C : Fin r → Scheme.{u}) (i : ∀ a, C a ⟶ X)
    [∀ a, IsReduced (C a)] [∀ a, IsClosedImmersion (i a)]
    (hcomponents : ∀ a, Set.range (i a) ∈ irreducibleComponents X)
    (hdistinct : Function.Injective fun a ↦ Set.range (i a))
    (hcover : (⋃ a, Set.range (i a)) = Set.univ)
    (L : X.Modules) [L.IsInvertible]
    (hL : ∀ a, ∃ h : ((tensorPullback (i a)).obj L).IsInvertible,
      @IsAmple (C a) ((tensorPullback (i a)).obj L) h)
    (x : X) (hx : ∃! a, x ∈ Set.range (i a)) :
    ∃ n : ℕ, 0 < n ∧
      ∃ s : (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤),
        ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
          (U : Set X) = nonvanishingLocus (L.tensorPow n) s := by
  sorry

end AlgebraicGeometry.Scheme.Modules
