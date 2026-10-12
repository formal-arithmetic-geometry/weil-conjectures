/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystem

/-! # Compatibility of normalized comparisons with inverse image

Source: Stacks Project, Tags 01EQ and 01FD. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- Inverse image respects any normalized additive Cech comparison systems.
This is a compatibility statement for existing systems, not an existence assertion.

Source: Stacks Project, Tag 01FD, Lemma 20.15.1, and the normalized comparison
construction of Tag 01EQ, Lemma 20.11.2.
(blueprint: lem-pc-cech-comparison-inverse-image-compatibility)

Proof: First identify any normalized system with the augmented-resolution
comparison. The Cech cohomology functors are effaceable for the exact structure
of coefficient sequences surjective on every tuple intersection: embed a sheaf F
into the product of direct images of F restricted to each covering open. On any
tuple intersection this embedding splits, using one member of that tuple, so the
quotient sequence is admissible. The positive Cech cohomology of the product
vanishes: in each factor insertion of its distinguished covering member contracts
the Cech complex. Products of abelian groups are exact. Dimension shifting along
these admissible sequences, naturality, and the connecting law show by induction
that a normalized comparison is uniquely determined by its degree-zero law.

Now compute with the resolution comparisons. Resolve the source and target abelian
sheaves and the pushed-forward target resolution. Lift the coefficient morphism
and form the augmented pentagon of Tag 01FD. Tuple restriction commutes with the
resolution maps and makes the two global-section squares commute. The coordinate
hypothesis identifies the two coefficient-augmentation images of the cycles.
Take total cohomology and invert the section-augmentation quasi-isomorphisms;
the outer square gives equality of their comparison classes. Its action on sheaf
cohomology is the displayed Ext action: inverse image is exact, sends the constant
integer sheaf to itself via constIso, and the adjoint coefficient map is coeff.
The derived section map and this Ext map agree in degree zero and commute with
boundaries, hence agree in all degrees by effaceability of sheaf cohomology.
Finally transport from module-valued to abelian Cech homology through the explicit
scalar-restriction isomorphisms; these are coordinatewise identities. The
uniqueness proved above substitutes the supplied systems for the resolution
systems. In degree zero the diagram is gluing; an empty cover forces the scheme
empty and the relevant groups zero. No acyclicity or quasi-coherence is used. -/
theorem cechComparison_inverseImage_compatibility
    {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}} {ι : Type u}
    (g : Y ⟶ X) (f : X ⟶ Spec (.of R)) (f' : Y ⟶ Spec (.of S))
    (U : ι → X.Opens) (V : ι → Y.Opens) (hcover : iSup U = ⊤)
    (hcover' : iSup V = ⊤) (M : X.Modules) (N : Y.Modules)
    (φ : M ⟶ (pushforward g).obj N)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (c : CechComparisonSystem U hcover) (c' : CechComparisonSystem V hcover') :
    ∀ (q : ℕ) (z : (cechOver f U M).cycles q) (z' : (cechOver f' V N).cycles q),
      (∀ y : Fin (q + 1) → ι,
        cechCoordinate f' V N q y ((cechOver f' V N).iCycles q z') =
          N.presheaf.map (homOfLE (hinter q y)).op
            (φ.val.app (op (⨅ l, U (y l)))
              (cechCoordinate f U M q y ((cechOver f U M).iCycles q z)))) →
      c'.overMap f' N q ((cechOver f' V N).homologyπ q z') =
        Sheaf.H.map (coeff g φ) q
          (Sheaf.H.mapFunctor (invImage g) (constIso g).symm
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) q
              (c.overMap f M q ((cechOver f U M).homologyπ q z))) := by sorry
end AlgebraicGeometry.Scheme.Modules
