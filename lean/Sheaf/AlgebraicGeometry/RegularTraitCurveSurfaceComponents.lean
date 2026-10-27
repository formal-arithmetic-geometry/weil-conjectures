/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.RationalFunctionsGenericStalks
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Topology.Separation.Basic
import WeilConjectures.AlgebraicGeometry.Dimension
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.KrullDimension.Zero
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # Integral surface components and vertical DVR stalks over a trait

Source: Stacks Project, Properties, Tags 033M and 04MU; Algebra, Tag 00PD (4);
Schemes, Tag 0HA1 (blueprint: lem-sfb-regular-trait-curve-surface-components).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A regular Noetherian proper flat trait scheme with reduced special fibre and the stated
local dimension bounds is a finite disjoint union of clopen integral regular surfaces, each
meeting both fibres. At each special-fibre component's generic point the ambient stalk is
a DVR, the image of the base uniformizer is nonzero and generates its maximal ideal, and
the quotient is canonically the special-fibre generic point's residue field.

The fibres are the intrinsic scheme-theoretic fibres at the generic and closed points of
`Spec R`; their coefficient fields are respectively the fraction field and residue field.
The image of `π` in an ambient stalk is obtained from the ring map corresponding under
`Spec` to `Spec (𝒪_{T,x}) → T → Spec R`. The quotient equivalence is characterized on germs.

Source: Stacks Project, Properties, Tags 033M and 04MU; Algebra, Tag 00PD (4);
Schemes, Tag 0HA1 (blueprint: lem-sfb-regular-trait-curve-surface-components).

Proof:
1. Apply `rem-pc-regular-normal` to decompose the Noetherian regular scheme into its finitely
   many disjoint clopen integral components. Their open subscheme stalks are the ambient
   stalks (`def-weil-open-immersion`), hence the components are regular. The empty scheme
   gives the empty family.
2. A component's generic stalk is a field (`lem-sc-scheme-sober` and
   `lem-sc-rational-functions-generic-stalks`). If its generic point lay over the closed
   base point, locality would kill π in this field, whereas flatness makes multiplication
   by π injective (`lem-trf-flat-module-torsionfree-domain`). Thus it meets the generic fibre.
3. Properness makes the component's image closed, so it is all of the trait. It meets the
   special fibre, and a closed specialization exists by
   `lem-sc-quasi-compact-kolmogorov-closed-point`. The hypothesis makes the ambient stalk
   there two-dimensional. Open restriction and `lem-pc-scheme-dimension-local-rings`,
   together with the upper bound on all stalk dimensions, give component dimension two.
4. A special-fibre component's generic point corresponds on an affine neighbourhood to
   a minimal prime (`lem-weil-pbc-spec-irreducible-components-minimal-primes`). Reducedness,
   `lem-weil-pbc-affine-open-stalk-localization` and
   `lem-weil-pbc-minimal-prime-reduced-localization-field` make its fibre stalk a field,
   hence its own residue field (`def-weil-residue-field`).
5. The ambient stalk is a Noetherian local domain by regularity and normality. Flatness
   makes the image t of π nonzero. By `lem-sbc-scheme-fibre-stalk-quotient`, its quotient
   by (t) is the fibre stalk, hence a field by step 4. Thus its maximal ideal is (t).
   Apply `lem-sc-principal-ideal-dvr`. Composing the quotient identification with the
   residue map gives the asserted canonical residue-field identification. -/
theorem regular_trait_curve_surface_components
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (T : Scheme.{u}) (g : T ⟶ Spec (.of R)) [IsProper g] [Flat g] [IsNoetherian T]
    (hregular : IsRegularScheme T) [IsReduced (g.fiber (IsLocalRing.closedPoint R))]
    (hdim : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 2)
    (hclosed : ∀ x : g.fiber (IsLocalRing.closedPoint R),
      IsClosed ({x} : Set (g.fiber (IsLocalRing.closedPoint R))) →
        ringKrullDim (T.presheaf.stalk (g.fiberι (IsLocalRing.closedPoint R) x)) = 2) :
    (∃ (n : ℕ) (U : Fin n → T.Opens),
      (∀ i : Fin n, IsClosed (U i : Set T)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (U i) (U j)) ∧
      (⨆ i : Fin n, U i) = ⊤ ∧
      ∀ i : Fin n, IsIntegral (U i).toScheme ∧ IsRegularScheme (U i).toScheme ∧
        topologicalKrullDim (U i).toScheme = 2 ∧
        (∃ x : g.fiber (genericPoint (Spec (.of R))),
          g.fiberι (genericPoint (Spec (.of R))) x ∈ U i) ∧
        (∃ x : g.fiber (IsLocalRing.closedPoint R),
          g.fiberι (IsLocalRing.closedPoint R) x ∈ U i)) ∧
    ∀ (Z : Set (g.fiber (IsLocalRing.closedPoint R))),
      Z ∈ irreducibleComponents (g.fiber (IsLocalRing.closedPoint R)) →
      ∀ ξ : g.fiber (IsLocalRing.closedPoint R), IsGenericPoint ξ Z →
        ∃ hdomain : IsDomain (T.presheaf.stalk (g.fiberι (IsLocalRing.closedPoint R) ξ)),
          @IsDiscreteValuationRing (T.presheaf.stalk (g.fiberι (IsLocalRing.closedPoint R) ξ))
            inferInstance hdomain ∧
          (Spec.preimage (T.fromSpecStalk (g.fiberι (IsLocalRing.closedPoint R) ξ) ≫ g)).hom π
            ≠ 0 ∧
          IsLocalRing.maximalIdeal (T.presheaf.stalk (g.fiberι (IsLocalRing.closedPoint R) ξ)) =
            Ideal.span
              {(Spec.preimage
                (T.fromSpecStalk (g.fiberι (IsLocalRing.closedPoint R) ξ) ≫ g)).hom π} ∧
          ∃ e : (T.presheaf.stalk (g.fiberι (IsLocalRing.closedPoint R) ξ) ⧸
              Ideal.span {(Spec.preimage
                (T.fromSpecStalk (g.fiberι (IsLocalRing.closedPoint R) ξ) ≫ g)).hom π}) ≃+*
              (g.fiber (IsLocalRing.closedPoint R)).residueField ξ,
            ∀ a : T.presheaf.stalk (g.fiberι (IsLocalRing.closedPoint R) ξ),
              e (Ideal.Quotient.mk _ a) =
                (g.fiber (IsLocalRing.closedPoint R)).residue ξ
                  ((g.fiberι (IsLocalRing.closedPoint R)).stalkMap ξ a) := by
  sorry

end AlgebraicGeometry
