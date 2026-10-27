/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth
import WeilConjectures.RingTheory.SingularIdeal

/-!
# Smooth principal neighbourhoods at regular points with separable residue

Source: Stacks Project, Algebra, Tags 00TV and 00TB; Schemes, Tag 01I3;
Morphisms, Tag 01V6
(blueprint: lem-sfb-regular-separable-affine-smooth-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A regular prime with finite separable residue in a finite type affine chart has a smooth
principal neighbourhood. For every such localization, its spectrum identifies with the image
of the principal open in the ambient scheme, compatibly with the given map to `Spec k`.
The equation `hbase` says precisely that the algebra structure on the section ring is the one
induced by `f`; it does not require the ambient scheme or morphism to be affine or finite type.

Source: Stacks Project, Algebra, Tag 00TV, `lemma-separable-smooth`, (2) implies (1),
and Tag 00TB, `definition-smooth-at-prime`; Schemes, Tag 01I3,
`lemma-standard-open-affine`; Morphisms, Tag 01V6, `lemma-smooth-characterize`
(blueprint: lem-sfb-regular-separable-affine-smooth-neighbourhood).

Proof:
1. The finite separable residue extension is separable in the general field-extension sense
   of `def-weil-pbc-separable-field-extension`: every finitely generated intermediate field
   remains separable algebraic, so its empty family is a transcendence basis
   (`def-weil-pbc-separable-algebraic-extension`, `def-weil-pbc-transcendence-basis`).
2. Apply `lem-weil-pbc-regular-local-separable-residue-smooth` to the finite type section
   algebra and its regular localization at `q`. Unfold smoothness at a prime from
   `def-weil-pbc-singular-ideal` to obtain `g` outside `q` with smooth principal localization.
3. For any such `g`, `lem-weil-pbc-affine-open-section-vanishing-prime` identifies the image
   of `D(g)` with the affine principal open whose section ring is the localization at `g`.
   The restriction localization gives the isomorphism `e`; its composite into `X` is the
   canonical localization map followed by `hU.fromSpec`. Functoriality and uniqueness of
   Spec (`def-weil-affine-spectrum`), together with `hbase`, identify the composite to
   `Spec k` with the map induced by `k → Γ(X, U) → Localization.Away g`.
   Since `g` is outside `q`, the point `hU.fromSpec q` lies in this image.
4. `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` makes the localized structural map
   smooth. Transport across `e` using clause (c) of
   `lem-weil-pbc-smooth-restrict-open-subschemes` to obtain smoothness of the restriction
   of `f` to that open. The argument applies to every `g` satisfying the algebraic clause. -/
theorem exists_smooth_principal_neighbourhood_of_regular_separable_residue
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (U : X.Opens) (hU : IsAffineOpen U) [Algebra k Γ(X, U)]
    (hbase : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))))
    [Algebra.FiniteType k Γ(X, U)] (q : PrimeSpectrum Γ(X, U))
    [IsRegularLocalRing (Localization.AtPrime q.asIdeal)]
    [Module.Finite k q.asIdeal.ResidueField] [Algebra.IsSeparable k q.asIdeal.ResidueField] :
    (∃ g : Γ(X, U), g ∉ q.asIdeal ∧ Algebra.Smooth k (Localization.Away g)) ∧
      ∀ g : Γ(X, U), g ∉ q.asIdeal → Algebra.Smooth k (Localization.Away g) →
        hU.fromSpec q ∈ hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen g ∧
        Smooth ((hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen g).ι ≫ f) ∧
        ∃ e : Spec (.of (Localization.Away g)) ≅
            (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen g).toScheme,
          e.hom ≫ (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen g).ι =
            Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away g))) ≫
              hU.fromSpec ∧
          e.hom ≫ (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen g).ι ≫ f =
            Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g))) := by
  sorry

end AlgebraicGeometry
