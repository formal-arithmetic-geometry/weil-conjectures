/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.RingTheory.SingularIdeal

import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# A smooth principal neighbourhood from smoothness at a chart prime

Source: Stacks Project, More on Morphisms, Tag 02H6, and Morphisms,
`lemma-smooth-at-point`, final affine-to-scheme passage
(blueprint: lem-trf-affine-smooth-prime-scheme-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Smoothness of the chart algebra at a prime gives a principal open neighbourhood
smooth over the original target. The chart inclusions are the open immersions `iW`
and `iV`; `hchart` says that the algebra structure is the induced chart ring map.
The point `x` of the node is `iW q`, and its principal neighbourhood is the actual
open subscheme `iW ''ᵁ PrimeSpectrum.basicOpen g` of `X`. The canonical identification
with `Spec (Localization.Away g)` is furnished by the localization open immersion,
`Scheme.Hom.opensRange_localizationAway`, and the chart open immersion.

Source: Stacks Project, Algebra, Definition 00TB; Schemes, Tags 01I3 and 01HI;
More on Morphisms, Tag 02H6; Morphisms, Tags 01V6, 01VC and 01VA, and the final
passage in `lemma-smooth-at-point`
(blueprint: lem-trf-affine-smooth-prime-scheme-neighbourhood).

Proof:
1. Unfold `Algebra.IsSmoothAtPrime` (def-weil-pbc-singular-ideal) and choose its
   witness `g` outside `q` with `Algebra.Smooth R (Localization.Away g)`. This uses
   no finite-presentation assumption on the original algebra `A`.
2. By lem-weil-pbc-principal-localization-open-immersion, the localization spectrum
   is an open subscheme with image `D(g)` in `Spec A`. Composing with `iW` identifies
   it canonically with the displayed image open in `X`. Since `g` avoids `q`,
   this open contains `iW q`. By lem-weil-pbc-morphism-factors-through-open-subscheme
   the restricted map factors through the target chart. The equation `hchart`
   and functoriality of Spec (def-weil-affine-spectrum) identify that map with
   the spectrum of `R → A → Localization.Away g` under the canonical identification.
3. Apply lem-weil-pbc-smooth-ring-map-iff-smooth-affine to this localized algebra.
   Clause (c) of lem-weil-pbc-smooth-restrict-open-subschemes transports smoothness
   through the canonical identification, giving a smooth map to the target chart.
4. Clause (b) of lem-weil-pbc-smooth-restrict-open-subschemes then composes with
   the target open immersion `iV`, yielding the asserted restriction to `S`.
   Together with the witness and membership in step 2 this proves all clauses. -/
theorem exists_principal_open_smooth_of_isSmoothAtPrime
    {X S : Scheme.{u}} (f : X ⟶ S)
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (iW : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion iW]
    (iV : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion iV]
    (hchart : iW ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iV)
    (q : PrimeSpectrum A) (hsmooth : Algebra.IsSmoothAtPrime R q) :
    ∃ g : A, g ∉ q.asIdeal ∧ Algebra.Smooth R (Localization.Away g) ∧
      Smooth ((iW ''ᵁ PrimeSpectrum.basicOpen g).ι ≫ f) ∧
      iW q ∈ iW ''ᵁ PrimeSpectrum.basicOpen g := by
  sorry

end AlgebraicGeometry
