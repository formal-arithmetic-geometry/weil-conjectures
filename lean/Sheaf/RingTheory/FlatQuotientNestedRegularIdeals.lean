module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Regular.Flat
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Algebra.Homology.DerivedTensorModuleTorComparison

/-!
# Regular generation of nested ideals with a flat quotient

Source: Stacks Project, Divided Power Algebra, Tag 09PX (lemma-perfect-map-ci),
equivalence of (1) and (3), with the quotient map flat.
(blueprint: lem-sfb-flat-quotient-nested-regular-ideals).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingTheory.Sequence

/-- For a flat local map with regular closed fibre and a flat induced quotient map,
regular generation of the target ideal is equivalent to regular generation of the source
ideal and of the relative ideal. All sequences are finite lists, possibly empty.
The maximal ideal of `S / IS` is written as the image of the maximal ideal of `S`.

Source: Stacks Project, Divided Power Algebra, Tag 09PX (lemma-perfect-map-ci),
equivalence of (1) and (3), specialized to a flat quotient map.
(blueprint: lem-sfb-flat-quotient-nested-regular-ideals).

Proof:
1. Put `A = R/I`, `B = S/IS`, and `M = S/J`. The proper-ideal hypotheses give
   nonzero local quotient rings, by lem-weil-pbc-quotient-local-structure.
   Surjective images are Noetherian by lem-weil-pbc-surjective-image-noetherian.
   Identify `B` canonically with `A ⊗[R] S`; flat base change
   (lem-weil-pbc-flat-module-base-change) makes `A → B` flat and local. Its closed
   fibre is `S / m_R S`. The original flat local map is faithfully flat by
   lem-weil-pbc-flat-local-hom-faithfully-flat.
2. Given regular generators of `I` and `J/IS`, lift the latter to `J`. The former
   stay regular in `S` by lem-sfb-regular-sequence-faithfully-flat-ascent.
   Concatenate the image list with the lifted list. It generates `J`, since reducing
   an element modulo `IS` expresses it in the second list, leaving an element of `IS`.
   Its successive quotients identify with those defining the two original lists;
   its final quotient is the nonzero ring `S/J`. Thus it is regular, including
   when either list is empty (def-weil-pbc-regular-sequence).
3. Conversely, suppose `J` is regularly generated. The cyclic finite `B`-module
   `M` in degree zero is pseudo-coherent by
   lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion. Flatness over `A`
   gives Tor amplitude `[0,0]`, by lem-trf-source-bounded-flat-tor-amplitude;
   in particular its derived residue tensor has cohomology only in degree zero.
4. Apply lem-sfb-regular-fibre-local-perfect to `A → B` and `M[0]`. If the
   regular closed fibre has dimension `d`, its derived tensor with every `B`-module
   vanishes outside `[-d,0]`. By lem-kun-derived-module-tor-comparison this gives
   finite Tor dimension of `M` over `B`.
5. Apply lem-sfb-nested-regular-ideals-finite-tor to `IS ⊆ J` in `S`.
   It yields regular generators of `IS` and `J/IS`.
6. Choose a residue-field basis of `I/m_R I` and lifts `f_i` in `I`, using
   lem-weil-pbc-residue-extension-minimal-generators. They generate `I`.
   Flatness identifies `I ⊗[R] S` with `IS`. Tensor right exactness
   (lem-weil-pbc-tensor-right-exact) gives
   `IS/m_S IS ≅ (I/m_R I) ⊗[k_R] k_S`, carrying the images of `f_i` to the
   scalar-extended basis. These images are therefore minimal generators of `IS`.
7. Apply lem-trf-lift-regular-generators-through-fibre with both local rings `S`
   and the identity homomorphism. The regular generation from step 5 implies that
   this particular minimal generating list of `IS` is regular. Only the identity
   map needs to induce a residue-field isomorphism; none is assumed for `R → S`.
8. For each initial segment of the `f_i`, tensoring its quotient with `S` gives
   the corresponding quotient by their images (lem-weil-pbc-tensor-right-exact).
   Multiplication by the next element becomes injective after tensoring, by step 7.
   Faithful flatness reflects this injectivity
   (def-weil-pbc-faithfully-flat-ring-map). Since `R/I` is nonzero, the lifted list
   is regular in `R` (def-weil-pbc-regular-sequence). Together with step 5 this
   proves the converse. Properness puts every generator in its maximal ideal.
-/
theorem exists_regular_generators_iff_source_quotient_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] (hφ : φ.Flat)
    (hF : IsRegularLocalRing (S ⧸ (IsLocalRing.maximalIdeal R).map φ))
    (I : Ideal R) (J : Ideal S)
    (hI : I ≤ IsLocalRing.maximalIdeal R) (hJ : J ≤ IsLocalRing.maximalIdeal S)
    (hIJ : I ≤ J.comap φ) (hQ : (Ideal.quotientMap J φ hIJ).Flat) :
    (∃ fs : List S, Ideal.ofList fs = J ∧ IsRegular S fs ∧
      ∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal S) ↔
    (∃ fs : List R, Ideal.ofList fs = I ∧ IsRegular R fs ∧
      ∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R) ∧
    (∃ gs : List (S ⧸ I.map φ),
      Ideal.ofList gs = J.map (Ideal.Quotient.mk (I.map φ)) ∧
      IsRegular (S ⧸ I.map φ) gs ∧
      ∀ g ∈ gs, g ∈ (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk (I.map φ))) := by
  sorry

end RingTheory.Sequence
