module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.Depth

import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.AlgebraicGeometry.Morphisms.RegularLocalPuncturedEtalePurity
import Sheaf.AlgebraicGeometry.Morphisms.LocalPurityDepthTwoFiniteFlatStalk
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtension
import Sheaf.AlgebraicGeometry.Morphisms.FlatDepthTwoFiniteFormallyUnramified

/-!
# Finite etale model across a regular codimension-two boundary

Source: Stacks Project, Tags 0BMA and 0EY7.
(blueprint: lem-sbc-regular-codimension-two-finite-etale-model)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem depth_two_of_regular_local (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim R) :
    (2 : ℕ∞) ≤ IsLocalRing.depth (R := R) R := by
  classical
  let m := IsLocalRing.maximalIdeal R
  obtain ⟨s, hcard, hs⟩ :=
    (IsNoetherian.noetherian m).exists_span_finset_card_eq_spanFinrank
  let rs := s.toList
  have hspan : Ideal.span {x | x ∈ rs} = m := by
    simpa [rs] using hs
  have hdim' : ringKrullDim R = (rs.length : WithBot ℕ∞) := by
    simpa [rs, hcard, m] using
      (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  have hparams : IsLocalRing.IsRegularSystemOfParameters rs := ⟨hspan, hdim'.symm⟩
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    R rs.length hdim' rs hparams).1
  have hdepth : (rs.length : ℕ∞) ≤ IsLocalRing.depth (R := R) R := by
    unfold IsLocalRing.depth Ideal.depth
    split_ifs
    · exact le_top
    · apply le_sSup
      refine ⟨rs, hreg, ?_, rfl⟩
      intro x hx
      change x ∈ m
      rw [← hspan]
      exact Ideal.subset_span hx
  have htwo : (2 : ℕ∞) ≤ (rs.length : ℕ∞) := by
    rw [hdim'] at hdim
    exact WithBot.coe_le_coe.mp hdim
  exact htwo.trans hdepth

/-- A finite etale restriction extends across a regular codimension-two boundary.

Source: Stacks Project, Tags 0BMA, 0EY7, and 0EY6(2).
(blueprint: lem-sbc-regular-codimension-two-finite-etale-model)

Proof: At every boundary point, a regular system of parameters is a regular
sequence of length the Krull dimension. Its length is one of the lengths
in the supremum defining depth, so the target stalk has depth at least two.
Apply the global depth-two finite extension theorem to the etale restriction
of p over V. This gives a finite r with source depth at least two over the
boundary and the prescribed isomorphism over V.

Tag 0BMA gives punctured local purity at each boundary stalk. Apply the
local-purity flatness theorem to r: its finite flat target locus contains V;
if its closed complement were nonempty, an irreducible-component generic
point s would have all proper generalizations in that locus. Over Spec O(L,s),
the punctured restriction is etale by flat depth-two purity. Local purity
extends it to a finite etale model. Depth-two uniqueness identifies the
model with the base change of r, and flat descent puts s in the flat locus,
a contradiction. Hence r is flat everywhere.

The flat depth-two extension criterion makes r formally unramified. Its
finiteness gives local finite presentation, so r is etale. Retain the source
boundary depth bound and invert the restriction isomorphism to obtain the
required comparison with p. No global quasi-compactness or quasi-separatedness
is needed. Empty covers and V = L are included in the same argument. -/
theorem exists_finite_etale_depth_two_model
    {L E : Scheme.{u}} [IsLocallyNoetherian L] (V : L.Opens)
    (hboundary : ∀ y : L, y ∉ V → IsRegularLocalRing (L.presheaf.stalk y) ∧
      (2 : WithBot ℕ∞) ≤ ringKrullDim (L.presheaf.stalk y))
    (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ V)] :
    ∃ (F : Scheme.{u}) (r : F ⟶ L), IsFinite r ∧ Etale r ∧
      (∀ z : F, r z ∉ V →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk z) (F.presheaf.stalk z)) ∧
      ∃ e : (p ⁻¹ᵁ V).toScheme ≅ (r ⁻¹ᵁ V).toScheme,
        e.hom ≫ r ∣_ V = p ∣_ V := by
  have hdepth : ∀ y : L, y ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y) (L.presheaf.stalk y) := by
    intro y hy
    obtain ⟨hreg, hdim⟩ := hboundary y hy
    let := hreg
    exact depth_two_of_regular_local _ hdim
  obtain ⟨F, r, hfin, hsource, e, he⟩ :=
    exists_finite_extension_of_depth_two V hdepth (p ∣_ V)
  let := hfin
  have : Etale (r ∣_ V) := by
    rw [← he]
    infer_instance
  have : Flat r := by
    refine flat_of_local_purity_depth_two_finite_extension V hdepth ?_ r hsource
    intro y hy U hU Z q hq hqe
    obtain ⟨hreg, hdim⟩ := hboundary y hy
    let := hreg
    let := hq
    let := hqe
    exact exists_finite_etale_extension_of_regular_local_punctured_spectrum
      (L.presheaf.stalk y) hdim U hU q
  have : FormallyUnramified r :=
    formallyUnramified_of_flat_depth_two_finite_extension V r hsource
  refine ⟨F, r, hfin, Etale.of_formallyUnramified_of_flat r, hsource, e.symm, ?_⟩
  rw [← he]
  simp

end AlgebraicGeometry.Scheme
