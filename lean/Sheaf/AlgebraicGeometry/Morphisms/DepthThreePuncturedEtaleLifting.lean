/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.RingTheory.Depth
import Sheaf.AlgebraicGeometry.Morphisms.DepthThreePuncturedFiniteFlatModel
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteUnramifiedPrincipalQuotient

/-!
# Lifting a punctured finite etale cover from a principal quotient

Source: Stacks Project, Tag 0BLM, `pione-lemma-lift-purity`.
(blueprint: lem-sbc-depth-three-punctured-etale-lifting)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- At depth at least three, extending the actual quotient restriction suffices.

Source: Stacks Project, Tag 0BLM, Lemma 58.20.7, and its proof through Tag 0BLS.
(blueprint: lem-sbc-depth-three-punctured-etale-lifting)

Proof: Because f lies in the maximal ideal, the inverse image V of the punctured
spectrum under Spec(A/(f)) to Spec A is precisely the punctured quotient spectrum.
Depth at least three kills the first and second local cohomology of A supported
at its maximal ideal (47.11.1), so in particular both are annihilated by a power
of f. Apply 0BLS to the cover q and the supplied extension of its actual pullback
to V. For completeness, 0BLS first passes to the complete local ring by 0BLL;
flat base change preserves the local-cohomology hypothesis. Over the complete
ring the pair (A,(f)) is henselian, so the finite etale quotient extension lifts
to a finite etale A-algebra (09ZL). The local-cohomology restriction comparison
0BM6 identifies its punctured spectrum with the original cover. The completion
descent of 0BLL returns the finite etale extension over A. All identifications
are over the punctured base, giving the morphism equality in the conclusion.
The zero finite algebra handles the empty cover. No regularity or nonzerodivisor
condition on f is used in this depth-three lifting criterion. -/
theorem exists_finite_etale_extension_of_depth_three_of_quotient_extension
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q] [Etale q]
    (hquot :
      let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      let V := i ⁻¹ᵁ U
      ∃ (F₀ : Scheme.{u}) (r₀ : F₀ ⟶ Spec (.of (A ⧸ Ideal.span {f}))),
        IsFinite r₀ ∧ Etale r₀ ∧
          ∃ e₀ : pullback q (i ∣_ U) ≅ (r₀ ⁻¹ᵁ V).toScheme,
            e₀.hom ≫ r₀ ∣_ V = pullback.snd q (i ∣_ U)) :
    ∃ (F : Scheme.{u}) (r : F ⟶ Spec (.of A)), IsFinite r ∧ Etale r ∧
      ∃ e : Y ≅ (r ⁻¹ᵁ U).toScheme, e.hom ≫ r ∣_ U = q := by
  obtain ⟨F, r, hfinite, hflat, hquotient, e, he⟩ :=
    exists_finite_flat_model_of_depth_three_of_quotient_extension A f hf hdepth U hU q hquot
  let : IsFinite r := hfinite
  let : Flat r := hflat
  let : FormallyUnramified r :=
    formallyUnramified_of_finite_of_principal_quotient_etale A f hf r hquotient
  exact ⟨F, r, hfinite, Etale.of_formallyUnramified_of_flat r, e, he⟩

end AlgebraicGeometry.Scheme
