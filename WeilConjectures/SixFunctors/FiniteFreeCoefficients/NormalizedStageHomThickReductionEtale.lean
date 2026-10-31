/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory

/-! Thick-generation reduction for the normalized ordinary-etale stage Hom comparison.

Source: blueprint latest, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraphs 1--2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
namespace WeilConjectures.FiniteFreeCoefficients

/-- A thick comparison locus containing the flat-model generators contains every ctf input.

Proof: install the supplied zero, shift, distinguished-triangle and retract closure witnesses as
`ObjectProperty` instances. The triangulated-envelope induction first contains the zero object,
then shifts and cones, and finally retracts; the generator inclusion transports the result from the
flat-model envelope. This is the categorical devissage used after the generator calculation.
(blueprint: lem-sf-normalized-stage-hom-thick-reduction-etale).
-/
theorem normalized_stage_hom_thick_reduction_etale
    {A : Type (u + 1)} [CommRing A] [Finite A] (X : Scheme.{u})
    (Q : ObjectProperty (Sites.D false A X)ᵒᵖ)
    (hz : ∀ K, IsZero K → Q K)
    (hs : ∀ K (n : ℤ), Q K → Q (K⟦n⟧))
    (ht : ∀ T : Triangle (Sites.D false A X)ᵒᵖ, T ∈ distTriang _ →
      Q T.obj₁ → Q T.obj₂ → Q T.obj₃)
    (hr : ∀ {K L : (Sites.D false A X)ᵒᵖ} (i : K ⟶ L) (r : L ⟶ K),
      i ≫ r = 𝟙 K → Q L → Q K)
    (G : ObjectProperty (Sites.D false A X)) (hg : G ≤ Q.unop)
    {K : Sites.D false A X} (hK : G.triangEnvelope K) : Q (op K) := by
  let : Q.IsStableUnderRetracts := ⟨fun r h ↦ hr r.i r.r r.retract h⟩
  obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := (Sites.D false A X)ᵒᵖ)
  let : Q.ContainsZero := ⟨Z, hZ, hz _ hZ⟩
  let : Q.IsStableUnderShift ℤ := ⟨fun n ↦ .mk (fun K h ↦ hs K n h)⟩
  let : Q.IsTriangulatedClosed₃ := .mk' ht
  let : Q.IsTriangulatedClosed₂ := .of_isTriangulatedClosed₃
  let : Q.IsTriangulated := {}
  let : Q.unop.IsStableUnderRetracts :=
    ⟨fun r ht ↦ Q.prop_of_retract
      { i := r.r.op, r := r.i.op, retract := by
          simpa only [op_comp, op_id] using congrArg Quiver.Hom.op r.retract } ht⟩
  exact ((ObjectProperty.triangEnvelope_le_iff (Q := Q.unop) G).mpr hg) K hK

end WeilConjectures.FiniteFreeCoefficients
