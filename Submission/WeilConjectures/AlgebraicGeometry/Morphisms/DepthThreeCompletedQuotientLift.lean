/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Submission.WeilConjectures.RingTheory.Depth

import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.CompletedQuotientCoverLift
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.CompletedPuncturedQuotientFullyFaithful

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Lifting the quotient cover over the maximal-ideal completion

Source: Stacks Project, Tags 0BLS, 0BM6, 09ZL and 0AVY.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The prescribed quotient restriction lifts over the completion.

Source: Stacks Project, proof of Tag 0BLS, Tags 0BM6, 09ZL, 0AVY and 0A02.
(blueprint: lem-sbc-depth-three-completed-quotient-lift)

Proof: Write C for the maximal-ideal completion. This is Noetherian and flat over A,
and its closed point is the unique point above the closed point of A. Thus W is
its punctured spectrum. Depth at least three gives zero first and second local
cohomology of A, and flat base change gives the same vanishing for C. Base change
of the supplied finite etale quotient extension to C/fC extends the actual
quotient restriction of the completed cover. Completeness and f in the maximal
ideal make (C,fC) a henselian pair. Tag 09ZL lifts that quotient extension to a
finite etale cover E of Spec C. Tag 0BM6 makes restriction from W to its principal
quotient fully faithful. The common quotient identification therefore lifts to
an isomorphism of covers over W; its inverse lifts too and faithfulness verifies
the inverse identities. Forgetting to schemes gives the stated isomorphism and
its equality over W. This includes f = 0 and the empty cover. -/
theorem exists_completed_etale_extension_of_depth_three_of_quotient_extension
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
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let c := Spec.map (CommRingCat.ofHom (algebraMap A C))
    let W := c ⁻¹ᵁ U
    ∃ (E : Scheme.{u}) (s : E ⟶ Spec (.of C)), IsFinite s ∧ Etale s ∧
      ∃ e : pullback q (c ∣_ U) ≅ (s ⁻¹ᵁ W).toScheme,
        e.hom ≫ s ∣_ W = pullback.snd q (c ∣_ U) := by
  classical
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let c := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let W := c ⁻¹ᵁ U
  let j := Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span {algebraMap A C f})))
  obtain ⟨E, s, hsfin, hset, e₀, he₀⟩ :=
    exists_completed_cover_with_quotient_iso A f hf U q hquot
  let := hsfin
  let := hset
  let P : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ W.toScheme :=
    MorphismProperty.Over.mk ⊤ (pullback.snd q (c ∣_ U))
      ⟨inferInstance, inferInstance⟩
  let Q : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ W.toScheme :=
    MorphismProperty.Over.mk ⊤ (s ∣_ W) ⟨inferInstance, inferInstance⟩
  let F := MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ (j ∣_ W)
  let a₀ : F.obj P ≅ F.obj Q := MorphismProperty.Over.isoMk e₀ he₀
  obtain ⟨hff⟩ := fullyFaithful_completed_punctured_quotient A f hf hdepth U hU
  let a : P ≅ Q := hff.preimageIso a₀
  refine ⟨E, s, hsfin, hset, ?_⟩
  refine ⟨((MorphismProperty.Over.forget _ ⊤ W.toScheme) ⋙
    CategoryTheory.Over.forget W.toScheme).mapIso a, ?_⟩
  exact MorphismProperty.Over.w a.hom

end AlgebraicGeometry.Scheme
