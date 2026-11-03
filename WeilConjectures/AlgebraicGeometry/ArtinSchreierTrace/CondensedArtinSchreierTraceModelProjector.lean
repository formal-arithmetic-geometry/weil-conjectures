/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! The universal condensed comparison projector is the recorded Artin--Schreier
projector.  This is the projector-level coherence needed to identify the two
implementations of the degree-q sheaf.

Source: the condensed-coefficients paragraph of `def-fd-artin-schreier-sheaf`
and clause (2) of `lem-wft-as-comparison`.
(blueprint: lem-fd-as-lisse-condensed-model-projector).

Proof: unfold both finite sums.  For each translation, identify the adjoint of
the inverse monoidal unit with `condensedPushforwardHom` by
`CondensedRing.homEquiv_εIso_inv_hom`; use the canonical lower-star composition
and equality transports, and then identify the scalar endomorphism by
`Mod.regularEndRingHom`.  The finite sums then agree term by term. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

/-- One translation term: the pulled-back regular section of `condensedPull` is the adjoint
of the inverse unit comparison, by `CondensedRing.homEquiv_εIso_inv_hom`. -/
private theorem pull_eq_translationAction {X Y : Scheme.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (t : X ⟶ X) (g : X ⟶ Y) (h : t ≫ g = g) :
    (ProEtale.CondensedRing.lowerStar Λ g).map
        (Mod.regularLift ((ProEtale.CondensedRing.lowerStar Λ t).obj (condensedUnit Λ X))
          (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ t)) ≫
      (ProEtale.CondensedRing.lowerStarComp Λ t g).hom.app _ ≫
        (ProEtale.CondensedRing.lowerStarCongr Λ h).hom.app _ =
    (ProEtale.CondensedRing.lowerStar Λ g).map
        (((ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ t).homEquiv _ _)
          (Functor.Monoidal.εIso (ProEtale.CondensedRing.upperStar Λ t)).inv) ≫
      (ProEtale.CondensedRing.lowerStarComp Λ t g).hom.app _ ≫
        eqToHom (congrArg (fun s ↦ (ProEtale.CondensedRing.lowerStar Λ s).obj
          (Mod.regular (ProEtale.condensedRingObj Λ X))) h) := by
  have h1 : Mod.regularLift ((ProEtale.CondensedRing.lowerStar Λ t).obj (condensedUnit Λ X))
      (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ t) =
      ((ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ t).homEquiv _ _)
        (Functor.Monoidal.εIso (ProEtale.CondensedRing.upperStar Λ t)).inv := by
    apply Mod.regular_hom_ext
    rw [Mod.one_comp_regularLift]
    erw [ProEtale.CondensedRing.homEquiv_εIso_inv_hom]
  erw [h1]
  simp only [ProEtale.CondensedRing.lowerStarCongr, eqToIso.hom, eqToHom_app]
  rfl

/-- Projector-level identification between the comparison and recorded models.
(blueprint: lem-fd-as-lisse-condensed-model-projector). -/
theorem condensed_trace_projector_eq_artin_projector
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
    (χ : AddChar k (MonObj.Γ Λ)) :
    condensedProjector Λ k
        (Over.mk (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)))
        (fun c ↦ Over.homMk (Etale.artinSchreierTranslation k c)
          (Etale.artinSchreierTranslation_comp_artinSchreierMap k c)) χ =
      ProEtale.condensedArtinSchreierProjector Λ k χ := by
  unfold condensedProjector ProEtale.condensedArtinSchreierProjector
  refine Finset.sum_congr rfl fun c _ ↦ congrArg (· ≫ _) ?_
  unfold condensedPull ProEtale.condensedArtinSchreierTranslationAction
  exact pull_eq_translationAction Λ (Etale.artinSchreierTranslation k c)
    (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))
    (Etale.artinSchreierTranslation_comp_artinSchreierMap k c)

end AlgebraicGeometry.ArtinSchreierTrace
