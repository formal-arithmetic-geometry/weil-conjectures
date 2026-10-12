/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z2
-/
module

public import Sheaf.AlgebraicGeometry.NagataFinitePresentationDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# The selected separated descent stage and model

Source: Weil conjectures blueprint, sec-nagata-compactification, order 368
(blueprint: def-nagata-separated-descent-stage).

The index and transition are selected from the proved upstream separated-stage theorem.
The model and its structure map are the canonical base change along this transition.
The input properties belong to the finite-presentation descent model; the properties of
this selected later model are asserted separately.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (R : NagataRelativeGluingDatum D c hc i₀ f)
    (P : NagataRelativeRawInclusions D c hc i₀ f R)
    (A : NagataRelativeGluingValidStageData D c hc i₀ f R P)
    (G : NagataFinitePresentationGluingData
      (nagataRelativeGluingValidDatum D c hc i₀ f R P A))
    (B : NagataFinitePresentationBaseMap G)
    (E : NagataFinitePresentationComparisonData D c hc i₀ f R P A G B)
    [IsIso (nagataFinitePresentationDescentComparison D c hc i₀ f R P A G B E)]

/-- The inverse of the constructed comparison identifies `X` with the pullback of the
specified finite-presentation model. Source: blueprint orders 362--368
(blueprint: def-nagata-separated-descent-stage).
Proof: the canonical pullback square is cartesian. Transport its upper-left object along
`asIso` of the constructed comparison. Its equation `comparison_base` gives the lower
projection after this transport; the upper projection is the inverse comparison followed
by `pullback.fst`. Thus the transported square is the displayed square. -/
theorem nagataFinitePresentationDescent_isPullback :
    IsPullback
      (inv (nagataFinitePresentationDescentComparison D c hc i₀ f R P A G B E) ≫
        pullback.fst (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)
          (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A))))
      f (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)
      (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A))) := by
  have h := IsPullback.of_hasPullback
    (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)
    (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)))
  refine h.of_iso (asIso (nagataFinitePresentationDescentComparison D c hc i₀ f R P A G B E))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp only [asIso_hom, Iso.refl_hom, Category.comp_id]
    exact E.comparison_base.symm
  · simp
  · simp

variable [IsSeparated f]
    [CompactSpace (D.obj (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)))]
    [QuasiSeparatedSpace (D.obj (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)))]
    [LocallyOfFinitePresentation (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)]
    [QuasiCompact (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)]
    [QuasiSeparated (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)]

/-- The index component of one witness supplied by the proved upstream separated-stage
existence theorem, applied to the constructed model and comparison.
Source: blueprint order 368 (blueprint: def-nagata-separated-descent-stage). -/
noncomputable def nagataSeparatedDescentStage : I :=
  unop (Classical.choose (Scheme.exists_isSeparated_pullback_snd hc
    (nagataFinitePresentationDescent_isPullback D c hc i₀ f R P A G B E)))

/-- The transition component of the same witness; its type records that the selected
stage is later than the relative gluing stage. Source: blueprint order 368
(blueprint: def-nagata-separated-descent-stage). -/
noncomputable def nagataSeparatedDescentTransition :
    op (nagataSeparatedDescentStage D c hc i₀ f R P A G B E) ⟶
      op (nagataRelativeGluingValidStage D c hc i₀ f R P A) :=
  Classical.choose (Classical.choose_spec (Scheme.exists_isSeparated_pullback_snd hc
    (nagataFinitePresentationDescent_isPullback D c hc i₀ f R P A G B E)))

/-- The selected model is exactly the base change of the constructed finite-presentation
model along the transition of the chosen witness. Source: blueprint order 368
(blueprint: def-nagata-separated-descent-stage). -/
noncomputable def nagataSeparatedDescentModel : Scheme.{u} :=
  pullback (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)
    (D.map (nagataSeparatedDescentTransition D c hc i₀ f R P A G B E))

/-- The selected model's structure map is its canonical projection to the selected base.
Source: blueprint order 368 (blueprint: def-nagata-separated-descent-stage). -/
noncomputable def nagataSeparatedDescentMap :
    nagataSeparatedDescentModel D c hc i₀ f R P A G B E ⟶
      D.obj (op (nagataSeparatedDescentStage D c hc i₀ f R P A G B E)) :=
  pullback.snd (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)
    (D.map (nagataSeparatedDescentTransition D c hc i₀ f R P A G B E))

end AlgebraicGeometry
