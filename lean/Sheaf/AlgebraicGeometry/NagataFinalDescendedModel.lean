/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z2
-/
module

public import Sheaf.AlgebraicGeometry.NagataSeparatedDescentStage
public import Sheaf.AlgebraicGeometry.GluedLimitComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Sheaf.AlgebraicGeometry.FinalNoetherianBaseSystemProperties

/-!
# The final descended model and its constructed comparison

Source: Weil conjectures blueprint, sec-nagata-compactification, order 373
(blueprint: def-nagata-final-descended-model).
-/

@[expose] public section

universe u

set_option genInjectivity false
set_option genSizeOf false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Identification of a directed presentation with the supplied final Noetherian system.
The diagram is the reindexing of the approximation, and its cone projections are the
same projections after this identification. The surrounding limit cone certifies that
the reindexing retains the limit. Source: blueprint orders 371--373
(blueprint: def-nagata-final-descended-model). -/
structure NagataFinalBaseSystemIdentification {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) where
  approximation : c.pt.NoetherianApproximation
  reindex : Iᵒᵖ ⥤ approximation.I
  diagramIso : D ≅ reindex ⋙ approximation.D
  projection_eq : ∀ i, c.π.app i ≫ diagramIso.hom.app i =
    approximation.π.app (reindex.obj i)

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

variable [IsSeparated f]
    [CompactSpace (D.obj (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)))]
    [QuasiSeparatedSpace (D.obj (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)))]
    [LocallyOfFinitePresentation (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)]
    [QuasiCompact (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)]
    [QuasiSeparated (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)]


/-- The final index is the already selected separated-descent index, with the supplied
identification of the base system. Source: blueprint order 373
(blueprint: def-nagata-final-descended-model). -/
noncomputable def nagataFinalDescendedStage
    (_Q : NagataFinalBaseSystemIdentification D c) : I :=
  nagataSeparatedDescentStage D c hc i₀ f R P A G B E

/-- The final model is exactly the selected separated model; no new model is chosen.
Source: blueprint order 373 (blueprint: def-nagata-final-descended-model). -/
noncomputable def nagataFinalDescendedModel
    (_Q : NagataFinalBaseSystemIdentification D c) : Scheme.{u} :=
  nagataSeparatedDescentModel D c hc i₀ f R P A G B E

/-- The final structure map is the selected separated model's canonical projection.
Source: blueprint order 373 (blueprint: def-nagata-final-descended-model). -/
noncomputable def nagataFinalDescendedMap
    (Q : NagataFinalBaseSystemIdentification D c) :
    nagataFinalDescendedModel D c hc i₀ f R P A G B E Q ⟶
      D.obj (op (nagataFinalDescendedStage D c hc i₀ f R P A G B E Q)) :=
  nagataSeparatedDescentMap D c hc i₀ f R P A G B E

/-- The constructed comparison is the canonical reassociation of the successive base
changes, followed by the existing finite-presentation comparison. Cone compatibility
identifies the composite base projection with the original one.
Source: blueprint order 373 (blueprint: def-nagata-final-descended-model). -/
noncomputable def nagataFinalDescendedComparison
    (Q : NagataFinalBaseSystemIdentification D c) :
    pullback (nagataFinalDescendedMap D c hc i₀ f R P A G B E Q)
      (c.π.app (op (nagataFinalDescendedStage D c hc i₀ f R P A G B E Q))) ⟶ X :=
  (pullbackLeftPullbackSndIso
    (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)
    (D.map (nagataSeparatedDescentTransition D c hc i₀ f R P A G B E))
    (c.π.app (op (nagataSeparatedDescentStage D c hc i₀ f R P A G B E)))).hom ≫
  (pullback.congrHom rfl
    (c.w (nagataSeparatedDescentTransition D c hc i₀ f R P A G B E))).hom ≫
  nagataFinitePresentationDescentComparison D c hc i₀ f R P A G B E

end AlgebraicGeometry
