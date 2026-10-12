/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z2
-/
module

public import Sheaf.AlgebraicGeometry.NagataFinalDescendedModel
import Sheaf.AlgebraicGeometry.FinalNoetherianBaseSystemProperties
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Properties of the final descended model

Source: Weil conjectures blueprint, sec-nagata-compactification, order 374
(blueprint: lemma-nagata-final-descended-model).
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

variable [IsSeparated f]
    [CompactSpace (D.obj (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)))]
    [QuasiSeparatedSpace (D.obj (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)))]
    [LocallyOfFinitePresentation (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)]
    [QuasiCompact (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)]
    [QuasiSeparated (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)]

/-- The selected model is separated and of finite presentation over its Noetherian stage,
and its constructed comparison is an isomorphism over the original base.
Source: Weil conjectures blueprint, sec-nagata-compactification, order 374
(blueprint: lemma-nagata-final-descended-model).

Proof: (1) By `def-nagata-final-descended-model`, this is the selected separated-descent
model. Apply `lemma-nagata-separated-eventually` to the separated finite-presentation map
`f`: the separated-stage construction gives separatedness, while base change preserves
finite presentation. Its canonical comparison with `X` is the finite-presentation
comparison transported through pullback reassociation, hence is an isomorphism. The
comparison's base equation and the pullback reassociation equations show it is over `c.pt`.
(2) By `lemma-nagata-final-noetherian-base-system`, the stage of the supplied approximation
is Noetherian. Transfer this property along `Q.diagramIso` at the selected index. -/
theorem nagataFinalDescendedModel_properties (Q : NagataFinalBaseSystemIdentification D c) :
    IsSeparated (nagataFinalDescendedMap D c hc i₀ f R P A G B E Q) ∧
    LocallyOfFinitePresentation (nagataFinalDescendedMap D c hc i₀ f R P A G B E Q) ∧
    QuasiCompact (nagataFinalDescendedMap D c hc i₀ f R P A G B E Q) ∧
    QuasiSeparated (nagataFinalDescendedMap D c hc i₀ f R P A G B E Q) ∧
    IsNoetherian (D.obj (op (nagataFinalDescendedStage D c hc i₀ f R P A G B E Q))) ∧
    IsIso (nagataFinalDescendedComparison D c hc i₀ f R P A G B E Q) ∧
    nagataFinalDescendedComparison D c hc i₀ f R P A G B E Q ≫ f =
      pullback.snd (nagataFinalDescendedMap D c hc i₀ f R P A G B E Q)
        (c.π.app (op (nagataFinalDescendedStage D c hc i₀ f R P A G B E Q))) := by
  sorry

end AlgebraicGeometry
