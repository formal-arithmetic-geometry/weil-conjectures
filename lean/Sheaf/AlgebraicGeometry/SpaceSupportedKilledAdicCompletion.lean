module

public import Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem

/-! # Completion on the subcategories supported on a fixed closed thickening

Source: Stacks Project, spaces-more-morphisms.tex, Tag 08BC,
lemma-existence-tricky, first two displayed full-subcategory identifications in the proof
(blueprint: def-sfb-space-supported-killed-adic-completion).

The closed thickening cut out by K^q is encoded by its exact ambient full subcategories,
as in the source. The functor is the existing canonical quotient-diagram completion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Coherent modules with proper closed carrier over the target of f, killed by K^q.
Source: Stacks 08BC, proof, first full-subcategory identification
(blueprint: def-sfb-space-supported-killed-adic-completion). -/
def supportedCoherentKilled {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (K : QuasiCoherentIdeal X) (q : ℕ) : ObjectProperty X.Modules :=
  fun H ↦ H.IsQuasicoherent ∧
    (∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
      ((X.schemeRestriction T).obj H)) ∧
    CoherentAdicHasProperSupportOver f ((Functor.const ℕᵒᵖ).obj H) ∧ AdicPowerKills K q H

/-- Coherent J-adic systems with proper first-term support, whose every term is killed
by K^q. Source: Stacks 08BC, proof, second full-subcategory identification
(blueprint: def-sfb-space-supported-killed-adic-completion). -/
def supportedAdicKilled {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (J K : QuasiCoherentIdeal X) (q : ℕ) :
    ObjectProperty (ℕᵒᵖ ⥤ X.Modules) :=
  fun F ↦ IsCoherentAdicSystem J F ∧ CoherentAdicHasProperSupportOver f F ∧
    ∀ n : ℕ, AdicPowerKills K q (F.obj (op n))

/-- The canonical J-completion is an equivalence on the two full subcategories belonging
to the closed thickening K^q = 0: it lands there, is bijective on every hom set, and is
essentially surjective. Bijectivity uses the actual completion map on arrows.
Source: Stacks 08BC, proof, paragraph following the two full-subcategory identifications
(blueprint: def-sfb-space-supported-killed-adic-completion). -/
def SupportedKilledAdicCompletionEquivalence {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (J K : QuasiCoherentIdeal X) (q : ℕ) : Prop :=
  (∀ H : X.Modules, supportedCoherentKilled f K q H →
    supportedAdicKilled f J K q ((coherentAdicCompletionDiagram J).obj H)) ∧
  (∀ F G : X.Modules, supportedCoherentKilled f K q F →
    supportedCoherentKilled f K q G →
      Function.Bijective (fun g : F ⟶ G ↦ (coherentAdicCompletionDiagram J).map g)) ∧
  (∀ F : ℕᵒᵖ ⥤ X.Modules, supportedAdicKilled f J K q F →
    ∃ H : X.Modules, supportedCoherentKilled f K q H ∧
      Nonempty ((coherentAdicCompletionDiagram J).obj H ≅ F))

end AlgebraicGeometry.AlgebraicSpace
