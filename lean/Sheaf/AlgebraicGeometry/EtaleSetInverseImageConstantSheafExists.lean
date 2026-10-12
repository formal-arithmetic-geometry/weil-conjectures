/- helper construction -/
module
public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
abbrev etaleSetInverseImageConstantSheafHom (U V : Scheme.{u}) (v : V ⟶ U) (E : Type u) :=
  (Scheme.etaleSetPullback v).obj
            ((constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
              (ULift.{u + 1, u} E)) ⟶
          (constantSheaf V.smallEtaleTopology (Type (u + 1))).obj
            (ULift.{u + 1, u} E)

def etaleSetInverseImageConstantSheafCondition
    (U V : Scheme.{u}) (v : V ⟶ U) (E : Type u)
    (γ : etaleSetInverseImageConstantSheafHom U V v E) : Prop :=
  (∀ e : E,
        γ.hom.app (Opposite.op ((MorphismProperty.Over.pullback
          (P := @AlgebraicGeometry.Etale) (Q := ⊤) v).obj
          (Scheme.Etale.mk (𝟙 U))))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback
            (P := @AlgebraicGeometry.Etale) (Q := ⊤) v) (Type (u + 1))
            (U.smallGrothendieckTopology @Etale)
            (V.smallGrothendieckTopology @Etale)).unit.app
              ((constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
                (ULift.{u + 1, u} E))).hom.app
            (Opposite.op (Scheme.Etale.mk (𝟙 U)))
            (((toSheafify U.smallEtaleTopology
              ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
                (Opposite.op (Scheme.Etale.mk (𝟙 U))) ⟨e⟩))) =
          (toSheafify V.smallEtaleTopology
            ((Functor.const V.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
            (Opposite.op ((MorphismProperty.Over.pullback
          (P := @AlgebraicGeometry.Etale) (Q := ⊤) v).obj
              (Scheme.Etale.mk (𝟙 U)))) ⟨e⟩)

/-- Construction of the canonical isomorphism and its section equations.
(blueprint: new-etaleSetInverseImageConstantSheaf-existence) -/
theorem etaleSetInverseImageConstantSheaf_exists
    (U V : Scheme.{u}) (v : V ⟶ U) (E : Type u) :
    ∃ γ : etaleSetInverseImageConstantSheafHom U V v E,
      etaleSetInverseImageConstantSheafCondition U V v E γ ∧ IsIso γ := by
  sorry
end AlgebraicGeometry
