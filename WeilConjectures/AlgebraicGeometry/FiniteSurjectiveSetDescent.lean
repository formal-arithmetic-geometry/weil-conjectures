/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentEqualizer
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Finite surjective descent of global sections for étale sheaves of sets

## References

* Stacks Project, Étale Cohomology, Remark 09Z3.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The unit on global sections is injective with image exactly the equalizer of the
projection pullbacks, composed with the inverse-image composition comparisons.
(Stacks, Remark 09Z3, following Lemma 09Z2.) -/
theorem finiteSurjectiveSetDescent
    {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] [Surjective f]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Function.Injective (etaleSetDescentUnit f G (Scheme.Etale.mk (𝟙 X))) ∧
      ∀ s' : ((Scheme.etaleSetPullback f).obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
            (Scheme.Etale.mk (𝟙 X)))),
        etaleSetDescentComparison f (pullback.fst f f) G (Scheme.Etale.mk (𝟙 X)) s' =
          eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := f) (g := f)).symm)
            (etaleSetDescentComparison f (pullback.snd f f) G
              (Scheme.Etale.mk (𝟙 X)) s') ↔
          ∃ s : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
            etaleSetDescentUnit f G (Scheme.Etale.mk (𝟙 X)) s = s' := by
  constructor
  · exact finiteSurjectiveSetDescent_injective f G
  · intro s'
    constructor
    · exact finiteSurjectiveSetDescent_compatible_lift f G s'
    · rintro ⟨s, rfl⟩
      have hunit (W : Scheme.{u}) (g : W ⟶ X') :
          etaleSetDescentComparison f g G (Scheme.Etale.mk (𝟙 X))
              (etaleSetDescentUnit f G (Scheme.Etale.mk (𝟙 X)) s) =
            etaleSetDescentUnit (g ≫ f) G (Scheme.Etale.mk (𝟙 X)) s := by
        have h := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
          X X' W f g G (Scheme.Etale.mk (𝟙 X)) s
        unfold etaleSetDescentComparison
        erw [h]
        simp [etaleSetDescentUnit, ← Functor.map_comp_apply, ← op_comp]
      have unit_transport {a b : pullback f f ⟶ X} (e : a = b) :
          eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) e)
            (etaleSetDescentUnit a G (Scheme.Etale.mk (𝟙 X)) s) =
            etaleSetDescentUnit b G (Scheme.Etale.mk (𝟙 X)) s := by
        subst b
        rfl
      exact (hunit _ (pullback.fst f f)).trans
        ((unit_transport ((pullback.condition (f := f) (g := f)).symm)).symm.trans
          (congrArg (fun z ↦ eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := f) (g := f)).symm) z)
            (hunit _ (pullback.snd f f)).symm))


end AlgebraicGeometry
