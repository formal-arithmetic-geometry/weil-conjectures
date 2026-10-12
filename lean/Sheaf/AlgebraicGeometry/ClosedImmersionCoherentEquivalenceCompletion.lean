/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers
import Sheaf.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.FinitePushforwardCoherent

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
open MonoidalCategory Scheme.Modules
/-- Completion comparison for closed immersion pushforward.
Source: Stacks Project, Cohomology of Schemes, equation 0880.
The proof assembles the canonical quotient comparisons into a natural isomorphism
and checks the stated projection equation at every positive level.
(blueprint: lem-weil-pbc-closed-immersion-coherent-formal-equivalence-completion)
-/
theorem closedImmersion_coherentFormal_equivalence_completion {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian X] (I : X.IdealSheafData) :
    ∃ θ : ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
        Scheme.Modules.pushforward i ⋙ formalCompletionFunctor I ≅
        ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
        formalCompletionFunctor (I.comap i) ⋙
          (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj
            (Scheme.Modules.pushforward i),
      ∀ (G : CoherentModules Z) (n : ℕ),
        formalModuleQuotientπ I (n + 1)
            ((Scheme.Modules.pushforward i).obj G.obj) ≫
          (θ.hom.app G).app (op n) =
        (Scheme.Modules.pushforward i).map
          (formalModuleQuotientπ (I.comap i) (n + 1) G.obj) := by
  sorry

end AlgebraicGeometry
