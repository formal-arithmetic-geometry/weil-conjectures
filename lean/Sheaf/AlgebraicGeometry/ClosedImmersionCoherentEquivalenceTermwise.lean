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
/-- Termwise part of the closed immersion coherent formal equivalence.
Source: Stacks Project, Cohomology of Schemes, Tags 088A and 087T.
The proof constructs the restricted pushforward equivalence level by level, using
the annihilation, coherence, ideal-power, and full-faithfulness lemmas.
(blueprint: lem-weil-pbc-closed-immersion-coherent-formal-equivalence-termwise)
-/
theorem closedImmersion_coherentFormal_equivalence_termwise {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] (I : X.IdealSheafData) :
    ∃ E : @CoherentFormalModule Z (isNoetherian_of_locallyOfFiniteType i) (I.comap i) ≌
        ObjectProperty.FullSubcategory (fun M : CoherentFormalModule X I ↦
          SupportedOn I M i),
      Nonempty (E.functor ⋙
        ObjectProperty.ι (fun M : CoherentFormalModule X I ↦ SupportedOn I M i) ⋙
        ObjectProperty.ι (IsCoherentFormalModule I) ≅
        ObjectProperty.ι (IsCoherentFormalModule (I.comap i)) ⋙
          (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj
            (Scheme.Modules.pushforward i)) := by
  sorry

end AlgebraicGeometry
