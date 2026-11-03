/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierTraceModelProjector

/-! Pullback of the universal comparison model to the recorded condensed
Artin--Schreier sheaf.

Source: the condensed-coefficients paragraph of `def-fd-artin-schreier-sheaf`
and clause (2) of `lem-wft-as-comparison`.
(blueprint: lem-fd-as-lisse-condensed-model-bridge).

Proof: unfold the irreducible `condensedSheafOf`.  The projector equality from
`lem-fd-as-lisse-condensed-model-projector` identifies its image with
`condensedArtinSchreierSheaf`; apply the upper-star functor along the map defined
by `f`, and use its image-map coherence to obtain the displayed isomorphism.
The argument is independent of the character and also covers the empty base. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

/-- Pullback bridge from the comparison model to the recorded sheaf.
(blueprint: lem-fd-as-lisse-condensed-model-bridge). -/
theorem condensed_trace_model_bridge
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
    (χ : AddChar k (MonObj.Γ Λ)) (X : Scheme.{u})
    [X.Over (Spec (.of k))] (f : Γ(X, ⊤))
    (hprojector : condensedProjector Λ k
        (Over.mk (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)))
        (fun c ↦ Over.homMk (Etale.artinSchreierTranslation k c)
          (Etale.artinSchreierTranslation_comp_artinSchreierMap k c)) χ =
      ProEtale.condensedArtinSchreierProjector Λ k χ) :
    Nonempty (condensedSheafOf Λ k χ X f ≅
      ProEtale.condensedArtinSchreierSheafOf Λ k X χ f) := by
  unfold condensedSheafOf ProEtale.condensedArtinSchreierSheafOf
    ProEtale.condensedArtinSchreierSheaf
  exact ⟨(ProEtale.CondensedRing.upperStar Λ
    (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ : PUnit ↦ f)).mapIso
      (eqToIso (congrArg (fun P ↦ image P) hprojector))⟩

end AlgebraicGeometry.ArtinSchreierTrace
