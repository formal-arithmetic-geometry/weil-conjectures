/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTorsorReflection
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTorsorLifting
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality

/-!
# Finite étale equivalence and first cohomology

## References

* Stacks Project, Tags 0A5G, 03AJ and 03RV
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Pullback equivalence on finite étale schemes implies comparison for finite constant H¹
(Stacks, Tag 0A5G; Tags 03AJ and 03RV). Only the categorical implication is stated: there is
no henselian ring, proper morphism, closed fibre, or assumption on the image of `i`. -/
theorem bijective_cohomologyMap_one_of_finiteEtale_equivalence
    [(@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange]
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (hFE : (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M] :
    Function.Bijective (cohomologyMap i
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)) 1) := by
  classical
  let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of M)
  let G₀ := (upperStar AddCommGrpCat.{u + 1} i).obj G
  have hnat := Sheaf.Torsor.etale_torsor_h1_functoriality.1 Y Y₀ i G
  choose τ e hact hclass using hnat
  let c := Sheaf.Torsor.classH1 G terminalIsTerminal
  let c₀ := Sheaf.Torsor.classH1 G₀ terminalIsTerminal
  constructor
  · intro x y hxy
    obtain ⟨q, rfl⟩ := c.surjective x
    obtain ⟨r, rfl⟩ := c.surjective y
    induction q using Quotient.inductionOn with | h T₁ => ?_
    induction r using Quotient.inductionOn with | h T₂ => ?_
    have heq : c₀ ⟦τ T₁⟧ = c₀ ⟦τ T₂⟧ := by
      exact (hclass T₁).symm.trans (hxy.trans (hclass T₂))
    have hiso : τ T₁ ≈ τ T₂ := Quotient.exact (c₀.injective heq)
    exact congrArg c (Quotient.sound
      (finiteEtale_reflects_torsor_transport i hFE M τ (fun T ↦ ⟨e T, hact T⟩) T₁ T₂ hiso))
  · intro y
    obtain ⟨q, rfl⟩ := c₀.surjective y
    induction q using Quotient.inductionOn with | h R => ?_
    obtain ⟨T, hT⟩ := finiteEtale_lifts_torsor_transport i hFE M τ (fun T ↦ ⟨e T, hact T⟩) R
    refine ⟨c ⟦T⟧, ?_⟩
    exact (hclass T).trans (congrArg c₀ (Quotient.sound hT))

end AlgebraicGeometry.Etale
