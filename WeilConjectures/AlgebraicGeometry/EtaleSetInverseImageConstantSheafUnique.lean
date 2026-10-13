/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

/- helper uniqueness -/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageConstantSheafExists
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Canonical section equations determine the inverse-image morphism uniquely.
(blueprint: new-etaleSetInverseImageConstantSheaf-uniqueness) -/
theorem etaleSetInverseImageConstantSheaf_unique
    (U V : Scheme.{u}) (v : V ⟶ U) (E : Type u)
    (γ : etaleSetInverseImageConstantSheafHom U V v E)
    (hγ : etaleSetInverseImageConstantSheafCondition U V v E γ) :
    ∀ γ' : etaleSetInverseImageConstantSheafHom U V v E,
      etaleSetInverseImageConstantSheafCondition U V v E γ' → γ' = γ := by
  intro γ' hγ'
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) v) (Type (u + 1))
    (U.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale)
  apply (adj.homEquiv _ _).injective
  apply ((constantSheafAdj U.smallEtaleTopology (Type (u + 1))
    (MorphismProperty.Over.mkIdTerminal @Etale U)).homEquiv _ _).injective
  rw [constantSheafAdj_homEquiv_apply, constantSheafAdj_homEquiv_apply]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext e
  obtain ⟨e⟩ := e
  exact (hγ' e).trans (hγ e).symm
end AlgebraicGeometry
