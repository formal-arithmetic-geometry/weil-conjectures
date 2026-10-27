module

public import Sheaf.Paper.FiniteConstantRingedLocalModel
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Sectionwise finite constant local models

Source: blueprint, sk-def-sfb-constructible, clause 1; Stacks 03CY and 03EK
(blueprint: sk-def-sfb-constructible).

The existing ringed-site and internal condensed-module definitions remain available
through the public import. This companion interface expresses the scalar local-model
clause on the chosen small site in sectionwise module sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe r
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

variable {C : Type r} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type r) [CommRing A] (B : Sheaf J CommRingCat.{r})
  (σ : realizationRing J A ⟶ B)

/-- A specified scalar model on a covering object: finite presentation is over the scalar
ring before sheafification, and extension uses the actual coefficient morphism.
Source: blueprint sk-def-sfb-constructible, clause 1; Stacks 03CY, 03EK
(blueprint: sk-def-sfb-constructible). -/
def HasFiniteScalarConstantModelOn
    (L : SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J B))
    (U : C) (N : ModuleCat.{r} A) : Prop :=
  Module.FinitePresentation A N ∧ Nonempty (L.over U ≅
    (SheafOfModules.changeOfRings σ ((commutativeSiteConstantModuleFunctor J A).obj N)).over U)

/-- The scalar local-model condition, imposed on a covering sieve of every site object.
It allows empty covering sieves and zero scalar modules. Source: blueprint
sk-def-sfb-constructible, clause 1; Stacks 03CY, 03EK
(blueprint: sk-def-sfb-constructible). -/
def HasFiniteScalarConstantLocalModel
    (L : SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J B)) :
    Prop :=
  ∀ V : C, ∃ W : Sieve V, W ∈ J V ∧ ∀ (U : C) (f : U ⟶ V), W f →
    ∃ N : ModuleCat.{r} A, HasFiniteScalarConstantModelOn J A B σ L U N

end AlgebraicGeometry.ProEtale
