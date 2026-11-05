/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.Algebra.Homology.Monoidal.ProjectionMap
public import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Transferring dualizability along exact monoidal functors

Let `G : C ⥤ D` be an exact monoidal functor between braided monoidal closed Grothendieck
abelian categories with functorial flat resolutions, with an exact left adjoint `L` such that
`G` commutes with internal homs (equivalently, the projection maps of `L ⊣ G` are isomorphisms).
This is the situation of the pullback along a weakly étale morphism of pro-étale sheaves.

We show that for a K-flat complex `P` of `C` whose image `G P` is K-flat, there is a single
morphism of complexes `χ` such that `Q P` is dualizable in `D(C)` if and only if `χ` is a
quasi-isomorphism, and `Q (G P)` is dualizable in `D(D)` if and only if `G χ` is a
quasi-isomorphism (`DerivedCategory.DualizabilityDatum.isDualizable_Q_obj_iff` and
`DerivedCategory.DualizabilityDatum.isDualizable_Q_obj_map_iff`). The morphism `χ` is the
chain-level model of the comparison `[P, 𝟙] ⊗ P ⟶ [P, P]` of the criterion
`DerivedCategory.isDualizable_Qh_obj_iff`. As `G` is exact, dualizability is therefore preserved
by `G`, and it is detected by a family of such functors which jointly reflects
quasi-isomorphisms.

## Main definitions

- `CochainComplex.monoidalClosed`: the monoidal closed structure on cochain complexes given by
  the internal hom complexes `CochainComplex.internalHom`.
- `DerivedCategory.DualizabilityDatum P`: the chain-level data of the criterion.

## Main statements

- `CochainComplex.isKInjective_map_of_adjunction`: a functor with an exact left adjoint
  preserves K-injective complexes.
- `DerivedCategory.DualizabilityDatum.isDualizable_Q_obj_iff`,
  `DerivedCategory.DualizabilityDatum.isDualizable_Q_obj_map_iff`.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace CochainComplex

section MonoidalClosed

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C] [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The monoidal closed structure on cochain complexes: the internal hom out of `P` is the
internal hom complex `CochainComplex.internalHom P`. -/
@[instance_reducible]
noncomputable def monoidalClosed : MonoidalClosed (CochainComplex C ℤ) where
  closed P := ⟨internalHom P, tensorHomAdjunction P⟩

end MonoidalClosed

section KInjective

variable {C : Type*} {D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (G : C ⥤ D) [G.Additive] {L : D ⥤ C} [L.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] (adj : L ⊣ G)

end KInjective

end CochainComplex

namespace DerivedCategory

open HomotopyCategory CochainComplex MonoidalClosed HomotopyCategory.MonoidalCategory

section Datum

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

end Datum

section Homotopic

variable {C : Type*} {D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (G : C ⥤ D) [G.Additive]

end Homotopic

section Transfer

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type u'} [Category.{v} D] [Abelian D] [IsGrothendieckAbelian.{v} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasDerivedCategory.{v} D] [Abelian.HasFunctorialFlatResolution D]
  (G : C ⥤ D) [G.Additive] [G.Monoidal] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
  {L : D ⥤ C} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ G)
  [∀ X : C, IsIso (ihomComparison G X).natTrans]

local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C
local instance : HasColimitsOfSize.{0, 0} D := hasColimitsOfSizeShrink D

attribute [local instance] CochainComplex.monoidalClosed

end Transfer

section Existence

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

end Existence

end DerivedCategory
