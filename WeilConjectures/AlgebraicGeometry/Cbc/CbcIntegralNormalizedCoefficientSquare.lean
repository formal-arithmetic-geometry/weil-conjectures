/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedCoefficientFamilies
import WeilConjectures.AlgebraicGeometry.Cbc.CbcProperCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
/-! Private helper lemmas on components of natural transformations and identity squares. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard pbcIntegralDatum
  AdicCoefficientDatum.completedPull cbcDerivedOpenShriek

private theorem app_heq
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (t : F ⟶ G) {x y : A} (h : x = y) : HEq (t.app x) (t.app y) := by
  cases h
  rfl

private theorem identity_square
    {A B : Type*} [Category A] [Category B] {U V : A ⥤ B}
    (S : A ⥤ A) (T : B ⥤ B) (bU : U ⋙ T ≅ S ⋙ U) (bV : V ⋙ T ≅ S ⋙ V)
    (hS : S = 𝟭 A) (hT : T = 𝟭 B)
    (hU : ∀ x, HEq (bU.hom.app x) (𝟙 (U.obj x)))
    (hV : ∀ x, HEq (bV.hom.app x) (𝟙 (V.obj x))) (t : U ⟶ V) (x : A) :
    T.map (t.app x) ≫ bV.hom.app x = bU.hom.app x ≫ t.app (S.obj x) := by
  subst S
  subst T
  rw [eq_of_heq (hU x), eq_of_heq (hV x)]
  change t.app x ≫ 𝟙 _ = 𝟙 _ ≫ t.app x
  rw [Category.comp_id, Category.id_comp]

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

variable {X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [IsNoetherian X'] [IsNoetherian Y']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ x : X', IsUnit (l : X'.presheaf.stalk x))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]

end AlgebraicGeometry.Scheme
