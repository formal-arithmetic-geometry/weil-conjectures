/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCupProduct
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing

/-!
# Coherence of the mixed-support cup product

Let `a : X ⟶ Y` be a morphism admitting a compactification. The *mixed-support cup product*
(`AlgebraicGeometry.Etale.mixedSupportCupProduct`, blueprint `sk-def-pairing-data`)
```
⌣_c : Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ L)
```
is the projection map of `Ra_!` followed by the counit of `La^* ⊣ Ra_*`. We prove its coherence
(blueprint `prop-pod-cup-product-coherence`): it is natural in `K` and `L`, associative with
respect to the cup product `∪ : Ra_* L ⊗ᴸ Ra_* M ⟶ Ra_*(L ⊗ᴸ M)`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarCupProduct`), unital for the unit section
`1 : Λ_Y ⟶ Ra_* Λ_X` (`AlgebraicGeometry.Etale.rightDerivedLowerStarUnit`), and compatible with
`∪` through the forget-supports map `Ra_! ⟶ Ra_*`, in particular through `Ra_! ≅ Ra_*` for proper
`a`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerStarCupProduct`: the cup product
  `Ra_* L ⊗ᴸ Ra_* M ⟶ Ra_*(L ⊗ᴸ M)`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarUnit`: the unit section `1 : Λ_Y ⟶ Ra_* Λ_X`.

## Main statements

- `AlgebraicGeometry.Etale.mixedSupportCupProduct_naturality`: naturality in `K` and `L`.
- `AlgebraicGeometry.Etale.mixedSupportCupProduct_associativity`: associativity.
- `AlgebraicGeometry.Etale.mixedSupportCupProduct_rightUnitality`: the unit acts as the identity.
- `AlgebraicGeometry.Etale.mixedSupportCupProduct_comp_lowerShriekIsoLowerStar`:
  for proper `a`, the mixed-support cup product is the cup product `∪` read through
  `Ra_! ≅ Ra_*`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarCupProduct_associativity`: associativity of `∪`.

## Implementation notes

All statements are deduced from the abstract coherence results of
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCupProduct`. The kernel is sensitive to
how the objects of the derived categories are written: the proofs only rewrite with lemmas whose
two sides agree syntactically up to unfolding of `AlgebraicGeometry.Etale.derivedTensor`, and they
never introduce `let`-bound names for the chosen compactification, whose unfolding makes the kernel
time out.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

namespace Etale

section CupProduct

variable {X Y : Scheme.{u}} (a : X ⟶ Y)

end CupProduct

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{u + 1} A FA]
  [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

section Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/- The projection map of `Rf_!(c) = Rg_* ∘ i_!`, in the form of
`CategoryTheory.Adjunction.compProjectionMap`. -/
set_option quotPrecheck false in
local notation "𝚷" =>
  (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap
    (leftDerivedUpperStarTensorComparison A c.g) D((c.i)_!open[A])
    (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app N)
    (fun L ↦ (leftDerivedUpperStarCompactificationIso A c).hom.app L)

/-- Right unitality of the projection map of `Rf_!(c)`. -/
lemma compactificationProjectionMap_rightUnitality (K : 𝐃(X, A)) :
    𝚷 K (𝟙_ _) ≫ (D((c.i)_!open[A]) ⋙ R((c.g)_*[A])).map
        (K ◁ (leftDerivedUpperStarUnitIso A f).hom ≫ (ρ_ K).hom) =
      (ρ_ _).hom :=
  (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap_rightUnitality _
    (leftDerivedUpperStarUnitIso A c.g).hom (leftDerivedUpperStarUnitIso A c.i).hom
    (leftDerivedUpperStarUnitIso A f).hom
    (leftDerivedUpperStarTensorComparison_rightUnitor_hom A c.g)
    (fun K _ _ y ↦ derivedOpenImmersionLowerShriekProjectionIso_inv_naturality_right A c.i K y)
    (derivedOpenImmersionLowerShriekProjectionIso_inv_rightUnitality A c.i)
    (leftDerivedUpperStarCompactificationIso_hom_app_unit A c) K

end Compactification

section Composition

omit [Etale.UpperStarPreservesFlat A] [ConcreteCategory A FA]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] in
/-- The composition isomorphism `Rg₁_* ⋙ Rg₂_* ≅ R(g₁ ≫ g₂)_*`, transported along
`g₁₂ = g₁ ≫ g₂`, is the conjugate of `AlgebraicGeometry.Etale.leftDerivedUpperStarComp` under the
adjunctions `Lg^* ⊣ Rg_*`. -/
lemma rightDerivedLowerStarComp_hom_comp_congr_hom {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂) :
    (rightDerivedLowerStarComp A g₁ g₂).hom ≫ (rightDerivedLowerStarCongr A hg.symm).hom =
      rightDerivedLowerStarCompHom A g₁ g₂ g₁₂ hg := by
  subst hg
  rw [rightDerivedLowerStarCongr_refl, Iso.refl_hom, Category.comp_id,
    rightDerivedLowerStarCompHom, conjugateEquiv_leftDerivedUpperStarComp_hom]
  rfl

end Composition

section MixedSupport

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a]

omit [Etale.UpperStarPreservesFlat A]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] in
/-- The forget-supports map `Ra_! ⟶ Ra_*` of the chosen compactification `(i, g)`, written as
`Rg_*` of `i_! ⟶ Ri_*` followed by the composition isomorphism `Ri_* ⋙ Rg_* ⟶ Ra_*` conjugate to
`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`. -/
lemma rightDerivedLowerShriekToLowerStarComp_comp_eq :
    rightDerivedLowerShriekToLowerStarComp A a ≫ (rightDerivedLowerStarComp A _ _).hom ≫
        (rightDerivedLowerStarCongr A (HasCompactification.compactification a).comm.symm).hom =
      Functor.whiskerRight
          (derivedOpenImmersionLowerShriekToLowerStar A (HasCompactification.compactification a).i)
          (R(((HasCompactification.compactification a).g)_*[A])) ≫
        rightDerivedLowerStarCompHom A (HasCompactification.compactification a).i
          (HasCompactification.compactification a).g a
          (HasCompactification.compactification a).comm := by
  rw [rightDerivedLowerStarComp_hom_comp_congr_hom]
  rfl

end MixedSupport

end Etale

end AlgebraicGeometry
