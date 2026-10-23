/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveBundleFormula

/-!
# The projective bundle formula for projective bundles

A projective bundle `p : P ⟶ B` (`AlgebraicGeometry.Etale.ProjectiveBundle`) is Zariski-locally on
`B` a projective space. The map `(1, h, …, hʳ) : ⊕ₐ Λ_B(-a)[-2a] ⟶ Rp_* Λ_P` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_projectiveFormulaMap_of_projectiveBundle`): this is checked on the
trivialising opens, where the formation of `Rp_*` commutes with restriction and the map is that of
projective space (`AlgebraicGeometry.Etale.isIso_projectiveFormulaMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open ProjectiveSpace

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (n : Type u)
  (S : Scheme.{u}) [HasInvertibleExponent Λ S]

variable {Λ n S}

variable [HasKummerClass.IsNormalized Λ] {k : Type u} [Field k] (aS : S ⟶ Spec (.of k))
  [IsSeparated aS] [LocallyOfFiniteType aS]

attribute [local instance] HasInvertibleExponent.opens

/-- The restriction of a class `h ∈ H^{2m}(Y, Λ(m))` along `g : X ⟶ Y`. -/
noncomputable def restrictClass {X Y : Scheme.{u}} [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] (g : X ⟶ Y) {m : ℤ}
    (h : constantComplex Λ Y ⟶ (tateObject Λ Y m)⟦2 * m⟧) :
    constantComplex Λ X ⟶ (tateObject Λ X m)⟦2 * m⟧ :=
  (leftDerivedUpperStarConstantComplexIso Λ g).inv ≫ (L((g)^*[ModuleCat.{u + 1} Λ])).map h ≫
    (leftDerivedUpperStarTateShiftIso Λ g m).hom

/-- A *projective bundle* of relative dimension given by `n`: a morphism `p : P ⟶ B` together
with an open cover `(U i)` of `B` and isomorphisms `p⁻¹(U i) ≅ ℙ(Option n; U i)` over `U i`. The
projectivization `ℙ_B(F)` of a vector bundle `F` of rank `#n + 1` is one. -/
structure ProjectiveBundle {P B : Scheme.{u}} (n : Type u) (p : P ⟶ B) where
  /-- The index type of the trivialising cover. -/
  ι : Type u
  /-- The trivialising opens of the base. -/
  U : ι → B.Opens
  iSup_U : iSup U = ⊤
  /-- The trivialisations. -/
  chart (i : ι) : (p ⁻¹ᵁ U i).toScheme ≅ ℙ(Option n; U i)
  chart_over (i : ι) : (chart i).hom ≫ ℙ(Option n; U i) ↘ U i = p ∣_ U i

include aS in
/-- Blueprint `thm-pur-projective-bundle-formula`: Projective-bundle formula without purity

Let `p : P ⟶ B` be a projective bundle of relative dimension `r = #n`
(`AlgebraicGeometry.Etale.ProjectiveBundle`), for instance the projectivization `ℙ_B(F)` of a
vector bundle `F` of rank `r + 1`, over a separated scheme of finite type over a field on which the
exponent of `Λ` is invertible, and let `h ∈ H²(P, Λ(1))` be a class restricting on every chart
`p⁻¹(U i) ≅ ℙʳ_{U i}` to the first Chern class of `𝒪(1)`, the hyperplane class (for `ℙ_B(F)`,
`h = c₁(𝒪(1))`). Then

`(1, h, …, hʳ) : ⊕_{a ≤ r} Λ_B(-a)[-2a] ⟶ Rp_* Λ_P`

is an isomorphism.

Not proved here: on the charts this is
`AlgebraicGeometry.Etale.isIso_projectiveFormulaMap`, and the formation of `Rp_*` commutes with
restriction to the opens of the base. -/
theorem isIso_projectiveFormulaMap_of_projectiveBundle [Fintype n] {P B : Scheme.{u}}
    [HasInvertibleExponent Λ P] [HasInvertibleExponent Λ B] (aB : B ⟶ Spec (.of k))
    [IsSeparated aB] [LocallyOfFiniteType aB] {p : P ⟶ B} (E : ProjectiveBundle n p)
    (h : constantComplex Λ P ⟶ (tateObject Λ P 1)⟦2 * (1 : ℤ)⟧)
    (hh : ∀ i, ∃ γ, IsHyperplaneClass Λ n (E.U i) γ ∧
      restrictClass ((E.chart i).inv ≫ (p ⁻¹ᵁ E.U i).ι) h = hyperplaneChernClass γ) :
    IsIso (projectiveFormulaMap p h (Fintype.card n)) := by
  sorry

end Etale

end AlgebraicGeometry
