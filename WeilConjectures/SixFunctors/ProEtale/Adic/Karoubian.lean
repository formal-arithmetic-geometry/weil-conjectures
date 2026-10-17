/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ObjectProperty.RetractOfKernels
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Karoubian
public import WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.SixFunctors.ProEtale.Adic.Abelian

/-!
# Idempotent completeness of `Dᵇc(X, ℚ̄_ℓ)`

The common-stage coefficient category `Dᵇc(X, ℚ̄_ℓ)` of blueprint
`def-weil-algebraically-closed-coefficients` is realised in the Bhatt–Scholze model as the
bounded complexes of sheaves of `ℚ̄_ℓ,X`-modules on the pro-étale site with constructible
cohomology sheaves (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic`). This
file shows that it is idempotent complete (blueprint `lem-weil-qbar-idempotent-complete`).

An idempotent `p` of a bounded object `K` of the derived category splits there: an object with
cohomology in an interval `[a, a + n]` carries the bounded truncations of the canonical
t-structure, and the induction of
`CategoryTheory.Triangulated.TStructure.isSplit_of_isGE_of_isLE` (blueprint
`thm-weil-karoubian-bounded-t`) splits `p`. The image of `p` is a retract of `K`, so it is
bounded and its cohomology sheaves are retracts of those of `K`. On a locally Noetherian scheme,
constructible `ℓ`-adic sheaves are closed under kernels
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.kernel_cokernel`), hence under retracts.

The blueprint deduces the lemma from the idempotent completeness of the finite stages
`Dᵇc(X, E)` by filtered retract descent; in the Bhatt–Scholze model the common-stage category is
directly a full subcategory of a derived category with a t-structure, and the argument above
applies to it directly.

## Main statements

- `AlgebraicGeometry.ProEtale.DerivedCategory.isIdempotentComplete_boundedConstructibleAdic`
- `AlgebraicGeometry.ProEtale.DerivedCategory.isEquivalence_toKaroubi_boundedConstructibleAdic`
-/

@[expose] public section

universe u

open CategoryTheory Limits Idempotents

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- On a locally Noetherian scheme, a retract of a constructible `ℓ`-adic sheaf is
constructible: constructible sheaves are closed under kernels. -/
instance [IsLocallyNoetherian X] : (adicConstructibleSheaf l X).IsStableUnderRetracts :=
  ObjectProperty.isStableUnderRetracts_of_kernels _

namespace DerivedCategory

variable (l X)

/-- On a locally Noetherian scheme, `Dᵇc(X, ℚ̄_ℓ)` is stable under retracts in the derived
category: a retract of a bounded object is bounded, and its cohomology sheaves are retracts of
constructible sheaves. -/
instance [IsLocallyNoetherian X] : (boundedConstructibleAdic l X).IsStableUnderRetracts where
  of_retract {M N} e := by
    rintro ⟨hb, hc⟩
    obtain ⟨a, b, hab⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded N).2 hb
    exact ⟨(_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded M).1
      ⟨a, b, (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_retract e hab⟩,
      fun n ↦ (adicConstructibleSheaf l X).prop_of_retract
        (e.map (_root_.DerivedCategory.homologyFunctor _ n)) (hc n)⟩

/-- Blueprint `lem-weil-qbar-idempotent-complete`: Idempotent completeness of the common-stage
category.

For a locally Noetherian scheme `X`, the category `Dᵇc(X, ℚ̄_ℓ)` is idempotent complete. Every
idempotent of a bounded object of the derived category of `ℚ̄_ℓ,X`-modules splits
(`CategoryTheory.Triangulated.TStructure.isSplit_of_isGE_of_isLE`), and the image is again in
`Dᵇc(X, ℚ̄_ℓ)`, being a retract. -/
theorem isIdempotentComplete_boundedConstructibleAdic [IsLocallyNoetherian X] :
    IsIdempotentComplete (boundedConstructibleAdic l X).FullSubcategory := by
  rw [isIdempotentComplete_iff_isSplit]
  intro K p hp
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.2.1
  have : _root_.DerivedCategory.TStructure.t.IsLE K.obj (a + ((b - a).toNat : ℕ)) :=
    _root_.DerivedCategory.TStructure.t.isLE_of_le K.obj b _ (by lia)
  obtain ⟨Y, i, e, h₁, h₂⟩ := _root_.DerivedCategory.TStructure.t.isSplit_of_isGE_of_isLE
    (b - a).toNat K.obj a p.hom ((boundedConstructibleAdic l X).ι.congr_map hp)
  have hY : boundedConstructibleAdic l X Y :=
    (boundedConstructibleAdic l X).prop_of_retract ⟨i, e, h₁⟩ K.2
  exact ⟨⟨Y, hY⟩, ObjectProperty.homMk i, ObjectProperty.homMk e, by ext; exact h₁,
    by ext; exact h₂⟩

/-- Blueprint `lem-weil-qbar-idempotent-complete`: for a locally Noetherian scheme `X`, the
canonical functor from `Dᵇc(X, ℚ̄_ℓ)` into its Karoubi envelope is an equivalence. -/
theorem isEquivalence_toKaroubi_boundedConstructibleAdic [IsLocallyNoetherian X] :
    (toKaroubi (boundedConstructibleAdic l X).FullSubcategory).IsEquivalence :=
  have := isIdempotentComplete_boundedConstructibleAdic l X
  inferInstance

end DerivedCategory

end AlgebraicGeometry.ProEtale
