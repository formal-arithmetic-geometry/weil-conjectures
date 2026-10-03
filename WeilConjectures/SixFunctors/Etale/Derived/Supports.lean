/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Classes with supports: products and restriction

Let `i : Z ⟶ U` be a closed immersion. A *class with supports in `Z`*, with source `K` and
coefficients `L`, is a morphism `K ⟶ Ri_! Ri^! L` in `D(U_ét)`. The supported term is `Ri_!`, as
in the supported localization triangle `AlgebraicGeometry.Etale.supportedLocalizationTriangle`;
for a closed immersion it is `Ri_*`. For `K = Λ_U` and `L = M[n]` these are the classes of
`H^n_Z(U, M)`.

This file provides the two operations on classes with supports used to glue local cohomology
classes:

* the *cup product with supports*
  `H^a_{Z₁}(U, M) × H^b_{Z₂}(U, N) ⟶ H^{a+b}_{Z₁ ∩ Z₂}(U, M ⊗ N)`;
* the *restriction of supports* along a morphism `e : U ⟶ X`, from classes supported on
  `Z ⊆ X` to classes supported on the preimage `Z' = Z ×_X U`.

Both are lifts through the counit `Ri_! Ri^! L ⟶ L` of a morphism whose source is supported on
`Z`. Such a lift exists by the supported localization triangle, and it is unique because there
are no morphisms from an object supported on `Z` to one pushed forward from the open complement
(`AlgebraicGeometry.Etale.subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`).

## Implementation notes

The two lifts, and the lift of a morphism along a surjective closed immersion, are *defined* as
`Classical.choose` of uniqueness statements whose proofs are not yet formalised; uniqueness is
what makes the choices canonical.

The cup product is stated for classes whose degree shift is carried by the coefficients,
`K ⟶ Ri_! Ri^! (M[a])`; a class `K ⟶ (Ri_! Ri^! M)[a]` of degree `a` is brought into this form
through the shift compatibility of `Ri_!` and `Ri^!`
(`AlgebraicGeometry.Etale.shiftSupportedClass`).

## Main definitions

- `AlgebraicGeometry.Etale.liftCounitOfRangeEqUniv`: supports on everything.
- `AlgebraicGeometry.Etale.supportedProduct`:
  `Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)` for `Z = Z₁ ∩ Z₂`.
- `AlgebraicGeometry.Etale.cupWithSupports`: the cup product of classes with supports.
- `AlgebraicGeometry.Etale.supportedRestriction`,
  `AlgebraicGeometry.Etale.restrictSupportedClass`: restriction of supports.

## Main statements

- `AlgebraicGeometry.Etale.existsUnique_comp_counit_of_range_eq_univ`
- `AlgebraicGeometry.Etale.existsUnique_supportedProduct`
- `AlgebraicGeometry.Etale.existsUnique_supportedRestriction`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section CupProduct

variable {U Z₁ Z₂ Z : Scheme.{u}}

/-- **Supports on everything.** For a surjective closed immersion `i : Z ⟶ U`, every morphism
`φ : K ⟶ L` factors uniquely through the counit `ε : Ri_! Ri^! L ⟶ L`:

```
           K
       ψ ╱   ╲ φ
        ▼     ▼
Ri_! Ri^! L ──ε──▶ L
```

This is the supported localization triangle
(`AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization`) for `i` and the open
immersion `j : ∅ ⟶ U` of the empty open complement: `Rj_*` of the empty scheme vanishes, so the
triangle makes `ε` an isomorphism. -/
theorem existsUnique_comp_counit_of_range_eq_univ (i : Z ⟶ U) [IsClosedImmersion i]
    (hi : Set.range i.base = Set.univ)
    {K L : DerivedCategory (Sheaf U.smallEtaleTopology A)} (φ : K ⟶ L) :
    ∃! ψ : K ⟶ (R(i)_![A]).obj ((R(i)^![A]).obj L),
      ψ ≫ (rightDerivedUpperShriekAdjunction A i).counit.app L = φ :=
  sorry

/-- The lift `K ⟶ Ri_! Ri^! L` of a morphism `φ : K ⟶ L` along a surjective closed immersion
`i`, through the counit of `Ri_! ⊣ Ri^!`.

It is *defined* as `Classical.choose` of
`AlgebraicGeometry.Etale.existsUnique_comp_counit_of_range_eq_univ`, whose proof is not yet
formalised; uniqueness is what makes the choice canonical. -/
noncomputable def liftCounitOfRangeEqUniv (i : Z ⟶ U) [IsClosedImmersion i]
    (hi : Set.range i.base = Set.univ)
    {K L : DerivedCategory (Sheaf U.smallEtaleTopology A)} (φ : K ⟶ L) :
    K ⟶ (R(i)_![A]).obj ((R(i)^![A]).obj L) :=
  (existsUnique_comp_counit_of_range_eq_univ A i hi φ).exists.choose

/-- **The product of supports.** Let `i₁ : Z₁ ⟶ U`, `i₂ : Z₂ ⟶ U` and `i : Z ⟶ U` be closed
immersions with `Z = Z₁ ∩ Z₂`. The tensor product `ε₁ ⊗ ε₂` of the two counits factors uniquely
through the counit `ε` of `Ri_! ⊣ Ri^!`:

```
Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ───ψ───▶ Ri_! Ri^! (M ⊗ N)
                 ╲                          │
           ε₁ ⊗ ε₂ ╲                        │ ε
                     ▼                      ▼
                             M ⊗ N
```

The source is supported on `Z₁ ∩ Z₂`, so its composite with the unit
`M ⊗ N ⟶ Rj_* Lj^* (M ⊗ N)` of the open complement `j` of `Z` vanishes and the supported
localization triangle provides the factorisation. It is unique because there are no morphisms
from an object supported on `Z` to `(Rj_* Lj^* (M ⊗ N))[-1]`
(`AlgebraicGeometry.Etale.subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`
after the projection formula). -/
theorem existsUnique_supportedProduct (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    ∃! ψ : ((derivedTensor A U).obj ((R(i₁)_![A]).obj ((R(i₁)^![A]).obj M))).obj
        ((R(i₂)_![A]).obj ((R(i₂)^![A]).obj N)) ⟶
          (R(i)_![A]).obj ((R(i)^![A]).obj (((derivedTensor A U).obj M).obj N)),
      ψ ≫ (rightDerivedUpperShriekAdjunction A i).counit.app (((derivedTensor A U).obj M).obj N) =
        ((derivedTensor A U).map ((rightDerivedUpperShriekAdjunction A i₁).counit.app M)).app _ ≫
          ((derivedTensor A U).obj M).map ((rightDerivedUpperShriekAdjunction A i₂).counit.app N) :=
  sorry

/-- The *product of supports* `Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)` for closed
immersions with `Z = Z₁ ∩ Z₂`: the unique factorisation of the tensor product of the counits
through the counit of `Ri_! ⊣ Ri^!`.

It is *defined* as `Classical.choose` of
`AlgebraicGeometry.Etale.existsUnique_supportedProduct`, whose proof is not yet formalised;
uniqueness is what makes the choice canonical. -/
noncomputable def supportedProduct (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    ((derivedTensor A U).obj ((R(i₁)_![A]).obj ((R(i₁)^![A]).obj M))).obj
        ((R(i₂)_![A]).obj ((R(i₂)^![A]).obj N)) ⟶
      (R(i)_![A]).obj ((R(i)^![A]).obj (((derivedTensor A U).obj M).obj N)) :=
  (existsUnique_supportedProduct A i₁ i₂ i h M N).exists.choose

/-- The *cup product with supports* of classes `α : K ⟶ Ri₁_! Ri₁^! M` supported on `Z₁` and
`β : K ⟶ Ri₂_! Ri₂^! N` supported on `Z₂`, a class supported on `Z = Z₁ ∩ Z₂`:

`α ∪ β : K ⟶ K ⊗ K ⟶ Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)`,

where `Δ : K ⟶ K ⊗ K` is a diagonal and the last map is
`AlgebraicGeometry.Etale.supportedProduct`. For cohomology classes `K` is the unit and `Δ` the
inverse of the unitor. Degrees are carried by the coefficients: a class of degree `a` is a class
with coefficients `M[a]`. -/
noncomputable def cupWithSupports (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    {K M N : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (Δ : K ⟶ ((derivedTensor A U).obj K).obj K)
    (α : K ⟶ (R(i₁)_![A]).obj ((R(i₁)^![A]).obj M))
    (β : K ⟶ (R(i₂)_![A]).obj ((R(i₂)^![A]).obj N)) :
    K ⟶ (R(i)_![A]).obj ((R(i)^![A]).obj (((derivedTensor A U).obj M).obj N)) :=
  Δ ≫ ((derivedTensor A U).map α).app K ≫ ((derivedTensor A U).obj _).map β ≫
    supportedProduct A i₁ i₂ i h M N

/-- A class `K ⟶ (Ri_! Ri^! L)[n]` of degree `n` with supports, read as a class with
coefficients `L[n]`, `K ⟶ Ri_! Ri^! (L[n])`, through the shift compatibility of `Ri_!` and
`Ri^!`. -/
noncomputable def shiftSupportedClass (i : Z ⟶ U) [IsClosedImmersion i] (n : ℤ)
    {K L : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (α : K ⟶ ((R(i)_![A]).obj ((R(i)^![A]).obj L))⟦n⟧) :
    K ⟶ (R(i)_![A]).obj ((R(i)^![A]).obj (L⟦n⟧)) :=
  α ≫ ((R(i)_![A]).commShiftIso n).inv.app _ ≫
    (R(i)_![A]).map (((R(i)^![A]).commShiftIso n).inv.app L)

end CupProduct

section Restriction

variable {U X Z Z' : Scheme.{u}}

/-- **Restriction of supports.** Let `e : U ⟶ X` be a morphism, `i : Z ⟶ X` a closed immersion
and `i' : Z' ⟶ U` its base change along `e`. For `L ∈ D(X_ét)`, `L' ∈ D(U_ét)` and
`τ : Le^* L ≅ L'`, the composite `Le^* ε ≫ τ` factors uniquely through the counit `ε'` of
`Ri'_! ⊣ Ri'^!`:

```
Le^* (Ri_! Ri^! L) ───ψ───▶ Ri'_! Ri'^! L'
         │                        │
  Le^* ε │                        │ ε'
         ▼                        ▼
      Le^* L ─────────τ─────────▶ L'
```

By base change for the closed immersion `i` (proper base change, `Ri_! = Ri_*`),
`Le^* Ri_! Ri^! L` is supported on `Z'`, and there are no morphisms from an object supported on
`Z'` to one pushed forward from its open complement. -/
theorem existsUnique_supportedRestriction (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology A)) (τ : (L((e)^*[A])).obj L ≅ L') :
    ∃! ψ : (L((e)^*[A])).obj ((R(i)_![A]).obj ((R(i)^![A]).obj L)) ⟶
        (R(i')_![A]).obj ((R(i')^![A]).obj L'),
      ψ ≫ (rightDerivedUpperShriekAdjunction A i').counit.app L' =
        (L((e)^*[A])).map ((rightDerivedUpperShriekAdjunction A i).counit.app L) ≫ τ.hom :=
  sorry

/-- The *restriction of supports* `Le^* (Ri_! Ri^! L) ⟶ Ri'_! Ri'^! L'` along `e : U ⟶ X`, for
the base change `i'` of a closed immersion `i` and an identification `τ : Le^* L ≅ L'`: the unique
factorisation of `Le^* (Ri_! Ri^! L) ⟶ Le^* L ≅ L'` through the counit of `Ri'_! ⊣ Ri'^!`.

It is *defined* as `Classical.choose` of
`AlgebraicGeometry.Etale.existsUnique_supportedRestriction`, whose proof is not yet
formalised; uniqueness is what makes the choice canonical. -/
noncomputable def supportedRestriction (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology A)) (τ : (L((e)^*[A])).obj L ≅ L') :
    (L((e)^*[A])).obj ((R(i)_![A]).obj ((R(i)^![A]).obj L)) ⟶
      (R(i')_![A]).obj ((R(i')^![A]).obj L') :=
  (existsUnique_supportedRestriction A e i i' g hg L L' τ).exists.choose

/-- The restriction of a class `γ : K ⟶ Ri_! Ri^! L` with supports along `e : U ⟶ X`, for a
comparison `σ : K' ⟶ Le^* K` of sources:
`K' ⟶ Le^* K ⟶ Le^* (Ri_! Ri^! L) ⟶ Ri'_! Ri'^! L'`, the last map being
`AlgebraicGeometry.Etale.supportedRestriction`. For cohomology classes `σ` is the
identification `Λ_U ≅ Le^* Λ_X` of the constant complexes. -/
noncomputable def restrictSupportedClass (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {K' L' : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (σ : K' ⟶ (L((e)^*[A])).obj K) (τ : (L((e)^*[A])).obj L ≅ L')
    (γ : K ⟶ (R(i)_![A]).obj ((R(i)^![A]).obj L)) :
    K' ⟶ (R(i')_![A]).obj ((R(i')^![A]).obj L') :=
  σ ≫ (L((e)^*[A])).map γ ≫ supportedRestriction A e i i' g hg L L' τ

end Restriction

end Etale

end AlgebraicGeometry
