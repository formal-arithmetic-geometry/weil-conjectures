# AlgebraicGeometry.Proj.scalarExtensionTwistSection and IsScalarExtensionTwistComparison

## Reason

Move the two existing definitions verbatim to the new publicly imported module
`Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData`. This lets the three independent
proof obligations import their types without a cycle back to the main assembly.
The existing public imports remain on the item and are also the data module's imports.
No definition's signature, body, visibility or value changes. No target statement or
meaning changes. This is solely a declaration-owner relocation.

## Old

In `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistComparison`:

```lean
noncomputable def scalarExtensionTwistSection
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (j : ℤ) (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 j, U)) :
    Γ(twist ℬ j, r ⁻¹ᵁ U) :=
  (θ j).hom.app (r ⁻¹ᵁ U) (tensorPullbackSection r (twist 𝒜 j) U s)

/-- The normalized fraction rule for the scalar-extension comparison. A section `s=a/b`
is specified by `b*s=a` where `b` is invertible. For `b=f^m`, this is exactly
`(a/f^m) ⊗ c ↦ c*ψ(a)/ψ(f)^m`. All opens are allowed, so the rule includes further
standard-open restrictions. Source: Stacks 01MY
(blueprint: lem-sfb-proj-scalar-extension-twist-comparison). -/
def IsScalarExtensionTwistComparison
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j) : Prop :=
  ∀ (j : ℤ) (i k : ℕ) (a : A) (b : A), a ∈ 𝒜 i → b ∈ 𝒜 k →
    (i : ℤ) = (k : ℤ) + j →
    ∀ (U : (Proj 𝒜).Opens), U ≤ basicOpen 𝒜 b →
    ∀ (s : Γ(twist 𝒜 j, U)),
      (∀ y : U, (s.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk b 1 = Localization.mk a 1) →
    ∀ (c : Γ(Proj ℬ, r ⁻¹ᵁ U)) (x : r ⁻¹ᵁ U),
      ((c • scalarExtensionTwistSection r θ j U s).1 x :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * Localization.mk (ψ b) 1 =
        (c.1 x).val * Localization.mk (ψ a) 1
```

## New

In `Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData`, publicly re-exported from
the original module:

```lean
noncomputable def scalarExtensionTwistSection
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (j : ℤ) (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 j, U)) :
    Γ(twist ℬ j, r ⁻¹ᵁ U) :=
  (θ j).hom.app (r ⁻¹ᵁ U) (tensorPullbackSection r (twist 𝒜 j) U s)

/-- The normalized fraction rule for the scalar-extension comparison. A section `s=a/b`
is specified by `b*s=a` where `b` is invertible. For `b=f^m`, this is exactly
`(a/f^m) ⊗ c ↦ c*ψ(a)/ψ(f)^m`. All opens are allowed, so the rule includes further
standard-open restrictions. Source: Stacks 01MY
(blueprint: lem-sfb-proj-scalar-extension-twist-comparison). -/
def IsScalarExtensionTwistComparison
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j) : Prop :=
  ∀ (j : ℤ) (i k : ℕ) (a : A) (b : A), a ∈ 𝒜 i → b ∈ 𝒜 k →
    (i : ℤ) = (k : ℤ) + j →
    ∀ (U : (Proj 𝒜).Opens), U ≤ basicOpen 𝒜 b →
    ∀ (s : Γ(twist 𝒜 j, U)),
      (∀ y : U, (s.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk b 1 = Localization.mk a 1) →
    ∀ (c : Γ(Proj ℬ, r ⁻¹ᵁ U)) (x : r ⁻¹ᵁ U),
      ((c • scalarExtensionTwistSection r θ j U s).1 x :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * Localization.mk (ψ b) 1 =
        (c.1 x).val * Localization.mk (ψ a) 1
```

## Users

`tools/downstream.py` reports no downstream modules and only the item itself as a user
of either moved name; an exact import search likewise finds no direct importers.
The three newly added theorem modules import the data module. No existing consumer
requires adaptation, and neither the item nor any upstream module is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistComparison | Q4 | Same public names and values via public import; proved assembly replaces sorry. |
| Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistExistence | new Q4 | Uses the unchanged normalization predicate. |
| Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistFractionLaws | new Q4 | Uses the unchanged normalization predicate. |
| Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistCompositionLaw | new Q4 | Uses the unchanged normalization predicate and comparison maps. |

## Status

landed 20261027T180741-L-3897713 2026-10-27 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistComparison)
