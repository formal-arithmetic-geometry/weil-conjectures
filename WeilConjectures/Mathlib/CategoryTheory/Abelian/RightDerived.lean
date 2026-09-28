/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Acyclic resolutions compute right derived functors

Let `F : C ⥤ D` be a left exact additive functor between abelian categories, where `C` has
injective resolutions. An object `A` is `F`-acyclic if `R^q F A = 0` for all `q > 0`.

The key statement is that `F.mapHomologicalComplex` sends quasi-isomorphisms between
`ℕ`-indexed cochain complexes of `F`-acyclic objects to quasi-isomorphisms. As a consequence,
if `ι : X → I` is a resolution of `X` by `F`-acyclic objects and `φ : I ⟶ J` is a morphism over
`X` to an injective resolution `J`, then `F(φ)` is a quasi-isomorphism, and the natural map
`H^q(F I) → H^q(F J) ≅ R^q F X` is an isomorphism. This generalises
`InjectiveResolution.isoRightDerivedObj`.

## Main definitions

* `CategoryTheory.Functor.IsRightAcyclic`: `F`-acyclic objects.
* `CategoryTheory.Functor.rightDerivedObjIsoOfIsRightAcyclic`: the isomorphism
  `R^q F X ≅ H^q(F I)` induced by a morphism from an `F`-acyclic resolution `I` of `X` to an
  injective resolution of `X`.

## Main results

* `CategoryTheory.Functor.quasiIso_map_of_isRightAcyclic`: `F` preserves quasi-isomorphisms
  between `ℕ`-indexed cochain complexes of `F`-acyclic objects.
* `CategoryTheory.Functor.quasiIso_map_of_isRightAcyclic_of_injectiveResolution`: the
  acyclicity criterion.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* C. A. Weibel, *An Introduction to Homological Algebra*, Exercise 2.4.3
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

/-- An object `A` is `F`-acyclic if `R^q F A = 0` for all `q > 0`. -/
def Functor.IsRightAcyclic (F : C ⥤ D) [F.Additive] (A : C) : Prop :=
  ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)

lemma Functor.isRightAcyclic_of_injective (F : C ⥤ D) [F.Additive] (A : C) [Injective A] :
    F.IsRightAcyclic A :=
  fun q ↦ F.isZero_rightDerived_obj_injective_succ q A

/-- Blueprint `sk-thm-acyclicity` (Step 2 of the proof): a left exact additive functor
`F : C ⥤ D` sends a quasi-isomorphism `φ : K ⟶ L` between `ℕ`-indexed cochain complexes whose
terms are all `F`-acyclic to a quasi-isomorphism `F(φ) : F(K) ⟶ F(L)`.
```
    K⁰ ──d──▶ K¹ ──d──▶ K² ──▶ ⋯
    │φ⁰        │φ¹        │φ²
    ▼          ▼          ▼
    L⁰ ──d──▶ L¹ ──d──▶ L² ──▶ ⋯
```
Left exactness (`PreservesFiniteLimits F`) is needed in degree `0`. Equivalently, `F` sends
exact `ℕ`-indexed complexes of `F`-acyclic objects to exact complexes. -/
theorem Functor.quasiIso_map_of_isRightAcyclic (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {K L : CochainComplex C ℕ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ n, F.IsRightAcyclic (K.X n)) (hL : ∀ n, F.IsRightAcyclic (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  sorry

/-- Blueprint `sk-thm-acyclicity`: **acyclicity criterion.** Let `F : C ⥤ D` be a left exact
additive functor and let `ι : single₀ X ⟶ I` be a resolution of `X` (a quasi-isomorphism) by
`F`-acyclic objects. Let `J` be an injective resolution of `X` and `φ : I ⟶ J` a morphism with
`ι ≫ φ = J.ι`.
```
    X ──ι⁰──▶ I⁰ ──d──▶ I¹ ──d──▶ I² ──▶ ⋯
    ‖          │φ⁰        │φ¹        │φ²
    ‖          ▼          ▼          ▼
    X ──────▶ J⁰ ──d──▶ J¹ ──d──▶ J² ──▶ ⋯
```
Then `F(φ) : F(I) ⟶ F(J)` is a quasi-isomorphism, so that `H^q(F I) ≅ H^q(F J) ≅ R^q F X`,
see `Functor.rightDerivedObjIsoOfIsRightAcyclic`. -/
theorem Functor.quasiIso_map_of_isRightAcyclic_of_injectiveResolution (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {X : C} {I : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ n, F.IsRightAcyclic (I.X n)) (J : InjectiveResolution X) (φ : I ⟶ J.cocomplex)
    (hφ : ι ≫ φ = J.ι) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  have : QuasiIso (ι ≫ φ) := by rw [hφ]; infer_instance
  have : QuasiIso φ := quasiIso_of_comp_left ι φ
  exact F.quasiIso_map_of_isRightAcyclic φ hI fun n ↦ F.isRightAcyclic_of_injective _

/-- Blueprint `sk-thm-acyclicity`: the isomorphism `R^q F X ≅ H^q(F I)` for a resolution
`ι : single₀ X ⟶ I` of `X` by `F`-acyclic objects, induced by a morphism `φ : I ⟶ J` over `X`
to an injective resolution `J` of `X`:
```
    R^q F X ≅ H^q(F J⁰ → F J¹ → ⋯) ◀──H^q(F φ)── H^q(F I⁰ → F I¹ → ⋯)
```
-/
noncomputable def Functor.rightDerivedObjIsoOfIsRightAcyclic (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {X : C} {I : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ n, F.IsRightAcyclic (I.X n)) (J : InjectiveResolution X) (φ : I ⟶ J.cocomplex)
    (hφ : ι ≫ φ = J.ι) (q : ℕ) :
    (F.rightDerived q).obj X ≅ ((F.mapHomologicalComplex _).obj I).homology q :=
  have := F.quasiIso_map_of_isRightAcyclic_of_injectiveResolution ι hI J φ hφ
  J.isoRightDerivedObj F q ≪≫
    (asIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) q)).symm

@[simp]
lemma Functor.rightDerivedObjIsoOfIsRightAcyclic_inv (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {X : C} {I : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ n, F.IsRightAcyclic (I.X n)) (J : InjectiveResolution X) (φ : I ⟶ J.cocomplex)
    (hφ : ι ≫ φ = J.ι) (q : ℕ) :
    (F.rightDerivedObjIsoOfIsRightAcyclic ι hI J φ hφ q).inv =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) q ≫
        (J.isoRightDerivedObj F q).inv :=
  rfl

end CategoryTheory
