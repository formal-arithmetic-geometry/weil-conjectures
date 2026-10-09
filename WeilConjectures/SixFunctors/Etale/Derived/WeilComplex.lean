/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability

/-!

# Strict Weil complexes

Let `A` be a monoidal Grothendieck abelian coefficient category and let `X` be a scheme
carrying an automorphism `g`. In the `ℓ`-adic formalism `X = X₀ ×_{k₀} k` is the base change
of a scheme over a finite field to an algebraic closure and `g = g_γ` is the
geometric-Frobenius automorphism of `X` attached to a choice of Frobenius `γ` of `k` over
`k₀`. The construction of `g_γ` from `X₀` and `k₀` belongs to a different blueprint block, so
here the automorphism is simply a parameter.

A *strict Weil complex* at `Λ` is then a pair `(K, φ)` with `K` in `Dctf(X, Λ)` and an
isomorphism `φ : Lg^* K ≅ K`; a morphism of strict Weil complexes is a morphism of the
underlying complexes commuting with the two `φ`s. These form the category
`D^b_{ctf,W}(X, Λ)`, equipped with a forgetful functor to `Dctf(X, Λ)`.

## Main definitions

- `AlgebraicGeometry.Etale.WeilComplex`: the objects of `D^b_{ctf,W}(X, Λ)`.
- `AlgebraicGeometry.Etale.WeilComplex.Hom` and the `Category` instance on
  `AlgebraicGeometry.Etale.WeilComplex`.
- `AlgebraicGeometry.Etale.WeilComplex.forget`: the forgetful functor to `Dctf(X, Λ)`.

## Implementation notes

`Lg^*` is taken as the restriction `DerivedCategoryFiniteTor.leftDerivedUpperStar` of the
derived pullback to the small category `Dctf(X, Λ)`, which is available by
`sk-thm-sf-ctf-stability` (i); see
`WeilConjectures.SixFunctors.Etale.Derived.Stability`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

variable [UpperStarPreservesFlat A] {X : Scheme.{u}} (g : X ≅ X)

/-- Blueprint `sk-def-sf-weil-complexes`: Strict Weil complexes.

A *strict Weil complex* at `Λ` on `X` is a pair `(K, φ)` consisting of an object `K` of
`Dctf(X, Λ)` — a bounded constructible complex of finite Tor amplitude — together with an
isomorphism `φ : Lg^* K ≅ K`, where `g` is the geometric-Frobenius automorphism of
`X = X₀ ×_{k₀} k`.

The automorphism `g` is a parameter here: its construction from a model `X₀` over a finite
field `k₀` and a Frobenius `γ` of `k` over `k₀` belongs to a different blueprint block.

Strict Weil complexes form a category `D^b_{ctf,W}(X, Λ)`, whose morphisms are the morphisms
of the underlying complexes commuting with the two `φ`s, with a forgetful functor
`AlgebraicGeometry.Etale.WeilComplex.forget` to `Dctf(X, Λ)`. -/
structure WeilComplex where
  /-- The underlying object of `Dctf(X, Λ)`. -/
  obj : DerivedCategoryFiniteTor A X
  /-- The Weil structure `φ : Lg^* K ≅ K`, a descent datum along the geometric Frobenius. -/
  frobenius : (DerivedCategoryFiniteTor.leftDerivedUpperStar A g.hom).obj obj ≅ obj

namespace WeilComplex

/-- Blueprint `sk-def-sf-weil-complexes`: Strict Weil complexes.

A morphism of strict Weil complexes `(K, φ_K) ⟶ (L, φ_L)` is a morphism `u : K ⟶ L` of the
underlying objects of `Dctf(X, Λ)` making the square

```
  Lg^* K --Lg^* u--> Lg^* L
     |                  |
    φ_K                φ_L
     v                  v
     K -------u------>  L
```

commute. -/
@[ext]
structure Hom (K L : WeilComplex A g) where
  /-- The underlying morphism of `Dctf(X, Λ)`. -/
  hom : K.obj ⟶ L.obj
  /-- Compatibility with the two Weil structures. -/
  comm : K.frobenius.hom ≫ hom =
    (DerivedCategoryFiniteTor.leftDerivedUpperStar A g.hom).map hom ≫ L.frobenius.hom

/-- Blueprint `sk-def-sf-weil-complexes`: Strict Weil complexes.

The category `D^b_{ctf,W}(X, Λ)` of strict Weil complexes: identities and composition are
computed on the underlying objects of `Dctf(X, Λ)`, and both are readily checked to be
compatible with the Weil structures. -/
noncomputable instance : Category (WeilComplex A g) where
  Hom K L := Hom A g K L
  id K := { hom := 𝟙 K.obj, comm := by simp }
  comp {K L M} f h :=
    { hom := f.hom ≫ h.hom
      comm := by
        rw [← Category.assoc, f.comm, Category.assoc, h.comm, ← Category.assoc,
          ← Functor.map_comp] }

@[simp]
lemma id_hom (K : WeilComplex A g) : (𝟙 K : K ⟶ K).hom = 𝟙 K.obj := rfl

@[simp]
lemma comp_hom {K L M : WeilComplex A g} (f : K ⟶ L) (h : L ⟶ M) :
    (f ≫ h).hom = f.hom ≫ h.hom := rfl

/-- Blueprint `sk-def-sf-weil-complexes`: Strict Weil complexes.

The forgetful functor `D^b_{ctf,W}(X, Λ) ⥤ Dctf(X, Λ)` sending a strict Weil complex
`(K, φ)` to the underlying object `K` and forgetting the Weil structure. -/
noncomputable def forget : WeilComplex A g ⥤ DerivedCategoryFiniteTor A X where
  obj K := K.obj
  map f := f.hom

end WeilComplex

end Etale

end AlgebraicGeometry
