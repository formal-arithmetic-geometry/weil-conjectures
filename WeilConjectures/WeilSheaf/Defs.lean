/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructiblePullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!

# Weil sheaves and Weil complexes

Let `X` be a scheme with an automorphism `e : X ≅ X`. A *Weil sheaf* for `(X, e)` is a
sheaf `F` on the small étale site of `X` together with an isomorphism `Φ : e^* F ≅ F`,
and a *Weil complex* is an object `K` of the derived category of étale sheaves on `X`
together with an isomorphism `Φ : e^* K ≅ K`. The isomorphism `Φ` is structure data, not
the proposition that some isomorphism exists, and a morphism is a morphism of the
underlying sheaves or complexes commuting with the structure isomorphisms.

The intended application is the following. Let `X₀` be a scheme over a finite field `k`
with structure morphism `f : X₀ ⟶ Spec k`, let `X = f.geometricFiber` be its geometric
fiber and let `e = f.geometricGaloisFrobenius` be the geometric Galois Frobenius of `X`
(see `WeilConjectures.AlgebraicGeometry.GeometricFrobenius`). Classically the resulting
data are called Weil sheaves and Weil complexes *on `X₀`*: the underlying sheaf lives on
the geometric fiber `X`, while the Frobenius structure isomorphism is what remains of a
descent datum to `X₀`. Fixing an arbitrary `(X, e)` rather than the geometric fiber of a
fixed `f` is what the transport of Weil structures through the six operations needs: the
Frobenius square of a morphism `X₀ ⟶ Y₀` over `k` involves the automorphisms of all four
corners of a base change square, each with its own automorphism.

The definitions are all instances of one categorical construction: an algebra with
invertible structure morphism (`CategoryTheory.Endofunctor.IsoAlgebra`) for the pullback
endofunctor along `e`. No group-action formalism is required: the single generator `e^*`
together with the coherently iterated structure isomorphisms
`CategoryTheory.Endofunctor.IsoAlgebra.strIterate` is sufficient. Since the pullback
`e^*` on sheaves is exact, its action on the derived category is the localization of its
termwise action on complexes (`CategoryTheory.Functor.mapDerivedCategory`); no unbounded
left derived functor machinery is needed.

Four layers are provided, each with its forgetful functor to the underlying category and
with comparison functors between them:

- `AlgebraicGeometry.WeilSheaf`, for étale sheaves on `X`;
- `AlgebraicGeometry.WeilComplex`, for the derived category of étale sheaves on `X`;
- `AlgebraicGeometry.WeilComplexPlus`, for the bounded below derived category
  `D⁺(X_ét, A)`, using the restriction
  `CategoryTheory.Functor.mapDerivedCategoryPlus` of the derived pullback. This is the
  level at which the compact-support base change of this project, hence the transport of
  Weil structures through `Rf_!`, is available;
- `AlgebraicGeometry.WeilComplexBoundedConstructible`, for the bounded constructible
  derived category `Dᵇc(X, A)`, using the restriction
  `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible.upperStar` of the derived
  pullback of `WeilConjectures.CategoryTheory.DerivedCategory.ConstructiblePullback`.

Since `e^*` is t-exact, a Weil complex induces for every `n` a Weil sheaf structure
`e^* Hⁿ(K) ≅ Hⁿ(e^* K) ≅ Hⁿ(K)` on its `n`-th homology sheaf. This is packaged as the
functors `AlgebraicGeometry.WeilComplex.homologyFunctor` and
`AlgebraicGeometry.WeilComplexBoundedConstructible.homologyFunctor` into
`AlgebraicGeometry.WeilSheaf`, built from the general transport of algebras
`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso` along the homology commutation isomorphism
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` of the exact functor `e^*`.

The canonical Weil structure on objects descended from `X₀` and the transport of Weil
structures through `Rf_!` are subsequent layers built on top of these definitions.

## Implementation notes

The iterated structure isomorphism `IsoAlgebra.strIterate n` of a Weil complex is an
isomorphism `(e^*)ⁿ K ≅ K`, whereas the `m`-th Frobenius operator `φ_m` of the trace
formula is an isomorphism `(eⁿ)^* K ≅ K`. Identifying the two uses the composition
isomorphism `AlgebraicGeometry.Etale.upperStarComp`, iterated; this identification is
still owed.

## Main definitions

- `AlgebraicGeometry.WeilSheaf`: the category of Weil sheaves for a scheme with an
  automorphism, with its forgetful functor `WeilSheaf.forget` to étale sheaves.
- `AlgebraicGeometry.WeilComplex`: the category of Weil complexes, with its forgetful
  functor `WeilComplex.forget` to the derived category of étale sheaves and with the
  Weil sheaf structure `WeilComplex.homologyFunctor` on its homology sheaves.
- `AlgebraicGeometry.WeilComplexPlus`: the category of bounded below Weil complexes, with
  its forgetful functor `WeilComplexPlus.forget` to `D⁺(X_ét, A)` and its comparison
  functor `WeilComplexPlus.toWeilComplex`.
- `AlgebraicGeometry.WeilComplexBoundedConstructible`: the category of bounded
  constructible Weil complexes, with its forgetful functor
  `WeilComplexBoundedConstructible.forget` to `Dᵇc(X, A)`, its comparison functors
  `WeilComplexBoundedConstructible.toWeilComplexPlus` and
  `WeilComplexBoundedConstructible.toWeilComplex`, and the Weil sheaf structure
  `WeilComplexBoundedConstructible.homologyFunctor` on its homology sheaves.

-/

@[expose] public section

universe u u'

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]
variable {X : Scheme.{u}} (e : X ≅ X)

noncomputable section

section WeilSheaf

/-- A *Weil sheaf* for a scheme `X` with an automorphism `e : X ≅ X` is an étale sheaf `F`
on `X` together with an isomorphism `Φ : e^* F ≅ F`. The isomorphism `Φ` is structure
data, and morphisms are morphisms of sheaves commuting with the structure isomorphisms.

For `X` the geometric fiber of a scheme `X₀` over a finite field and `e` its geometric
Galois Frobenius, this is the classical notion of a Weil sheaf *on `X₀`*. -/
abbrev WeilSheaf : Type _ :=
  IsoAlgebra (Etale.upperStar A e.hom)

/-- The forgetful functor from Weil sheaves to étale sheaves, discarding the Frobenius
structure isomorphisms. -/
def WeilSheaf.forget : WeilSheaf A e ⥤ Sheaf X.smallEtaleTopology A :=
  IsoAlgebra.forget (Etale.upperStar A e.hom)

end WeilSheaf

section WeilComplex

/-- A *Weil complex* for a scheme `X` with an automorphism `e : X ≅ X` is an object `K` of
the derived category of étale sheaves on `X` together with an isomorphism
`Φ : e^* K ≅ K`, where `e^*` acts on the derived category through
`CategoryTheory.Functor.mapDerivedCategory`, the pullback on sheaves being exact. The
isomorphism `Φ` is structure data, and morphisms are morphisms of the derived category
commuting with the structure isomorphisms.

For `X` the geometric fiber of a scheme `X₀` over a finite field and `e` its geometric
Galois Frobenius, this is the classical notion of a Weil complex *on `X₀`*. -/
abbrev WeilComplex : Type _ :=
  IsoAlgebra (Etale.upperStar A e.hom).mapDerivedCategory

/-- The forgetful functor from Weil complexes to the derived category of étale sheaves,
discarding the Frobenius structure isomorphisms. -/
def WeilComplex.forget :
    WeilComplex A e ⥤ DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  IsoAlgebra.forget (Etale.upperStar A e.hom).mapDerivedCategory

/-- Since the pullback `e^*` is t-exact, the `n`-th homology sheaf of a Weil complex
carries the induced Weil sheaf structure `e^* Hⁿ(K) ≅ Hⁿ(e^* K) ≅ Hⁿ(K)`: the transport
of the structure isomorphism along the homology functor via the commutation isomorphism
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`. -/
def WeilComplex.homologyFunctor (n : ℤ) : WeilComplex A e ⥤ WeilSheaf A e :=
  IsoAlgebra.mapOfNatIso ((Etale.upperStar A e.hom).mapDerivedCategoryHomologyFunctorIso n)

end WeilComplex

section WeilComplexPlus

/-- A *bounded below Weil complex* for a scheme `X` with an automorphism `e : X ≅ X` is an
object `K` of `D⁺(X_ét, A)` together with an isomorphism `Φ : e^* K ≅ K`, where `e^*` acts
on `D⁺(X_ét, A)` through `CategoryTheory.Functor.mapDerivedCategoryPlus`, the restriction
of the derived pullback along the inclusion `DerivedCategory.Plus.ι`. The isomorphism `Φ`
is structure data.

This is the level at which the compact-support base change of this project, hence the
transport of Weil structures through `Rf_!`, is available. -/
abbrev WeilComplexPlus : Type _ :=
  IsoAlgebra (Etale.upperStar A e.hom).mapDerivedCategoryPlus

/-- The forgetful functor from bounded below Weil complexes to `D⁺(X_ét, A)`, discarding
the Frobenius structure isomorphisms. -/
def WeilComplexPlus.forget :
    WeilComplexPlus A e ⥤ DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) :=
  IsoAlgebra.forget (Etale.upperStar A e.hom).mapDerivedCategoryPlus

/-- A bounded below Weil complex is in particular a Weil complex: the square

```
                  mapDerivedCategoryPlus
      D⁺(X_ét, A) ----------------------> D⁺(X_ét, A)
           |                                   |
          ι                                   ι
           v                                   v
        D(X_ét)  ------------------------>  D(X_ét)
                    mapDerivedCategory
```

commutes by `CategoryTheory.Functor.mapDerivedCategoryPlusCompatibility`, and its
commutation isomorphism transports the structure isomorphism. -/
def WeilComplexPlus.toWeilComplex : WeilComplexPlus A e ⥤ WeilComplex A e :=
  IsoAlgebra.mapOfNatIso (L := DerivedCategory.Plus.ι)
    (Etale.upperStar A e.hom).mapDerivedCategoryPlusCompatibility.symm

end WeilComplexPlus

section WeilComplexBoundedConstructible

/-- A *bounded constructible Weil complex* for a scheme `X` with an automorphism
`e : X ≅ X` is an object `K` of the bounded constructible derived category `Dᵇc(X, A)`
together with an isomorphism `Φ : e^* K ≅ K`, where `e^*` acts on `Dᵇc(X, A)` through
`AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible.upperStar`, the restriction
of the derived pullback. The isomorphism `Φ` is structure data. This is the category in
which the `ℓ`-adic formalism of the Weil conjectures takes place. -/
abbrev WeilComplexBoundedConstructible : Type _ :=
  IsoAlgebra (Etale.DerivedCategoryBoundedConstructible.upperStar A e.hom)

/-- The forgetful functor from bounded constructible Weil complexes to `Dᵇc(X, A)`,
discarding the Frobenius structure isomorphisms. -/
def WeilComplexBoundedConstructible.forget :
    WeilComplexBoundedConstructible A e ⥤ Dᵇc(X, A) :=
  IsoAlgebra.forget (Etale.DerivedCategoryBoundedConstructible.upperStar A e.hom)

/-- A bounded constructible Weil complex is in particular a bounded below Weil complex:
the square

```
                        upperStar
         Dᵇc(X, A) -----------------> Dᵇc(X, A)
             |                            |
          toPlus                       toPlus
             v                            v
        D⁺(X_ét, A) ---------------> D⁺(X_ét, A)
                  mapDerivedCategoryPlus
```

commutes by
`AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible.toPlusUpperStarIso`, and its
commutation isomorphism transports the structure isomorphism. -/
def WeilComplexBoundedConstructible.toWeilComplexPlus :
    WeilComplexBoundedConstructible A e ⥤ WeilComplexPlus A e :=
  IsoAlgebra.mapOfNatIso (Etale.DerivedCategoryBoundedConstructible.toPlusUpperStarIso A e.hom)

/-- A bounded constructible Weil complex is in particular a Weil complex, through the
bounded below Weil complexes. -/
def WeilComplexBoundedConstructible.toWeilComplex :
    WeilComplexBoundedConstructible A e ⥤ WeilComplex A e :=
  WeilComplexBoundedConstructible.toWeilComplexPlus A e ⋙ WeilComplexPlus.toWeilComplex A e

/-- The Weil sheaf structure on the `n`-th homology sheaf of a bounded constructible Weil
complex, obtained through the underlying Weil complex. -/
def WeilComplexBoundedConstructible.homologyFunctor (n : ℤ) :
    WeilComplexBoundedConstructible A e ⥤ WeilSheaf A e :=
  WeilComplexBoundedConstructible.toWeilComplex A e ⋙ WeilComplex.homologyFunctor A e n

end WeilComplexBoundedConstructible

end

end AlgebraicGeometry

end
