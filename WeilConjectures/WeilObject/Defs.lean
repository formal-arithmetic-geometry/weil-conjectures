/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

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

Two layers are provided, each with its forgetful functor to the underlying category:

- `AlgebraicGeometry.WeilSheaf`, for étale sheaves on `X`;
- `AlgebraicGeometry.WeilComplex`, for the derived category of étale sheaves on `X`.

Since `e^*` is t-exact, a Weil complex induces for every `n` a Weil sheaf structure
`e^* Hⁿ(K) ≅ Hⁿ(e^* K) ≅ Hⁿ(K)` on its `n`-th homology sheaf. This is packaged as the
functor `AlgebraicGeometry.WeilComplex.homologyFunctor` into `AlgebraicGeometry.WeilSheaf`,
built from the general transport of algebras
`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso` along the homology commutation isomorphism
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` of the exact functor `e^*`.

Bounded and constructible variants, the canonical Weil structure on objects descended
from `X₀` and the transport of Weil structures through `Rf_!` are subsequent layers built
on top of these definitions.

## Implementation notes

Following the convention of the `SixFunctors` folder, the coefficient category `A` is a
Grothendieck abelian category with `Hom`-types in the universe `u + 1`, one above the
universe `u` of the base schemes. This is what makes the pullback
`AlgebraicGeometry.Etale.upperStar` exist and be exact, and what supplies the derived
category of étale sheaves.

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

-/

@[expose] public section

universe u u'

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
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

end

end AlgebraicGeometry

end
