/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# Weil objects in the bounded constructible derived category

Let `Λ` be a commutative condensed ring and `X` a scheme with an automorphism `e : X ≅ X`. The
*Frobenius pullback* on the bounded constructible derived category `Dᵇc(X)⟦Λ⟧` of module
objects over `Λ_X = p_X^* Λ` is the restricted derived pullback
`Φ_X := Le^* = boundedConstructibleUpperStar Λ ℓ k e.hom`. The coefficients are kept fixed by
construction: the pullback on module objects over `Λ` is the extension of scalars along the
coefficient isomorphism `α_e : e^* Λ_X ≅ Λ_X`, and the preservation of bounded constructibility
is the input `boundedConstructible_leftDerivedUpperStar_obj`.

A *Weil object* of `Dᵇc(X)⟦Λ⟧` for `e` is an object `K` together with an isomorphism
`φ_K : Φ_X K ≅ K` as structure data, that is an object of
`CategoryTheory.Endofunctor.IsoAlgebra Φ_X`
(`ProEtale.CondensedRing.WeilBoundedConstructible`). Morphisms are morphisms of `Dᵇc(X)⟦Λ⟧`
commuting with the structure isomorphisms.

Forgetting bounded constructibility, a Weil object of `Dᵇc(X)⟦Λ⟧` is a Weil object of the
ambient derived category `D(Mod_{Λ_X})` for the derived pullback `L((e.hom)^*⟦Λ⟧)`: this is the
transport of algebras along the inclusion, using the compatibility isomorphism
`boundedConstructibleUpperStarCompatibility`
(`ProEtale.CondensedRing.WeilBoundedConstructible.toDerivedCategory`).

## The setting

The setting is that of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`: a prime `ℓ`,
a field `k` of characteristic `p > 0` with `p ≠ ℓ`, and `X` separated and of finite type over
`Spec k`. The automorphism `e` is required to be a morphism over `Spec k`
(`[e.hom.IsOver (Spec (.of k))]`), as is every morphism to which the bounded constructible
pullback applies.

## Implementation notes

The geometric Galois Frobenius `Scheme.Hom.geometricFrobenius` of the geometric fiber of a
scheme over a finite field `𝔽_q` is semilinear over `k̄ = 𝔽̄_q`, not a morphism over
`Spec k̄`, and the geometric fiber is not of finite type over `𝔽_q`. It therefore does not fit
the hypothesis `[e.hom.IsOver (Spec (.of k))]` for either choice of `k`. Applying the present
definitions to it requires extending the bounded constructible pullback beyond `k`-morphisms, or
a Frobenius-twist interface; this is not done here.

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible`: the category of Weil objects of
  `Dᵇc(X)⟦Λ⟧` for an automorphism `e` of `X` over `Spec k`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.forget`: the forgetful functor to
  `Dᵇc(X)⟦Λ⟧`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.toDerivedCategory`: the functor to the Weil
  objects of `D(Mod_{Λ_X})` for the derived pullback along `e`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
  (e : X ≅ X) [e.hom.IsOver (Spec (.of k))]

/-- A *Weil object* of the bounded constructible derived category `Dᵇc(X)⟦Λ⟧` for an
automorphism `e : X ≅ X` over `Spec k` is an object `K` together with an isomorphism
`φ_K : Le^* K ≅ K`, where `Le^* = boundedConstructibleUpperStar Λ ℓ k e.hom` is the restricted
derived pullback along `e`. The isomorphism `φ_K` is structure data, and morphisms are morphisms
of `Dᵇc(X)⟦Λ⟧` commuting with the structure isomorphisms. -/
abbrev WeilBoundedConstructible : Type _ :=
  IsoAlgebra (boundedConstructibleUpperStar Λ ℓ k e.hom)

namespace WeilBoundedConstructible

/-- The forgetful functor from Weil objects of `Dᵇc(X)⟦Λ⟧` to `Dᵇc(X)⟦Λ⟧`, discarding the
Frobenius structure isomorphisms. -/
noncomputable def forget : WeilBoundedConstructible Λ ℓ k e ⥤ Dᵇc(X)⟦Λ⟧ :=
  IsoAlgebra.forget (boundedConstructibleUpperStar Λ ℓ k e.hom)

/-- A Weil object of `Dᵇc(X)⟦Λ⟧` is a Weil object of the ambient derived category
`D(Mod_{Λ_X})` for the derived pullback `L((e.hom)^*⟦Λ⟧)`: the transport of algebras along the
inclusion, the structure isomorphism of `K` being
`L((e.hom)^*⟦Λ⟧) K ≅ Le^* K ≅ K` through `boundedConstructibleUpperStarCompatibility`. -/
noncomputable def toDerivedCategory :
    WeilBoundedConstructible Λ ℓ k e ⥤ IsoAlgebra L((e.hom)^*⟦Λ⟧) :=
  IsoAlgebra.mapOfNatIso (boundedConstructibleUpperStarCompatibility Λ ℓ k e.hom).symm

@[simp]
lemma toDerivedCategory_obj_carrier (K : WeilBoundedConstructible Λ ℓ k e) :
    ((toDerivedCategory Λ ℓ k e).obj K).carrier = K.carrier.obj :=
  rfl

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
