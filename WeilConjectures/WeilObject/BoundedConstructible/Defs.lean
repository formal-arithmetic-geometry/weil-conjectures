/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# Weil objects in the bounded constructible derived category of `ℚ̄_ℓ`-sheaves

Let `ℓ` be a prime and `ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ` the condensed ring of `ℚ̄_ℓ`, and let
`X` be a scheme with an automorphism `e : X ≅ X`. The *Frobenius pullback* on the bounded
constructible derived category `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` of `ℚ̄_ℓ`-sheaves, the module objects over
`ℚ̲̄_ℓ,X = p_X^* ℚ̲̄_ℓ`, is the restricted derived pullback
`Φ_X := Le^* = boundedConstructibleUpperStar ℚ̲̄_ℓ ℓ k e.hom`. The coefficients are kept fixed by
construction: the pullback on module objects is the extension of scalars along the coefficient
isomorphism `α_e : e^* ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X`, and the preservation of bounded constructibility is the
input `boundedConstructible_leftDerivedUpperStar_obj`.

A *Weil object* of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `e` is an object `K` together with an isomorphism
`φ_K : Φ_X K ≅ K` as structure data, that is an object of
`CategoryTheory.Endofunctor.IsoAlgebra Φ_X`
(`ProEtale.CondensedRing.WeilBoundedConstructible`). Morphisms are morphisms of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`
commuting with the structure isomorphisms.

Forgetting bounded constructibility, a Weil object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` is a Weil object of the
ambient derived category `D(Mod_{ℚ̲̄_ℓ,X})` for the derived pullback `L((e.hom)^*⟦ℚ̲̄_ℓ⟧)`: this is
the transport of algebras along the inclusion, using the compatibility isomorphism
`boundedConstructibleUpperStarCompatibility`
(`ProEtale.CondensedRing.WeilBoundedConstructible.toDerivedCategory`).

## The setting

The setting is that of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, specialized to
the coefficient ring `ℚ̲̄_ℓ`: a prime `ℓ`, a field `k` of characteristic `p > 0` with `p ≠ ℓ`,
and `X` separated and of finite type over `Spec k`. The automorphism `e` is required to be a
morphism over `Spec k` (`[e.hom.IsOver (Spec (.of k))]`), as is every morphism to which the
bounded constructible pullback applies.

## Implementation notes

The geometric Galois Frobenius `Scheme.Hom.geometricFrobenius` of the geometric fiber of a
scheme over a finite field `𝔽_q` is semilinear over `k̄ = 𝔽̄_q`, not a morphism over
`Spec k̄`, and the geometric fiber is not of finite type over `𝔽_q`. It therefore does not fit
the hypothesis `[e.hom.IsOver (Spec (.of k))]` for either choice of `k`. Applying the present
definitions to it requires extending the bounded constructible pullback beyond `k`-morphisms, or
a Frobenius-twist interface; this is not done here.

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible`: the category of Weil objects of
  `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for an automorphism `e` of `X` over `Spec k`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.forget`: the forgetful functor to
  `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.toDerivedCategory`: the functor to the Weil
  objects of `D(Mod_{ℚ̲̄_ℓ,X})` for the derived pullback along `e`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
  (e : X ≅ X) [e.hom.IsOver (Spec (.of k))]

/-- A *Weil object* of the bounded constructible derived category `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` of
`ℚ̄_ℓ`-sheaves for an automorphism `e : X ≅ X` over `Spec k` is an object `K` together with an
isomorphism `φ_K : Le^* K ≅ K`, where `Le^* = boundedConstructibleUpperStar ℚ̲̄_ℓ ℓ k e.hom` is
the restricted derived pullback along `e`. The isomorphism `φ_K` is structure data, and
morphisms are morphisms of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` commuting with the structure isomorphisms. -/
abbrev WeilBoundedConstructible : Type _ :=
  IsoAlgebra (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k e.hom)

namespace WeilBoundedConstructible

/-- The forgetful functor from Weil objects of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` to `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, discarding the
Frobenius structure isomorphisms. -/
noncomputable def forget :
    WeilBoundedConstructible ℓ k e ⥤ Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  IsoAlgebra.forget (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k e.hom)

/-- A Weil object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` is a Weil object of the ambient derived category
`D(Mod_{ℚ̲̄_ℓ,X})` for the derived pullback `L((e.hom)^*⟦ℚ̲̄_ℓ⟧)`: the transport of algebras along
the inclusion, the structure isomorphism of `K` being
`L((e.hom)^*⟦ℚ̲̄_ℓ⟧) K ≅ Le^* K ≅ K` through `boundedConstructibleUpperStarCompatibility`. -/
noncomputable def toDerivedCategory :
    WeilBoundedConstructible ℓ k e ⥤
      IsoAlgebra L((e.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  IsoAlgebra.mapOfNatIso
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ k e.hom).symm

@[simp]
lemma toDerivedCategory_obj_carrier (K : WeilBoundedConstructible ℓ k e) :
    ((toDerivedCategory ℓ k e).obj K).carrier = K.carrier.obj :=
  rfl

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
