/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation

/-!
# Constructibility of projective direct images

For a finite ring `Λ` killed by an integer invertible in a field `k`, this file proves that
every projective morphism `f` between schemes of finite type over `k` satisfies `𝒞(f)`: its
higher direct images preserve constructibility.

- `AlgebraicGeometry.Etale.hasConstructibleDirectImages_projectiveLine`
  (`thm-fin-projective-line-constructible`): the projective line `ℙ¹_S ⟶ S`, by resolving a
  constructible sheaf by finite pushforwards of constant sheaves and using the case of curves;
- `AlgebraicGeometry.Etale.HasConstructibleDirectImages.of_projectiveLine`
  (`lem-finrepair-projective-from-line`): from the projective line to all projective morphisms,
  through `(ℙ¹_S)ⁿ ⟶ ℙⁿ_S` (finite and surjective) and composition;
- `AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_isClosedImmersion`
  (`thm-fin-projective-constructibility-complete`).

A morphism `f : X ⟶ S` is projective (`def-pc-projective-morphism`) if it is the composite of a
closed immersion `X ⟶ ℙ(N; S)`, for a finite type `N` of homogeneous coordinates, with the
structure morphism; quasi-compactness is automatic here, `S` being Noetherian.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

/-- Blueprint `thm-fin-projective-line-constructible`: Constructible coefficients on the
projective line.

Let `S` be of finite type over a field `k`, and let `Λ` be a finite ring killed by an integer
invertible in `k`. For every constructible sheaf `F` of `Λ`-modules on `ℙ¹_S`, every higher
direct image `Rᵠπ_* F` along `π : ℙ¹_S ⟶ S` is constructible. -/
theorem hasConstructibleDirectImages_projectiveLine [HasInvertibleExponent Λ (Spec (.of k))]
    {S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] :
    HasConstructibleDirectImages Λ (ProjectiveLine S ↘ S) :=
  sorry

/-- Blueprint `lem-finrepair-projective-from-line`: Projective constructibility from
projective-line constructibility.

Suppose `𝒞(ℙ¹_T ⟶ T)` holds for every scheme `T` of finite type over `k`. Then `𝒞(f)` holds for
every projective morphism `f : X ⟶ S` with `S` of finite type over `k`: here `f` is the
composite of a closed immersion `e : X ⟶ ℙ(N; S)` with the structure morphism. -/
theorem HasConstructibleDirectImages.of_projectiveLine
    (h : ∀ (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT],
      HasConstructibleDirectImages Λ (ProjectiveLine T ↘ T))
    {X S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (f : X ⟶ S) (N : Type u) [Finite N] (e : X ⟶ ℙ(N; S)) [IsClosedImmersion e]
    (he : e ≫ ℙ(N; S) ↘ S = f) : HasConstructibleDirectImages Λ f :=
  sorry

/-- Blueprint `thm-fin-projective-constructibility-complete`: Projective direct-image
constructibility.

Let `Λ` be a finite ring killed by an integer invertible in the field `k`. Every projective
morphism `f : X ⟶ S` with `S` of finite type over `k` (so `f` is the composite of a closed
immersion `e : X ⟶ ℙ(N; S)` with the structure morphism) satisfies `𝒞(f)`. -/
theorem hasConstructibleDirectImages_of_isClosedImmersion
    [HasInvertibleExponent Λ (Spec (.of k))] {X S : Scheme.{u}} (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) (N : Type u) [Finite N]
    (e : X ⟶ ℙ(N; S)) [IsClosedImmersion e] (he : e ≫ ℙ(N; S) ↘ S = f) :
    HasConstructibleDirectImages Λ f :=
  HasConstructibleDirectImages.of_projectiveLine
    (fun _ aT _ _ ↦ hasConstructibleDirectImages_projectiveLine aT) aS f N e he

end Etale

end AlgebraicGeometry
