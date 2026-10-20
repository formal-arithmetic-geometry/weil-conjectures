/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Constructible coefficients on the projective line

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/thm-fin-projective-line-constructible.md`,
order 1618 (blueprint: thm-fin-projective-line-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- Every higher direct image of a constructible finite-coefficient module sheaf along
`ℙ¹_S → S` is constructible when `S` is of finite type over a field and the coefficients
are annihilated by a positive integer invertible in that field. The coefficient convention
is imposed on `Spec k`; invertibility of its constant global section is invertibility in `k`.
The two homogeneous coordinates are indexed by `ULift (Fin 2)`.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/thm-fin-projective-line-constructible.md`,
order 1618 (blueprint: thm-fin-projective-line-constructible).

Proof. Work first over an affine open of `S`, with the original finite coefficient ring.
Every constructible sheaf embeds into a finite sum of finite pushforwards of finite constant
module sheaves. These sums are constructible. The proved embedding criterion
`hasConstructibleDirectImages_of_exists_mono` reduces the assertion to their higher images;
its finite truncation argument replaces the explicit Cartan–Eilenberg resolution of the plan.
Derived direct image and homology preserve these finite sums.

For a finite morphism `h` into the projective line, the composite with the projection is
projective over the affine Noetherian base. After any geometric base change the map from its
fibre to the projective-line fibre is finite, hence integral. Incomparability of primes says
this map identifies no two comparable points, so it cannot increase topological Krull
dimension. The projective-line fibre has dimension at most one.

The additive group of a finite module killed by `N` has order dividing a power of `N`, hence
invertible on the base. Apply projective-curve finiteness for finite constant abelian sheaves.
The coefficient-forgetting comparison identifies this with the underlying abelian sheaf of
the module higher image. Its finite locally constant strata remain finite locally constant
on forgetting to sets; the finite-coefficient reconstruction theorem recovers module
constructibility. Exactness of finite direct image and the derived composition isomorphism
identify this result with the higher image of the finite pushforward used in the embedding.

Finally apply this affine argument to every affine open of `S`. The cartesian projective-space
base-change square and étale localization identify the restricted higher images. Constructibility
is local for this open cover on the Noetherian base. Convert between the two constructibility
predicates and between bounded-below and unbounded derived categories using their comparison
isomorphisms. The argument includes empty bases and every integer cohomological degree.
-/
theorem isConstructibleEtaleModuleSheaf_higherDirectImage_projectiveLine
    (k : Type u) [Field k] (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)))
    (F : Sheaf (ProjectiveSpace (ULift.{u} (Fin 2)) S).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
    (hF : @Scheme.IsConstructibleEtaleModuleSheaf
      (ProjectiveSpace (ULift.{u} (Fin 2)) S) Λ _ hcoeff.2.1 F) (q : ℤ) :
    @Scheme.IsConstructibleEtaleModuleSheaf S Λ _ hcoeff.2.1
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ)
          (ProjectiveSpace (ULift.{u} (Fin 2)) S ↘ S)).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (ProjectiveSpace (ULift.{u} (Fin 2)) S).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)) 0).obj F))) := by
  let : Finite Λ := hcoeff.2.1
  let : HasInvertibleExponent Λ (Spec (.of k)) :=
    ⟨N, hcoeff.1, hcoeff.2.2.1, hcoeff.2.2.2⟩
  -- The source library already proves the projective-line argument for these coefficients.
  have hC := hasConstructibleDirectImages_projectiveLine (Λ := Λ)
    (S ↘ Spec (.of k)) F ((Scheme.isConstructibleEtaleModuleSheaf_iff F).1 hF) q
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff _).2
  let R := lowerStar (ModuleCat.{u + 1} Λ) (ProjectiveLine S ↘ S)
  exact @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (R.rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).symm hC

end AlgebraicGeometry.Etale
