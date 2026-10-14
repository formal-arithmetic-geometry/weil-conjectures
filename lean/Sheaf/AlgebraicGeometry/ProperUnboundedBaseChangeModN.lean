/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAcyclic
import Sheaf.AlgebraicGeometry.TorsionAssembly
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Unbounded proper base change for finite cyclic coefficients -/

@[expose] public section

universe u

open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme
variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Proper base change on unbounded complexes with coefficients in Z/nZ, n positive.
Source: Stacks Project, Tag 0F0C (Lemma 59.92.3), with Tags 095U, 07K7, and 079P.
(blueprint: lem-kun-0f0c)

Proof in words: first work with quasi-compact bases. Properness and quasi-compactness
bound the dimensions of all fibres of f and its pullback f'. Every Z/nZ-module sheaf
is killed by n, so the torsion cohomological-dimension bound of Tag 095U applies to
both direct images. Choose a K-injective representative I whose individual terms
are injective module sheaves (Tag 079P). Each term is f_*-acyclic. After forgetting
coefficients, its positive higher direct images vanish, by the restriction-of-scalars
acyclicity comparison. Ordinary torsion proper base change identifies these higher
direct images with those of g'^*I under f'_*, so g'^*I is termwise f'_*-acyclic too.
The finite-dimension acyclic-complex lemma (Tag 07K7) computes both unbounded derived
direct images by these termwise direct images. In degree zero, ordinary proper base
change identifies g^*f_*I with f'_*g'^*I term by term. Exact inverse image and the
canonical adjunction units and counits identify this chain isomorphism with the
canonical derived exchange, proving invertibility. For general bases, cover Y by
affine opens and cover their inverse images in Y' by affine opens separately. Apply
the quasi-compact argument to each restricted cartesian square, and glue the
isomorphism assertion using locality of the canonical exchange. No quasi-compactness
of the inverse image of an affine open is assumed. Universe lifting changes neither
the coefficient ring nor the underlying sheaf-theoretic argument. -/
theorem Etale.isIso_derivedBaseChangeMap_of_isProper_modN
    (n : ℕ) (hn : 0 < n) [IsProper f] (sq : IsPullback g' f' f g) :
    IsIso (Etale.derivedBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) sq.toCommSq) := by
  sorry

end AlgebraicGeometry
