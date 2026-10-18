/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar


/-! # BoundedConstructibleLowerStarHomology

The constructible-cohomology component of ordinary direct-image finiteness.
-/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- Every homology module of the derived module-object pushforward is constructible.

Source: Bhatt--Scholze, Section 6.8, and blueprint `lem-sfb-dc-lower-star-preserves`,
steps 1--8 (the constructible-cohomology component).
For integral coefficients the stratified-perfect characterization makes the input derived
complete with uniformly bounded, constructible finite reductions. Right derived direct image
preserves the completion tower. The perfect projection formula identifies reduction of the
ambient direct image with the finite-level direct image. Etale/pro-etale comparison and
finite-coefficient direct-image finiteness make every such reduction constructible, and the
uniform cohomological-dimension bound bounds all their amplitudes simultaneously. The reverse
stratified-perfect characterization consequently identifies the ambient direct image as a
bounded complex with stratified locally finitely presented homology. For rational coefficients,
choose an integral constructible representative, localize by ell, and commute the uniformly
bounded-below localization diagram with direct image. Exact scalar extension preserves the
constructible homology presentations. For algebraic-closure coefficients, descend the input to
a finite extension. Finite-free coefficient extension commutes with direct image, and filtered
continuity identifies extension to the algebraic closure with the direct image there; again
exact extension carries the homology presentations across. A unit-ball presentation identifies
with its integral coefficient ring. For finite discrete ell-primary rings, use the finite-type
etale direct-image finiteness theorem and etale/pro-etale comparison directly. The zero ring,
zero complex and empty scheme satisfy the assertion with rank-zero presentations.
(blueprint: lem-sfb-dc-lower-star-constructibility) -/
theorem boundedConstructible_rightDerivedLowerStar_constructible
    [IsFinitenessCoefficient ℓ Λ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K) (n : ℤ) :
    IsConstructibleModuleObject (condensedRingObj Λ Y.left)
      ((DerivedCategory.homologyFunctor _ n).obj ((R((f.left)_*⟦Λ⟧)).obj K)) := by
  sorry


end AlgebraicGeometry.ProEtale.CondensedRing
