/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Bounded coherent direct image in the Noetherian proper case

Source: Stacks Project, Tag 08E2, specialized to a proper morphism; Tag 02O5.
(blueprint: lem-pc-noetherian-proper-bounded-coherent-image).
-/

@[expose] public section
set_option autoImplicit false
universe u wY wT
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A proper morphism over a Noetherian base preserves bounded coherent cohomology.
This asserts neither a finite-free representative nor pseudo-coherence or a base-change
comparison. Source: Stacks Project, Tag 08E2, Lemma 36.11.3; Tag 02O5.

Proof: Coherence makes every cohomology sheaf quasi-coherent and finite type on the
locally Noetherian source. Its nonzero-stalk locus is closed. Because p is proper, the
closed support is proper over T. Apply the hypercohomology spectral sequence for derived
pushforward. Its E2 terms are the higher direct images of these coherent sheaves, hence
coherent by proper coherence over a Noetherian base (Tag 02O5). In each total degree its
finite filtration has coherent subquotients, so the abutment is coherent. The lower
bound is the lower bound of A, since pushforward is left exact. For the upper bound,
p is quasi-compact and separated and T is quasi-compact. A finite affine cover yields a
uniform bound on the higher direct images of quasi-coherent modules; equivalently use
the derived uniform truncation bound of Tag 08D5. Shift A by its upper cohomology bound
and apply this bound, then shift back. This gives a finite interval containing all image
cohomology. The zero object gives zero image. For an empty source the image is zero.
No relative flatness, finite Tor dimension or finite-free image is used.

The existing proper-support direct-image module cannot be imported here: its current
proof dependencies reach the arbitrary-base pseudo-coherence item. This strictly
Noetherian proper case isolates the calculation needed before approximation pullback.
(blueprint: lem-pc-noetherian-proper-bounded-coherent-image). -/
theorem noetherian_proper_directImage_bounded_coherent
    {Y T : Scheme.{u}} [IsNoetherian T] (p : Y ⟶ T)
    [IsProper p]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wT}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (A : schemeDerivedCategory Y)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A))
    (hcoherent : ∀ i : ℤ, RingedSpace.IsCoherent Y.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A)) :
    (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj
          ((schemeDerivedDirectImage p).obj A))) ∧
    (∀ i : ℤ, RingedSpace.IsCoherent T.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj
          ((schemeDerivedDirectImage p).obj A))) := by sorry

end AlgebraicGeometry.Scheme
