/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
import Sheaf.AlgebraicGeometry.FiniteTorDimensionOver
import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Perfect direct image of a bounded coherent finite-Tor complex

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.27.1 (Tag 08EV)
(blueprint: lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect).
-/

universe u wX wS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A bounded coherent complex with proper cohomological support and finite Tor dimension
 over the inverse-image structure sheaf has perfect derived direct image.
Source: Stacks Project, Derived Categories of Schemes, Lemma 36.27.1 (Tag 08EV)
(blueprint: lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect).

Proof:
1. Apply lem-pc-direct-image-bounded-coherent: the Noetherian base, locally finite-type
   morphism, bounded coherent cohomology, and proper supports give bounded coherent
   cohomology of Rf_*E.
2. Apply lem-pc-noetherian-bounded-coherent-pseudo-coherent on S to obtain pseudo-coherence.
3. Apply lem-pc-proper-direct-image-finite-tor to the same hypotheses and the finite Tor
   dimension over f⁻¹𝒪_S. Its proper-support reduction, projection formula and Tor bounds
   give finite Tor dimension of Rf_*E over 𝒪_S.
4. Apply lem-pc-pseudo-coherent-finite-tor-perfect to the conclusions of steps 2 and 3.
-/
theorem isPerfect_schemeDerivedDirectImage_of_bounded_coherent_finiteTor
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{wS} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hcoherent : ∀ i : ℤ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hsupport : ∀ i : ℤ,
      Scheme.Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hTor : HasFiniteTorDimensionOver f E) :
    IsPerfect S ((schemeDerivedDirectImage f).obj E) := by
  sorry

end AlgebraicGeometry.Scheme
