/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Copowers for proper geometric-point derived direct image

This is the component-level comparison used to assemble preservation of all discrete
colimits.  Its proof is the finite-coefficient proper cohomology argument from Tags 0F11
and 0F12.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Proper direct image over a geometric point preserves a sum of copies of one object.
Source: Stacks Project, Lemma 59.96.3 (Tag 0F11), used in Lemma 59.96.5 (Tag 0F12).
(blueprint: lem-etale-proper-geometric-point-derived-copowers)

Proof in words: choose a K-injective representative J of E with injective terms. The
termwise sum of I copies of J represents this copower. Properness gives a finite-type
scheme over k and hence a uniform finite torsion cohomological-dimension bound for finite
coefficient sheaves. The module-cohomology forgetful comparison transfers this bound to
modules. Module sheaves on Spec k are constant, identifying global cohomology with higher
pushforward. Higher pushforward commutes with filtered colimits and finite sums, and thus
with this copower. Consequently each term of the copower of J is pushforward-acyclic.
The finite-dimension acyclic-complex theorem computes the unbounded derived pushforward
by applying pushforward termwise. Its degree-zero copower comparison is invertible, so
localizing this termwise comparison gives the required image colimit cocone. The positive
additive characteristic of the finite ring supplies torsion, including the zero ring.
For empty I the termwise complex and its direct image are zero. -/
theorem proper_geometricPoint_preservesCopowers
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p]
    (I : Type (u + 1))
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    PreservesColimit (Discrete.functor (fun _ : I ↦ E))
      (R((p)_*[ModuleCat.{u + 1} Λ])) := by
  sorry

end AlgebraicGeometry.Etale
