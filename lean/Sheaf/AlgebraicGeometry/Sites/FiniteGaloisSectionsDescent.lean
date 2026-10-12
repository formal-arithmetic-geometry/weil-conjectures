/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.Galois.Basic
import Sheaf.AlgebraicGeometry.FiniteGaloisTensorDecomposition

/-!
# Finite Galois descent for sections of an etale sheaf

Source: Stacks Project, Etale Cohomology, Tag 04JM, Lemma
`lemma-global-sections-point`, finite Galois descent argument
(blueprint: lem-exc-finite-galois-sections-descent).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.Etale.of_finite_of_isSeparable

/-- (blueprint: lem-exc-finite-galois-sections-descent) Stacks Project, Tag 04JM.
For a finite Galois extension `E/L`, pullback from `Spec L` to `Spec E` identifies
the sections of any sheaf of sets on the small etale site of `Spec L` with the
sections fixed by every `L`-automorphism of `E`.

The finite separable extension gives an etale cover `Spec E -> Spec L`.
The Galois tensor decomposition identifies the two restrictions to its self-intersection
with the constant family and the family of Galois pullbacks. The sheaf equalizer condition
then identifies sections downstairs with precisely the invariant sections upstairs. -/
theorem finiteGaloisSectionsDescent
    (L E : Type u) [Field L] [Field E] [Algebra L E]
    [FiniteDimensional L E] [IsGalois L E]
    (F : Sheaf (Spec (.of L)).smallEtaleTopology (Type v)) :
    Set.BijOn (F.obj.map (etaleSpecMap (Algebra.ofId L E)).op)
      Set.univ
      {s | ∀ q : E ≃ₐ[L] E, F.obj.map (etaleSpecMap q).op s = s} := by
  sorry

end AlgebraicGeometry.Scheme
