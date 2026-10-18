/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q44
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel
import Sheaf.RingTheory.RingPseudoCoherent
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-! # Bounded finite Tor amplitude implies perfect

Source: Stacks Project, Tags 0658, 066E, 00NZ
(blueprint: lem-weil-bounded-finite-tor-perfect).
-/

@[expose] public section

universe u w

open CategoryTheory Limits

namespace DerivedCategory

/-- A bounded complex of finite modules with Tor amplitude in `[a,b]` admits a
bounded finite-projective model in exactly that interval; over a local ring the
model can be chosen finite free.

Source: Stacks Project, Tags 0658, 066E, 00NZ
(blueprint: lem-weil-bounded-finite-tor-perfect).
Proof:
1. The cycles of `K` are finite by `lem-weil-pbc-noetherian-submodule-finite`;
   their quotient cohomology is finite. Boundedness gives an upper cohomological
   bound, so `lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion` makes
   `Q.obj K` pseudo-coherent.
2. By `def-pc-ring-pseudo-coherent-complex`, choose a bounded-above finite-free
   representative. Its terms are flat by
   `lem-sc-affine-standard-cover-finite-free-local-fp-flat`, and it is K-flat by
   `lem-pc-module-bounded-flat-kflat`, in the sense of `def-pc-module-kflat-complex`.
   The comparison `lem-pc-source-kflat-module-tensor-model`, tested with `R[0]`,
   and the ordinary tensor-unit isomorphism show that cohomology vanishes outside
   `[a,b]`, in particular above `b`.
3. Apply `lem-pc-pseudo-coherent-bounded-finite-free-model` to obtain a finite-free
   representative `P` zero above `b`. Again it is flat and K-flat by the preceding
   flatness and K-flatness nodes. The same tensor-model comparison identifies
   `H^(a-1)(P tensor M)` with the corresponding derived tensor cohomology, zero
   for every module `M` by the Tor-amplitude hypothesis.
4. Let `Q` be the cokernel of `P^(a-1) → P^a`. It is flat by
   `lem-pc-module-flat-opcycles-tor-criterion`. Finite bases of these two terms
   give a finite presentation of `Q`, so
   `lem-weil-pbc-finitely-presented-flat-module-projective` makes it finite projective.
5. Form the quotient truncation `E`: zero below `a`, `Q` in degree `a`, and `P`
   above `a`. Its bottom differential descends since consecutive differentials
   compose to zero. The quotient chain map `P → E` preserves cohomology in degree
   `a` by the kernel modulo image formula, in degree `a+1` by surjectivity onto
   `Q`, and in all higher degrees directly; below `a` both cohomologies vanish.
   It is a quasi-isomorphism and becomes invertible by
   `def-weil-abstract-derived-category`. Since `a ≤ b`, the resulting model is
   supported in `[a,b]`. Its other terms are projective by
   `lem-weil-pbc-free-module-projective`, proving `def-pc-perfect-ring-complex`.
6. If `R` is local, `lem-weil-pbc-finite-flat-local-free` makes the bottom finite
   flat term free. Finite generation gives a finite basis, and all other terms
   already are finite free, including the zero terms with their empty bases.
-/
theorem exists_bounded_finite_projective_model_of_torAmplitudeIn
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∃ c d : ℤ, K.IsStrictlyGE c ∧ K.IsStrictlyLE d ∧
      ∀ i : ℤ, Module.Finite R (K.X i))
    (a b : ℤ) (hab : a ≤ b)
    (hTor : torAmplitudeIn (ModuleCat.{u} R) a b (Q.obj K)) :
    (∃ E : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i)) ∧
      (∀ i : ℤ, Module.Projective R (E.X i) ∧ Module.Finite R (E.X i)) ∧
      Nonempty (Q.obj E ≅ Q.obj K)) ∧
      IsPerfectRingComplex (Q.obj K) ∧
      (IsLocalRing R →
        ∃ E : CochainComplex (ModuleCat.{u} R) ℤ,
          (∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i)) ∧
          (∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)) ∧
          Nonempty (Q.obj E ≅ Q.obj K)) := by
  sorry

end DerivedCategory
