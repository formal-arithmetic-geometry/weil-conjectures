/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
import Sheaf.RingTheory.GeometricReducednessSeparableScalarRestriction
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Geometric reducedness and transcendence degree in a field diamond

Source: Stacks Project, Algebra, Tag 0C2Y and `lemma-subalgebra-separable` (1), and
Fields, Tag 030H; extracted for de Jong, Families of curves and alterations (1997),
Lemma 5.2 proof, printed p. 613
(blueprint: lem-sfb-geometric-subfield-scalar-restriction).
-/

@[expose] public section

universe u v w x t

open scoped TensorProduct

namespace Algebra

/-- Geometric reducedness descends through separable algebraic scalar restriction and to
an intermediate subfield. In the field diamond `k₀ ⊆ k ⊆ E`, `k₀ ⊆ F ⊆ E`, algebraicity
of `E/F` also identifies all three stated transcendence degrees. The two scalar towers
express compatibility of the inclusions into `E`; there is no inclusion assumption between
`k` and `F`. Test fields lie in a common enlarged universe, and cardinal lifts compare
transcendence degrees for fields in different universes. Tensor products have their usual
commutative algebra multiplication; reducedness means every nilpotent element is zero.

Source: Stacks Project, Algebra, Tag 0C2Y, `lemma-subalgebra-separable` (1), and Fields,
Tag 030H; de Jong (1997), Lemma 5.2 proof, printed p. 613
(blueprint: lem-sfb-geometric-subfield-scalar-restriction).

Proof:
1. Apply `lem-trf-geometric-reducedness-separable-scalar-restriction` to `k₀ ⊆ k`
   and the algebra `E`. Its right-to-left implication turns the geometric reducedness
   hypothesis over `k` into reducedness of `E ⊗[k₀] L` for every field extension `L/k₀`.
   Swapping tensor factors reconciles the cited theorem's factor order with this one.
2. The `k₀`-vector space `L` is free, hence flat, by
   `lem-weil-pbc-module-over-field-flat`. Apply `lem-trf-flat-tensor-preserves-injection`
   to the `k₀`-linear inclusion `F → E`, then swap factors. This gives the injective
   ring map `F ⊗[k₀] L → E ⊗[k₀] L`, sending `a ⊗ b` to `i(a) ⊗ b`.
   A nilpotent maps to a nilpotent in the reduced target, hence to zero; injectivity
   implies that it was zero. No inclusion of `k` into `F` is needed.
3. Apply `lem-kun-transcendence-degree-tower` to `k₀ ⊆ F ⊆ E`. Algebraicity of `E/F`
   makes its relative transcendence degree zero, giving the first equality. Apply it
   again to `k₀ ⊆ k ⊆ E`; separability implies algebraicity of `k/k₀`, giving the
   second equality. Lift cardinals to a common universe; no infinite-cardinal
   cancellation, finite generation, or finite-degree argument is used.
-/
theorem geometric_subfield_scalar_restriction
    (k₀ : Type u) (k : Type v) (E : Type w) (F : Type x)
    [Field k₀] [Field k] [Field E] [Field F]
    [Algebra k₀ k] [Algebra k E] [Algebra k₀ E]
    [Algebra k₀ F] [Algebra F E]
    [IsScalarTower k₀ k E] [IsScalarTower k₀ F E]
    [Algebra.IsSeparable k₀ k] [Algebra.IsAlgebraic F E]
    (hgeom : ∀ (K : Type (max u v w x t)) [Field K] [Algebra k K],
      IsReduced (E ⊗[k] K)) :
    (∀ (L : Type (max u v w x t)) [Field L] [Algebra k₀ L],
      IsReduced (E ⊗[k₀] L) ∧ IsReduced (F ⊗[k₀] L)) ∧
      Cardinal.lift.{w} (Algebra.trdeg k₀ F) =
        Cardinal.lift.{x} (Algebra.trdeg k₀ E) ∧
      Algebra.trdeg k₀ E = Algebra.trdeg k E := by
  sorry

end Algebra
