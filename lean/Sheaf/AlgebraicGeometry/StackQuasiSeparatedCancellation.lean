/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Quasi-separated cancellation for morphisms of algebraic stacks

Source: Stacks Project, stacks-morphisms.tex, Tag 050M(4),
lemma-compose-after-separated
(blueprint: lem-sfb-stack-quasiseparated-cancellation).

The hypothesis on the second relative diagonal is quasi-separatedness of its
algebraic-space scheme tests. It does not assert quasi-compactness of that diagonal.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry

namespace CategoryTheory

/-- If a composite of algebraic-stack morphisms is quasi-separated and the second
morphism has quasi-separated relative diagonal, the first morphism is quasi-separated.
Source: Stacks Project, stacks-morphisms.tex, Tag 050M(4),
lemma-compose-after-separated
(blueprint: lem-sfb-stack-quasiseparated-cancellation).

Proof:
1. Put P = A ×_B A and Q = A ×_C A, using
lem-sfb-algebraic-stack-fibre-products. The functor i : P → Q applies b to the
comparison isomorphism. The factorization Δ(ba) = i Δa is 2-cartesian over Δb:
a lift of (a(x₁),a(x₂),ψ) is an isomorphism φ with b(φ) = ψ; a presentation by
(y,u,v) gives φ = v⁻¹u, with inverse (a(x₂),φ,1). These constructions respect
arrows and pullbacks by def-sfb-stable-pointed-moduli-groupoids. The diagonals
and i are representable by lem-sfb-stack-relative-diagonal-finite-type.
2. For a scheme test t : T → P, form E = A ×_Q T and F = P ×_Q T.
The projection v : F → T is a test of Δb, so it is quasi-separated by hΔb.
The composite E → F → T is a test of Δ(ba), hence quasi-compact and
quasi-separated by hab and def-sfb-stack-qcqs-morphism.
3. For u : E → F, the inclusion E ×_F E → E ×_T E pulls Δ(E/T) back to Δ(E/F):
both diagonals impose equality of the two E-sections. Thus u is quasi-separated,
by lem-sfb-space-quasicompact-affine-tests and def-trf-algebraic-space.
4. Apply lem-sfb-space-qc-cancellation to u followed by v to get u quasi-compact.
The atlas and topological conventions agree by lem-a1-space-etale-open-image;
lem-sfb-space-quasicompact-affine-tests transports affine tests to arbitrary
quasi-compact space tests using a quasi-compact scheme atlas. Composing the
etale surjective atlases uses lem-sfb-stack-chartwise-smooth-etale-calculus.
5. The original t gives a section T → F. Pulling E → F back along it gives
A ×_P T → T, by the triple formula of def-sfb-stable-pointed-moduli-groupoids.
Its quasi-compactness follows by base change, and its diagonal is the base change
of Δu, so is quasi-compact as well, by lem-sfb-space-quasicompact-affine-tests.
Since t was arbitrary, def-sfb-stack-qcqs-morphism gives the conclusion. -/
theorem algebraicStack_quasiSeparated_cancellation {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    {C : BasedCategory.{v₃, w₃} (Over S)}
    (a : BasedFunctor A B) (b : BasedFunctor B C)
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (hC : IsAlgebraicModuliStack C)
    (hab : IsQuasiSeparatedAlgebraicModuliMap (a.comp b))
    (hΔb : ∀ (T : Over S)
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) (moduliTwoFiberProduct b b)),
      ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange (moduliRelativeDiagonal b) T t Z p ∧
          AlgebraicSpace.MapIsQuasiSeparated p) :
    IsQuasiSeparatedAlgebraicModuliMap a := by
  sorry

end CategoryTheory
