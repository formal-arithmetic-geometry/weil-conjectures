/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Mathlib.AlgebraicGeometry.Limits

/-! # Quasi-compact and quasi-separated permanence for algebraic stacks

Source: Stacks Project, stacks-morphisms.tex, Tag 075S(2),
lemma-quasi-compact-quasi-separated-permanence; Tag 04YW(4), definition-separated
(blueprint: lem-sfb-algebraic-stack-qcqs-permanence).

Absolute quasi-separatedness uses the structural map after composing the given
projection with `Over.map` along `S → Spec (ULift ℤ)`. Thus both diagonals are
absolute, even when the original base scheme is not quasi-separated.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry

namespace CategoryTheory

/-- A morphism from a quasi-compact, absolutely quasi-separated algebraic stack
into an absolutely quasi-separated algebraic stack is quasi-compact and quasi-separated.
Source: Stacks Project, stacks-morphisms.tex, Tags 075S(2) and 04YW(4)
(blueprint: lem-sfb-algebraic-stack-qcqs-permanence).

Proof:
1. By lem-sfb-algebraic-stack-change-base-to-integers, view both stacks over Spec Z.
The composite projections written below are precisely this change of base.
By lem-sfb-stack-quasicompact-absolute-criterion the source structure morphism is
quasi-compact. Its quasi-separatedness and the qcqs of the target's diagonal are
exactly the hypotheses. Apply lem-sfb-representable-stack-quasicompact-tests to
the target diagonal to regard it as a quasi-compact stack morphism.
2. By lem-sfb-algebraic-stack-fibre-products, form X × Y over Spec Z. Factor f
through its graph and the second projection. The graph is the base change of the
target diagonal: the relevant fibre-product objects are (x,y,α:f(x)≅y), each
isomorphic to (x,f(x),id), and its arrows are determined by the arrow of x.
The second projection is a base change of the source structure morphism.
Base change and composition preserve quasi-compactness directly by the tests of
def-sfb-stack-qcqs-morphism, so f is quasi-compact.
3. Apply lem-sfb-stack-quasiseparated-cancellation to f followed by the target
structure morphism. The composite is quasi-separated, as is the target diagonal,
so f is quasi-separated. Part (3) of lem-sfb-algebraic-stack-change-base-to-integers
transports both properties back to S. No representability of f is used. -/
theorem algebraicStack_qcqs_permanence {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) (hX : IsAlgebraicModuliStack X) (hY : IsAlgebraicModuliStack Y)
    (hXqc : IsQuasiCompactModuli X)
    (hXqs : IsQuasiSeparatedAlgebraicModuliMap
      (moduliBaseStructure
        (BasedCategory.ofFunctor (X.p ⋙ Over.map (specULiftZIsTerminal.from S)))))
    (hYqs : IsQuasiSeparatedAlgebraicModuliMap
      (moduliBaseStructure
        (BasedCategory.ofFunctor (Y.p ⋙ Over.map (specULiftZIsTerminal.from S))))) :
    IsQuasiCompactAlgebraicModuliMap.{u, v₁, w₁, v₂, w₂, v₃, w₃} f ∧
      IsQuasiSeparatedAlgebraicModuliMap f := by
  sorry

end CategoryTheory
