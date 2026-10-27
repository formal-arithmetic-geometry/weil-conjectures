/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.SchemeActionTorsorGroupoids
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-! # The scalar quotient description of a projective linear group scheme

Source: Milne, Algebraic Groups (2017), Example 5.49, printed p.111;
Stacks, examples-stacks.tex, Tag 04WM
(blueprint: def-sfb-projective-linear-quotient).

The matrix quotient is Mathlib's existing group. Injectivity and local surjectivity
characterize its fppf sheafification, without requiring global matrix lifts.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- A group scheme represents the fppf sheafification of `GL_r / scalar units`.
The quotient presheaf embeds in its functor of points and every section lies locally
in its image. The natural maps preserve multiplication.
Source: Milne, Example 5.49 (blueprint: def-sfb-projective-linear-quotient). -/
def IsProjectiveLinearQuotient (k : Type u) [Field k] (r : ℕ)
    (G : Over (Spec (.of k))) [GrpObj G] : Prop :=
  ∃ q : ∀ T : Over (Spec (.of k)),
      Matrix.ProjGenLinGroup (Fin r) Γ(T.left, ⊤) →* (T ⟶ G),
    (∀ T, Function.Injective (q T)) ∧
    (∀ (T W : Over (Spec (.of k))) (h : W ⟶ T)
        (g : Matrix.ProjGenLinGroup (Fin r) Γ(T.left, ⊤)),
      q W (Matrix.ProjGenLinGroup.map h.left.appTop.hom g) = h ≫ q T g) ∧
    ∀ (T : Over (Spec (.of k))) (x : T ⟶ G),
      ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over (Spec (.of k))) T ∧
        ∀ (W : Over (Spec (.of k))) (h : W ⟶ T), R h →
          ∃ g : Matrix.ProjGenLinGroup (Fin r) Γ(W.left, ⊤), q W g = h ≫ x

end AlgebraicGeometry
