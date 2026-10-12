/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion

/-! # Lower truncation of universally connective affine flat complexes -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Canonical lower truncation retains finite presentation and flatness when
negative homology vanishes universally. It preserves nonnegative homology after
any base change. This statement has no proper morphism or coefficient sheaf.
Source: Stacks Project, Tags 0653 and 0654 (flat opcycles and lower truncation).
(blueprint: lem-pc-affine-flat-connective-truncation).

Proof: Write S = Spec A and pass to global sections using the affine
quasi-coherent equivalence. The terms of C become finitely presented flat, hence
finite projective, A-modules. Let P be their complex. For an arbitrary A-module N,
base change to the square-zero A-algebra A ⊕ N. The tensor complex is the direct
sum of P and P tensor N. Universal negative vanishing therefore makes P tensor N
exact in degree -1. The flat-opcycle criterion of Tag 0653 gives flatness of
coker(d : P^(-1) -> P^0). This cokernel is finitely presented as the cokernel of a
map between finitely presented modules. Sheafification identifies it with the
zeroth term of C.truncGE 0. Terms above zero are unchanged and terms below zero
are zero, proving all three termwise assertions. For any g, pullback is right
exact and identifies the degree-zero term with the cokernel of the pulled-back
differential. Thus g*(C.truncGE 0) is the canonical lower truncation of g*C up to
a canonical complex isomorphism. The truncation projection induces isomorphisms
on homology in degrees q >= 0 (in degree zero both are ker(d^0)/im(d^(-1))).
Taking the inverse yields the displayed isomorphisms. This is global even for
nonaffine S', since cokernels and these computations are sheaf-local. Empty S,
b = 0 and C = 0 require no nontriviality assumption. -/
theorem affine_flat_connective_truncation (S : Scheme.{u}) (hS : IsAffine S)
    (C : CochainComplex S.Modules ℤ) (a : ℤ) (b : ℕ)
    (hCge : C.IsStrictlyGE a) (hCle : C.IsStrictlyLE b)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 S))
    (hCqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (hCfp : ∀ n : ℤ, (C.X n).IsFinitePresentation)
    (hneg : ∀ {S' : Scheme.{u}} (g : S' ⟶ S) (i : ℤ), i < 0 →
      IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology i)) :
    (∀ n : ℤ, ((C.truncGE 0).X n).IsFlatOver (𝟙 S)) ∧
    (∀ n : ℤ, ((C.truncGE 0).X n).IsQuasicoherent) ∧
    (∀ n : ℤ, ((C.truncGE 0).X n).IsFinitePresentation) ∧
    ∀ {S' : Scheme.{u}} (g : S' ⟶ S) (q : ℕ),
      Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj
          (C.truncGE 0)).homology q ≅
        (((Modules.pullback g).mapHomologicalComplex _).obj C).homology q) := by sorry

end AlgebraicGeometry.Scheme.Modules
