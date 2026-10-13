/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Noetherian.Defs

/-! # Projective cohomology finiteness over an affine base

Source: Stacks Project, Tag 01YS, Lemma 30.14.1 (3).
(blueprint: lem-pc-m1-projective-affine-finite-cohomology-independent)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- Finiteness for an explicit projective model over an arbitrary affine Noetherian scheme.

Source: Stacks Project, Tag 01YS, Lemma 30.14.1 (3), and Tag 01Y6, Lemma 30.9.9.
(blueprint: lem-pc-m1-projective-affine-finite-cohomology-independent)

Proof: identify T with Spec Gamma(T,O) by its affine canonical isomorphism, and base
change the specified embedding along this isomorphism. Closed pushforward of F is
quasi-coherent and finitely presented on the Noetherian projective space, and has the
same cohomology. On projective space, the standard coordinate affine cover bounds the
cohomological degree. Descending induction on degree, simultaneously for all coherent
modules, uses a surjection from a finite sum of twists with coherent kernel. The twists
have finite cohomology by the explicit standard-cover calculation; the long exact
sequence and Noetherian submodule finiteness give finiteness for F. All comparisons
are natural under multiplication by sections of T, hence linear for the displayed
restriction-of-scalars action. If N is empty, Y is empty and all groups are zero.
No use is made of proper coherence. -/
theorem finite_H_projective_affine_independent
    {Y T : Scheme.{u}} [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (N : Type u) [Finite N] (j : Y ⟶ ℙ(N; T)) [IsClosedImmersion j]
    (F : Y.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (q : ℕ) :
    letI : Module Γ(T, ⊤) (F.H q) :=
      Module.compHom _ (j ≫ (ℙ(N; T) ↘ T)).appTop.hom
    Module.Finite Γ(T, ⊤) (F.H q) := by sorry

end AlgebraicGeometry.Scheme.Modules
