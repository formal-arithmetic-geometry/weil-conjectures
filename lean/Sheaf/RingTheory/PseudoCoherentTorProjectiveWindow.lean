/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Module.Projective
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Algebra.Homology.FlatOpcyclesTorCriterion
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Finite projective representatives in a prescribed Tor interval

Source: Stacks Project, More on Algebra, Tag 0658 (lemma-perfect), final assertion
(blueprint: lem-trf-pseudo-coherent-tor-projective-window).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A pseudo-coherent object with Tor amplitude in `[a, b]` has a finite projective
representative supported in that same interval. Finite projective modules are precisely
summands of finite free modules. No Noetherian assumption is made.

Source: Stacks Project, More on Algebra, Tag 0658 (lemma-perfect), final assertion
(blueprint: lem-trf-pseudo-coherent-tor-projective-window).

Proof:
1. Take a K-flat representative K of C. Testing the amplitude with A in degree zero
   shows that the cohomology of C vanishes outside [a,b], since tensoring K with A[0]
   recovers K (def-pc-module-kflat-complex).
2. By lem-pc-pseudo-coherent-bounded-finite-free-model choose a finite free complex F
   with no terms above b and an isomorphism Q(F) ≅ C. Each free term is flat.
3. By lem-pc-module-bounded-flat-kflat, F is K-flat. The comparison in
   lem-pc-source-kflat-module-tensor-model identifies its tensor with every N[0]
   with C tensor-derived N[0], independently of the K-flat representative used.
   The amplitude gives zero homology in degree a-1. Thus
   lem-pc-module-flat-opcycles-tor-criterion makes M = F.opcycles a flat. The sequence
   F^(a-1) → F^a → M → 0 is a finite presentation (def-sc-finitely-presented-module).
4. By lem-weil-pbc-finitely-presented-flat-module-projective, M is finite projective.
   Projectivity splits its finite free presentation, so M is a summand of a finite
   free module (def-weil-pbc-projective-module).
5. Set P^i = 0 below a, P^a = M, and P^i = F^i above a, with the induced differential
   out of M. The quotient F → P induces an isomorphism on cohomology: below a both
   cohomologies vanish; in degree a its cycles are ker(d_F^a)/im(d_F^(a-1)); above a
   cycles and boundaries are unchanged, including degree a+1 because F^a → M is
   surjective. Hence Q(F → P) is invertible (def-weil-abstract-derived-category).
   Its inverse composed with Q(F) ≅ C gives Q(P) ≅ C. Since a ≤ b, P vanishes above b
   as well as below a. Its bottom term is finite projective, the higher terms are
   finite free, and its zero terms are summands of A^0. -/
theorem exists_finiteProjective_model_of_torAmplitudeIn
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (a b : ℤ) (hab : a ≤ b) (C : DerivedCategory (ModuleCat.{u} A))
    (hC : IsPseudoCoherent C) (hTor : torAmplitudeIn (ModuleCat.{u} A) a b C) :
    ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      (∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i)) ∧
      Nonempty (Q.obj P ≅ C) := by
  sorry

end DerivedCategory
