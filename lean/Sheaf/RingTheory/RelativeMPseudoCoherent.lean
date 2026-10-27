/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.RingTheory.MPseudoCoherent
public import Sheaf.AlgebraicGeometry.RingDerivedScalarExtension

/-! # Relative degreewise pseudo-coherence over a finite type algebra

Source: Stacks Project, More on Algebra, Tag 065I, definition-relatively-pseudo-coherent,
clause (1), using Tag 065H, lemma-relatively-pseudo-coherent, condition (1)
(blueprint: def-sfb-ring-relative-m-pseudocoherent).
-/

@[expose] public section

set_option autoImplicit false

universe u wA wP

open CategoryTheory

namespace DerivedCategory

/-- Relative `m`-pseudo-coherence means `m`-pseudo-coherence after restriction along
some surjective finite polynomial presentation over the base ring. The derived restriction
is induced by ordinary restriction on modules: it keeps additive groups and differentials,
and a polynomial acts through its image under the presentation. This module functor is
additive and exact, hence induces the functor on derived categories termwise.

Source: Stacks Project, More on Algebra, Tag 065I, definition-relatively-pseudo-coherent,
clause (1), using Tag 065H, lemma-relatively-pseudo-coherent, condition (1)
(blueprint: def-sfb-ring-relative-m-pseudocoherent). -/
def IsMPseudoCoherentRelativeTo (R : Type u) {A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{wP} (ModuleCat.{u} (MvPolynomial (Fin n) R))]
    (m : ℤ) (M : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
    Function.Surjective α ∧
      IsMPseudoCoherent m
        ((RingDerivedScalarExtension.moduleDerivedRestriction α.toRingHom).obj M)

end DerivedCategory
