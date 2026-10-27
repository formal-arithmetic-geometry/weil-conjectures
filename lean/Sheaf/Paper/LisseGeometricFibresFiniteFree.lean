/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.LisseQlbarRepresentationDefs

/-! # Finite free geometric fibres of lisse modules

Source: the representation theorem, Fibres paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj Opposite
open scoped TensorProduct CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.monoidal_upperStarFromPoint
namespace AlgebraicGeometry.ProEtale.LisseRepresentation

attribute [local irreducible] IntegralNormalization Compatibilities FiniteFreeFibre

/-- The actual geometric sections of a lisse module are finite free over its
coefficient ring, with the scalar action induced by the specified constant sections.
This assertion is local at the geometric point and needs no Noetherian or normality
hypothesis on the scheme.

Source: blueprint latest, thm-lisse-qlbar-representations.proof, step 3, Fibres
(blueprint: lem-sfb-lisse-geometric-fibres-finite-free).

Proof: inverse image along the geometric point preserves lisse modules. Choose a finite
free trivializing cover of this pullback and restrict its trivialization along a section
of a covering arrow, using separable closedness. This gives a finite free module globally
on the point. Evaluate its finite direct sum on the final object: finite sums of abelian
sheaves are finite products, so sections give the same finite power of the coefficient
ring. The condensed point coefficient comparison evaluated on the one-point profinite
set identifies that ring with the original scalar ring. Constants act by multiplication
under this identification, since the comparison is a ring-object comparison. Transport
this action and the chosen finite basis across the global trivialization to obtain V,
the additive isomorphism, and its scalar identity. Apply this argument to the integral,
finite-extension and finite-subextension-valued algebraic-closure coefficient rings.
The zero-rank trivialization gives the zero module by the same computation.
-/
theorem lisse_geometric_fibres_finite_free
    (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    (∀ E, FiniteFreeFibre (integers ell E)
      (Padic.coefficientExtensionIntegers ell E) (continuousConstants _) x) ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField ell,
      FiniteFreeFibre (Mon.mk (Profinite.continuousMapRingObj E)) E (continuousConstants E) x) ∧
    FiniteFreeFibre (Mon.mk (Profinite.padicAlgClRingObj ell)) (PadicAlgCl ell)
      (Profinite.PadicAlgCl.constRingHom ell) x := by sorry

end AlgebraicGeometry.ProEtale.LisseRepresentation
