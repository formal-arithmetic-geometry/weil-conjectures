/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.RingTheory.MinimalFreeModel
import Sheaf.Algebra.Homology.FreeComplexResidueDegreeCancellation
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Finite free residue-rank models near a prime

Source: Stacks Project, More on Algebra, Tags 0BYP, 0BCC, and 0BCD
(blueprint: lem-sfb-bounded-pseudocoherent-residue-model).
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A bounded-below pseudo-coherent object admits, near a prime, a bounded finite free
model whose ranks are its derived residue cohomology dimensions. The representative
`Classical.choose hK` is bounded above and finite free by `IsPseudoCoherent`; hence
termwise scalar extension computes both derived tensors in the statement.
Source: Stacks Project, More on Algebra, Tag 0BYP, with Tags 0BCC and 0BCD
(blueprint: lem-sfb-bounded-pseudocoherent-residue-model).

Proof:
1. Choose the bounded-above finite-free representative P, with upper bound u. Its
   residue cohomology is finite dimensional, being a subquotient of a finite dimensional
   term, and vanishes above u. Choose c from boundedness below and set t = min(a,c)-1.
   Then the residue cohomology in degree t and the original cohomology in degrees <= t vanish.
2. Apply lem-weil-pbc-free-complex-residue-degree-cancellation in degree t. After inverting
   s outside p, obtain a homotopy equivalent finite-free Q with Q^t = 0 and unchanged zero
   terms above max(u,t). Split Q as A plus B, in degrees < t and > t respectively.
3. By lem-weil-pbc-localization-module-exact, Q has zero cohomology in degrees <= t.
   Thus A is acyclic and projection to the bounded finite-free B is a quasi-isomorphism.
4. Tensor the original homotopy equivalence with the residue field. The homotopy equations
   persist. Above t the residue cohomology is that of B; at and below t both B and the
   prescribed residue cohomology vanish. Thus B has the original residue Betti numbers.
5. At p, apply lem-sc-perfect-local-pseudocoherent-free-model to B. Its minimal model M
   has ranks d_i, zero below a and above u. Transport to standard free terms and take
   b = max(a,u), so the support lies in [a,b], including when all ranks vanish.
6. Use lem-pc-ring-derived-map-representative to represent the derived comparison between
   M and B_p and its inverse by chain maps, with both inverse identities up to homotopy.
   All differentials, comparison maps and homotopies are finitely many finite matrices.
7. Clear their denominators outside p. For each error entry in the complex, chain-map and
   two homotopy identities, choose an annihilator outside p by the localization equality
   criterion. Invert their product as well. All equations then hold over one R_f.
8. The descended matrices define F with the claimed terms and a homotopy equivalence to
   B localized at f. Exact localization preserves the earlier quasi-isomorphism to B.
   Combining it with the localized homotopy equivalences yields the displayed derived
   isomorphism. Empty products are 1; zero modules and zero ranks are retained. -/
theorem exists_bounded_finiteFree_residue_model
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [∀ f : R, HasDerivedCategory.{w'} (ModuleCat.{max u v} (Localization.Away f))]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (hbelow : ∃ c : ℤ, ∀ i : ℤ, i < c →
      IsZero ((homologyFunctor (ModuleCat.{max u v} R) i).obj K))
    (a : ℤ)
    (hresidue : ∀ i : ℤ, i < a → IsZero
      (((Functor.mapHomologicalComplex (ModuleCat.extendScalars
        ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)))
          (ComplexShape.up ℤ)).obj (Classical.choose hK)).homology i)) :
    (∀ i : ℤ, Module.Finite (FractionRing (R ⧸ p))
      (((Functor.mapHomologicalComplex (ModuleCat.extendScalars
        ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)))
          (ComplexShape.up ℤ)).obj (Classical.choose hK)).homology i)) ∧
    ∃ f : R, f ∉ p ∧ ∃ b : ℤ, a ≤ b ∧
      ∃ F : CochainComplex (ModuleCat.{max u v} (Localization.Away f)) ℤ,
        (∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i)) ∧
        (∀ i : ℤ, a ≤ i → i ≤ b → Nonempty (F.X i ≅
          ModuleCat.of (Localization.Away f) (ULift.{v}
            (Fin (Module.finrank (FractionRing (R ⧸ p))
              (((Functor.mapHomologicalComplex (ModuleCat.extendScalars
                ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)))
                  (ComplexShape.up ℤ)).obj (Classical.choose hK)).homology i)) →
                    Localization.Away f)))) ∧
        Nonempty (Q.obj F ≅ Q.obj
          ((Functor.mapHomologicalComplex (ModuleCat.extendScalars
            (algebraMap R (Localization.Away f))) (ComplexShape.up ℤ)).obj
              (Classical.choose hK))) := by
  sorry

end DerivedCategory
