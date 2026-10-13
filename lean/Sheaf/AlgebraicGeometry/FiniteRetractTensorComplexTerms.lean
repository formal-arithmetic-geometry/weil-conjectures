/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.KFlat

/-! # Terms of an ordinary bounded finite-projective tensor complex

Source: Stacks Project, Tags 0DJQ and 01Y0.
(blueprint: lem-pc-finite-retract-tensor-complex-terms).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

noncomputable local instance tensorComplexTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- The ordinary total tensor of a bounded finite-free-retract complex with a termwise
coherent complex has coherent terms, even if the second complex is unbounded.
Source: Stacks Project, perfect.tex, Tag 0DJQ, local tensor calculation;
coherent.tex, Tag 01Y0, label lemma-coherent-abelian-Noetherian.
(blueprint: lem-pc-finite-retract-tensor-complex-terms).

Proof: In total degree n the summands are P^p tensor N^q for p+q=n.
The bounds of P make a summand zero unless a<=p<=b.
For each such p the equation determines q=n-p, so there are finitely many pairs. Remove the
zero summands using the coproduct universal property. Every remaining summand
is a retract of (N^q)^{oplus m}, by tensoring the given retraction of P^p
from the rank-m free module and using distribution of tensor over finite sums.
Finite sums of coherent modules are coherent. A retract is coherent: it is the
kernel of 1 minus the idempotent given by the splitting, up to the canonical
isomorphism. Thus each total term is coherent. The argument includes zero ranks,
reversed bounds for P, empty schemes and the zero complex; it imposes no bounds on N.
It involves no homology, derived localization,
restriction functor or choice of local model. -/
theorem finiteRetract_tensorComplex_coherent_terms
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a b : ℤ)
    (hPbounds : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hPfree : ∀ n : ℤ, ∃ m : ℕ,
      ∃ (ι : P.X n ⟶ SheafOfModules.free
          (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin m)) ⟶ P.X n),
        ι ≫ π = 𝟙 (P.X n))
    (hNcoherent : ∀ n : ℤ, RingedSpace.IsCoherent X.toRingedSpace (N.X n)) :
    ∀ i : ℤ, RingedSpace.IsCoherent X.toRingedSpace
        ((CochainComplex.mapBifunctor P N (curriedTensor _)).X i) := by sorry

end AlgebraicGeometry.Scheme
