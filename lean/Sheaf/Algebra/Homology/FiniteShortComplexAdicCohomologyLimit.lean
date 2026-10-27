/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.Algebra.Homology.AdicShortComplexCohomologyML
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Filtration

/-! # Completed cohomology of a finite short complex

Source: Stacks Project, Tag 0EGU, assertion (2) and its canonical cycle maps.
(blueprint: lem-sfb-finite-short-complex-adic-cohomology-limit).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AdicCohomology

/-- The compatible-sequence limit of quotient cohomology is canonically the completion of
cohomology. The component formula specifies the map on every completed element by choosing
any representative of its residue in H/I^(n+1)H; it therefore specifies the actual canonical
comparison, not merely an abstract isomorphism. The second clause is naturality for every
morphism of short complexes, written on each coordinate of the compatible sequence.

Source: Stacks Project, Tag 0EGU, assertion (2), with its preceding canonical maps.
(blueprint: lem-sfb-finite-short-complex-adic-cohomology-limit).

Proof: Write Z = ker(v), B = im(u), and P_n = v⁻¹(I^n W). Lifting representatives identifies
H_n with P_n/(B + I^n V), and H/I^n H with Z/(B + I^n Z). Inclusion defines the comparison
maps and commutes with transitions. Apply lem-weil-pbc-artin-rees to v(V) in W and Z in V,
obtaining constants a,b; put c = a+b+1. For n at least c, write y in P_n as z+w with z in Z
and w in I^(n-a)V. Map the class of y to the class of z in H/I^(n-c)H. If choices differ,
z'-z-ut lies in Z ∩ I^(n-a)V, hence in I^(n-a-b)Z, so this map is well defined and linear.
The same representative works under transitions. Its composites with the cycle comparison
are the quotient transitions: one uses w=0 on a genuine cycle, and the other uses
w in I^(n-a)V ⊆ I^(n-c)V. On a compatible sequence x define the inverse at coordinate k
by applying this shifted map to x_(k+c). The two composite identities give inverse maps on
compatible sequences. Finally a commuting triple sends cycles, boundaries, and ideal powers
to their counterparts. Both routes around each finite-level comparison square send z to
the class of its middle-component image. This proves naturality coordinate by coordinate,
and then naturality of the inverse follows by composing with the two inverses. -/
theorem finite_short_complex_adic_cohomology_limit
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    ∃ e : ∀ (S : ShortComplex (ModuleCat.{u} R)),
      Module.Finite R S.X₁ → Module.Finite R S.X₂ → Module.Finite R S.X₃ →
      AdicCompletion I S.homology ≃ₗ[R] ↥(ModuleCat.sectionsSubmodule (tower I S)),
      ∀ (S : ShortComplex (ModuleCat.{u} R))
        (h₁ : Module.Finite R S.X₁) (h₂ : Module.Finite R S.X₂)
        (h₃ : Module.Finite R S.X₃),
        (∀ (x : AdicCompletion I S.homology) (n : ℕ) (h : S.homology),
          AdicCompletion.eval I S.homology (n + 1) x =
            (power I S.homology (n + 1)).mkQ h →
          (e S h₁ h₂ h₃ x).val (op n) =
            ShortComplex.homologyMap (S.mapNatTrans (projection I (n + 1))) h) ∧
        ∀ (T : ShortComplex (ModuleCat.{u} R))
          (k₁ : Module.Finite R T.X₁) (k₂ : Module.Finite R T.X₂)
          (k₃ : Module.Finite R T.X₃) (f : S ⟶ T)
          (x : AdicCompletion I S.homology) (n : ℕ),
          ShortComplex.homologyMap ((quotient I (n + 1)).mapShortComplex.map f)
              ((e S h₁ h₂ h₃ x).val (op n)) =
            (e T k₁ k₂ k₃ (AdicCompletion.map I (ShortComplex.homologyMap f).hom x)).val
              (op n) := by
  sorry

end AdicCohomology
