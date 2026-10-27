/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Algebra.Opposite
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.RingTheory.MPseudoCoherent
import WeilConjectures.RingTheory.ConePseudoCoherent
import WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Finite free resolutions over a finite free algebra

Source: Stacks Project, perfect.tex, Tag 0CSF, lemma-pseudo-coherent-over-algebra
(blueprint: lem-sfb-finite-free-algebra-pseudocoherent-resolution).

Right modules over the possibly noncommutative algebra `B` are left modules over `Bᵐᵒᵖ`.
Restriction uses the canonical central algebra map into this opposite ring.
-/

@[expose] public section

set_option autoImplicit false

universe u v t wA wB

open CategoryTheory

namespace DerivedCategory

/-- An object of the derived category of right modules over a finite free central algebra
has a bounded-above finite-free right-module representative if its restriction to the
commutative base is pseudo-coherent.

Source: Stacks Project, Tag 0CSF, lemma-pseudo-coherent-over-algebra
(blueprint: lem-sfb-finite-free-algebra-pseudocoherent-resolution).

Proof, following the accepted split:
1. Represent `M` by a right `B`-complex `K`. A bounded-above finite-free `A`-model of
   its restriction supplies an upper cohomology bound `b`. Starting with zero in degrees
   at least `b+1`, construct finite-free approximations supported in `[n,b]` whose maps
   to `K` are cohomology isomorphisms above `n` and surjective in degree `n`.
2. The cone of the stage-`n` map has zero cohomology in degrees at least `n`, by the
   long exact sequence (lem-sf-derived-homology-long-exact).
3. The approximation is bounded finite free over `A`, since `B` is finite free over `A`.
   Truncating the fixed base-ring model shows that the restriction of `K` is
   `(n-1)`-pseudo-coherent. Apply lem-sc-cone-pseudo-coherent with parameter `n-1`,
   then lem-sc-finite-cohomology: the cone's degree-`n-1` cohomology is finite over `A`.
4. Lift finitely many `A`-generators to cone cycles. They also generate as right
   `B`-modules. Map a finite-free right `B`-module to these cycles. Writing its two
   components as `(a,-d)`, the cycle equation supplies the new differential `d` and
   chain-map component `a`, leaving all higher terms fixed. Empty generators are allowed.
5. The new cone's degree-`n-1` cohomology is the previous group modulo these generators,
   hence zero; higher groups are unchanged. The long exact sequence gives precisely
   the next stage's cohomology isomorphisms and surjection.
6. Assemble the degreewise stationary terms, differentials and maps. Every relation
   already holds at a finite stage. In any fixed degree, the cohomology map is the
   isomorphism established at stage `n=j-1`; thus the resulting map is a
   quasi-isomorphism. The complex is zero above `b` and finite free in every degree,
   and its image under `Q` is isomorphic to `M`.
-/
theorem exists_finite_free_resolution_of_restrictScalars_pseudoCoherent
    (A : Type u) [CommRing A] (B : Type v) [Ring B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B]
    [HasDerivedCategory.{wA} (ModuleCat.{max u v t} A)]
    [HasDerivedCategory.{wB} (ModuleCat.{max u v t} Bᵐᵒᵖ)]
    (M : DerivedCategory (ModuleCat.{max u v t} Bᵐᵒᵖ))
    (hM : IsPseudoCoherent
      (((ModuleCat.restrictScalars (algebraMap A Bᵐᵒᵖ)).mapHomologicalComplexUpToQuasiIso
        (ComplexShape.up ℤ)).obj M)) :
    ∃ (F : CochainComplex (ModuleCat.{max u v t} Bᵐᵒᵖ) ℤ) (b : ℤ),
      F.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free Bᵐᵒᵖ (F.X i) ∧ Module.Finite Bᵐᵒᵖ (F.X i)) ∧
      Nonempty (Q.obj F ≅ M) := by
  sorry

end DerivedCategory
