/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-!
# Filtered free complexes are K-projective

Source: Stacks Project, Differential Graded Algebra, Tag 09KM, lemma-property-P-K-projective.
(blueprint: lem-pc-filtered-free-kprojective).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- An exhaustive, degreewise split filtration with shifted free quotients is K-projective.
Source: Stacks Project, Tag 09KM, lemma-property-P-K-projective, specialized to the algebra
concentrated in degree zero; the larger carrier universe uses the rank-one module `ULift A`.
(blueprint: lem-pc-filtered-free-kprojective).

Proof: each shifted free module has no maps up to homotopy to an acyclic complex:
a chain map is determined by a cycle, and acyclicity writes that cycle as a boundary.
The same holds for a direct sum of these modules, by choosing a primitive on each
free generator. The degreewise split short exact sequences for the filtration give
mapping-cone triangles in the homotopy category. Induction from the zero initial
term therefore shows that every finite filtration term, and each of its shifts,
is left orthogonal to all acyclic complexes. Form the telescope sequence with first
map identity minus successor on the direct sum of the filtration terms. Exhaustion
identifies its cokernel with `P`. The degreewise retractions give a splitting of
this sequence of graded modules (successively compose retractions on each finite
stage), so it gives a distinguished triangle in the homotopy category. Maps from
both coproduct terms to an acyclic complex, including its shifts, are zero, since
maps from coproducts are families of maps. The exact Hom sequence of this triangle
makes every map from `P` to an acyclic complex zero in the homotopy category, hence
null homotopic. This is `IsKProjective`. All coproducts and choices of generators
stay in `Type (max u v)`. Empty free bases, zero rings and unbounded complexes are
included. -/
theorem isKProjective_of_filtered_free {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0)) (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hquot : ∀ n, ∃ (I : Type (max u v)) (degree : I → ℤ),
      Nonempty (cokernel (step n) ≅
        ∐ (fun i : I ↦
          (HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) (degree i)).obj
            (ModuleCat.of A (ULift.{v} A))))) :
    P.IsKProjective := by sorry

end CochainComplex
