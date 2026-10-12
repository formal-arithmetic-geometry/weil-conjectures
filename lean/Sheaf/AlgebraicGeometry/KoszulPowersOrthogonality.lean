/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Paper.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Koszul orthogonality propagates to positive powers
Source: Stacks Project, Tag 09IR.
(blueprint: lem-pc-koszul-powers-orthogonality).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Orthogonality to every shift persists after raising the generators to positive powers.
Source: Stacks Project, Tag 09IR, proof of lemma-orthogonal-koszul-complex;
Tag 062C, lemma-koszul-mult.
(blueprint: lem-pc-koszul-powers-orthogonality).

Proof: Induct on the sum of the positive exponents minus r. The zero case has every
exponent equal to one, so it is the hypothesis. Otherwise select a coordinate with
exponent m+1, m positive, and use the Koszul multiplication triangle for f_i^m and
f_i, with all other entries fixed. Its two outer Koszul objects have smaller sums.
The long exact Hom sequence, in all integer shifts, makes the middle Hom group zero.
Tensoring the one-variable triangle with the remaining finite free Koszul factors,
then sheafifying and localizing, gives the required triangle for any coordinate.
The argument also applies to an empty tuple, zero ring, or zero generators. -/
theorem koszul_powers_orthogonal_of_orthogonal
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (E : schemeDerivedCategory (Spec (.of A)))
    (horth : ∀ n : ℤ, Subsingleton ((DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
            ((ExteriorAlgebra.koszulComplex A r f).extend
              ComplexShape.embeddingDownNat)))⟦n⟧ ⟶ E))
    (e : Fin r → ℕ) (he : ∀ i, 0 < e i) (n : ℤ) :
    Subsingleton ((DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
            ((ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ e i)).extend
              ComplexShape.embeddingDownNat)))⟦n⟧ ⟶ E) := by sorry

end AlgebraicGeometry
