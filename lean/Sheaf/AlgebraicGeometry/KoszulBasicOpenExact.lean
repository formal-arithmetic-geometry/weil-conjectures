/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Paper.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Local exactness of the sheafified Koszul complex

Source: Stacks Project, More on Algebra, Tag 0663.
(blueprint: lem-r4-koszul-basic-open-exact).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- The sheafified Koszul complex is exact on each generator's basic open.
Source: Stacks Project, More on Algebra, Tag 0663 (lemma-homotopy-koszul),
and Derived Categories of Schemes, Tag 09IR (lemma-orthogonal-koszul-complex).
(blueprint: lem-r4-koszul-basic-open-exact).

Proof: Write e_i for the i-th standard basis vector. Exterior multiplication
by e_i is a homotopy between multiplication by f_i and zero: contraction
satisfies d(e_i wedge x) + e_i wedge d(x) = f_i x. On D(f_i), f_i is a unit
in the structure sheaf. Multiply this homotopy by its inverse to obtain a
homotopy from the identity to zero. Sheafification sends the exterior-power
maps and their homotopy identity to module-sheaf maps; restriction preserves
that identity. Extension to cochain degrees -q preserves the identity and
puts zero objects in the remaining degrees. Therefore every homology sheaf
vanishes, which is exactness in each degree. No regular-sequence hypothesis
is needed. An empty basic open has only zero module sheaves, and r=0 gives
no index i, so the assertion is vacuous in that case. -/
theorem koszul_basicOpen_exact
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (i : Fin r) (n : ℤ) :
    (((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)
      (PrimeSpectrum.basicOpen (f i))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        _ _ _ _ (tilde.functor (.of A))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A r f).extend
          ComplexShape.embeddingDownNat))).ExactAt n := by sorry

end AlgebraicGeometry
