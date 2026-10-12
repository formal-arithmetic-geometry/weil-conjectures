/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-!
# Ideal quotients of a finite free kernel

Source: Stacks Project, Tag 01XF, the coordinate-filtration paragraph of the proof
of Lemma 30.3.1 (blueprint: lem-pqf-finite-free-kernel-ideal-filtration).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A kernel inside a finite free module admits a finite chain starting at zero whose
successive quotients are quasi-coherent ideal sheaves. There is no cohomology hypothesis.

Source: Stacks Project, Tag 01XF, label lemma-quasi-compact-h1-zero-covering,
coordinate-filtration paragraph (blueprint: lem-pqf-finite-free-kernel-ideal-filtration).

Proof: Enumerate the finite index set by n coordinates. Let F_j, for j ≤ n, be the
kernel of p restricted to the first j summands. Extend the chain constantly after n.
The empty sum is zero, so F_0 is zero, and F_n is isomorphic to kernel p. The finite
free source and the structure sheaf are quasi-coherent, hence so is each F_j by
quasi-coherent kernel closure. Project F_(j+1) onto its last coordinate. Its kernel
is F_j, and its image is quasi-coherent by quasi-coherent image closure. On each
affine open the image is an ideal in the section ring. These ideals commute with
localization and define IdealSheafData J. The associated J.toModules is isomorphic
to that image: both inclusions into the structure sheaf have these same section
ranges on the affine basis. Transport the image factorization along this isomorphism.
The first isomorphism theorem gives the asserted short exact sequence. This uses
no surjectivity of p. For an empty index set choose n = 0 and the constant zero chain.
-/
theorem finite_free_kernel_ideal_filtration (X : Scheme.{u})
    {I : Type u} [Finite I]
    (p : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    ∃ (n : ℕ) (F : ℕ → X.Modules),
      IsZero (F 0) ∧ Nonempty (F n ≅ kernel p) ∧
      ∀ j : ℕ, j < n → ∃ J : X.IdealSheafData,
        J.toModules.IsQuasicoherent ∧
        ∃ (a : F j ⟶ F (j + 1)) (b : F (j + 1) ⟶ J.toModules)
          (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by sorry

end AlgebraicGeometry
