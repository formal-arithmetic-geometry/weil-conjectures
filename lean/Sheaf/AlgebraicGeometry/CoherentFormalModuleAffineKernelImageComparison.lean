/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Affine comparison of formal kernel images with module quotients

Source: Stacks Project, Lemma 087X, affine description of K'_(l,m), using Lemma 087W.
(blueprint: new-formal-affine-kernel-image-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On an affine open, comparison of any two finite-level kernel image subsheaves
is equivalent to comparison of the corresponding quotient submodules of a completed
module. There is no stabilization assertion or Artin--Rees bound in this statement.

Source: Stacks Project, Lemma 087X, description of K'_(l,m) before claim (a),
and Lemma 087W; Schemes, Tags 01IB and 01IC.
(blueprint: new-formal-affine-kernel-image-comparison).

Proof: Restrict F, H and alpha to U and identify U with Spec A for A = Gamma(U,O_X).
Restriction preserves the defining coherent formal object conditions. Apply 087W to
these systems and their morphism to obtain finite completed modules M, N and a linear
map f. Put J = I(U)R in the completed ring R. The level-n projections are surjective
and have kernels J^(n+1)M and J^(n+1)N. Hence sections of ker(alpha_l) lift precisely
to f inverse(J^(l+1)N), and transition to level m sends their lifts to their classes
modulo J^(m+1)M. Affine sections of the abelian image equal the ordinary linear image.
The tilde/global-sections equivalence identifies the image inclusion with the tilde
of this quotient submodule inclusion. Thus equal quotient submodules give equal
subsheaves on U, and consequently equal section ranges on every W contained in U.
Conversely equality of these ranges includes equality at W = U; the affine quotient
identification recovers equality of the two submodules. Restriction of scalars from
R to A preserves equality of underlying submodules. No finiteness or affine assumption
on W is used. On empty U, A and R are zero rings and both sides are the unique zero
submodule; zero and unit ideals give the same quotient computations. -/
theorem coherentFormalModule_affine_kernel_image_comparison
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (F H : CoherentFormalModule X I) (α : F ⟶ H) (U : X.affineOpens) :
    let A := Γ(X, U.1)
    let R := AdicCompletion (I.ideal U) A
    let J := (I.ideal U).map (algebraMap A R)
    ∃ (M N : ModuleCat.{u} R) (f : M ⟶ N),
      Module.Finite R M ∧ Module.Finite R N ∧
      ∀ (l k m : ℕ) (hl : m ≤ l) (hk : m ≤ k),
        (((J ^ (l + 1) • (⊤ : Submodule R N)).comap f.hom).map
            (J ^ (m + 1) • (⊤ : Submodule R M)).mkQ =
          ((J ^ (k + 1) • (⊤ : Submodule R N)).comap f.hom).map
            (J ^ (m + 1) • (⊤ : Submodule R M)).mkQ) ↔
        ∀ (W : X.Opens), W ≤ U.1 →
          Set.range ((Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE hl).op)).app W) =
          Set.range ((Abelian.image.ι (kernel.ι (α.hom.app (op k)) ≫
            F.obj.map (homOfLE hk).op)).app W) := by sorry

end AlgebraicGeometry
