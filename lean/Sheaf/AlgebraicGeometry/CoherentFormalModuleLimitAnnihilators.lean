/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Ideal.Operations
public import Sheaf.AlgebraicGeometry.CoherentFormalModule

import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness

/-! # Annihilators of affine limits of formal kernels and cokernels -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The affine-limit description of a formal kernel and cokernel preserves their
annihilator ideals over the ring of sections. This statement has no auxiliary ideal,
exponent, or covering hypothesis.

Source: Stacks Project, Lemma 087W and the affine calculation in Lemma 087X
(blueprint: lem-weil-pbc-formal-kernel-cokernel-limit-annihilators).

Proof: Restrict the limiting fork and colimiting cofork to V. Exact restriction
(Lemma 087X (2)) preserves their universal properties. Identify V with the spectrum
of its section ring A and apply Lemma 087W: the restricted category is equivalent
to finite modules over the I(V)-adic completion of A, with underlying A-module the
inverse limit of affine sections, naturally on morphisms. Equivalences preserve
kernels and cokernels. Finite modules over this Noetherian completed ring are closed
under both operations, and restriction of scalars preserves kernels and cokernels.
The resulting A-linear isomorphisms identify the limit of k with the linear kernel
of the limit map and the limit of c with the quotient by its range. Annihilator
ideals are invariant under linear equivalence (LinearEquiv.annihilator_eq), giving
the two equalities. This uses the formal kernel, not a termwise kernel. For an empty
V all section modules are zero and both annihilators are the unit ideal. -/
theorem coherentFormalModule_limit_annihilators
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    (F G : CoherentFormalModule X I) (α : F ⟶ G)
    (k : KernelFork α) (c : CokernelCofork α) (hk : IsLimit k) (hc : IsColimit c)
    (V : X.affineOpens) :
    Module.annihilator Γ(X, V.1)
      (limit (k.pt.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)) :
        ModuleCat Γ(X, V.1)) =
      Module.annihilator Γ(X, V.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op V.1)))).hom) ∧
    Module.annihilator Γ(X, V.1)
      (limit (c.pt.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)) :
        ModuleCat Γ(X, V.1)) =
      Module.annihilator Γ(X, V.1)
        (↥(limit (G.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)) :
          ModuleCat Γ(X, V.1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation X.ringCatSheaf (op V.1)))).hom) := by sorry

end AlgebraicGeometry
