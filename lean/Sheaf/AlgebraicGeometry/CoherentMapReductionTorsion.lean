/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated

/-! # Torsion bounds for reductions of coherent maps

Source: Stacks Project, Remark 0888.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Reduction by any positive ideal power doubles an actual kernel/cokernel bound.
Source: Stacks Project, Remark 0888, commutative algebra fact
(blueprint: lem-weil-pbc-coherent-map-reduction-torsion).

Proof: restrict to an affine open Spec A. Coherence on a Noetherian scheme identifies
both sheaves with finite A-modules, and affine sections compute the kernel, cokernel,
ideal products and quotients. If K^t kills the kernel and cokernel of u, the canonical
scalar quasi-inverses for products of two elements of K^t show that K^(2t) kills the
kernel and cokernel of u modulo any ideal J. Apply
LinearMap.ker_coker_reduction_annihilated_double with J = I^(n+1).
The quotient projections identify this reduced map with formalModuleQuotientMap.
Vanishing of the ideal products is checked on affine sections, so these affine bounds
give the two global IsZero statements, with the same exponent 2t on every open.
-/
theorem coherentMap_reduction_torsion
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (F H : CoherentModules X) (a : F ⟶ H) (t : ℕ) (ht : 1 ≤ t)
    (hker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
      (kernel a.hom)))
    (hcoker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
      (cokernel a.hom))) :
    ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (kernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (cokernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))))) := by sorry

end AlgebraicGeometry
