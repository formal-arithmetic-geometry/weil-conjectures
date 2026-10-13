/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Ideal.Operations
public import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # Annihilation of formal kernels and cokernels on an affine cover

Source: Stacks Project, Lemmas 087W and 087X, and Remark 0888.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On any affine open cover, a fixed positive power kills a formal kernel and cokernel
exactly when its section ideals kill the kernels and cokernels of the affine limit maps.
Source: Stacks Project, Lemmas 087W and 087X (the affine description of the kernel)
(blueprint: lem-weil-pbc-formal-annihilation-kernel-cokernel-cover).

Proof:
1. Exact restriction to each open preserves the given limiting fork and colimiting
   cofork. The affine equivalence identifies their objects with the finite completed
   kernel T and cokernel Q of the affine inverse-limit map.
2. Under that equivalence their level n+1 objects are the tilde sheaves of
   T/I^(n+1)T and Q/I^(n+1)Q. The ideal-product section criterion identifies vanishing
   of the K^t-products with annihilation of these quotients by K(U)^t.
3. If K(U)^t kills T and Q, it kills every such quotient. Conversely, if it kills all
   quotients, every scalar product lies in the intersection of all I^(n+1)-powers
   of T or Q. Those intersections are zero: finite modules over the Noetherian
   completed ring are adically complete and separated. Thus it kills T and Q.
4. Vanishing of these quasi-coherent ideal-product sheaves is local on the supplied
   cover. Apply step 3 on each member and glue, retaining the same exponent t.
In particular the formal kernel is not asserted to be the termwise kernel.
For an empty index type covering X, X is empty and both sides hold. -/
theorem coherentFormalModule_annihilated_formal_cover
    (X : Scheme.{u}) [IsNoetherian X] (I K : X.IdealSheafData)
    (F G : CoherentFormalModule X I) (α : F ⟶ G)
    (k : KernelFork α) (c : CokernelCofork α) (hk : IsLimit k) (hc : IsColimit c)
    (J : Type v) (U : J → X.affineOpens) (hcover : (⨆ j, (U j).1) = ⊤)
    (t : ℕ) (ht : 1 ≤ t) :
    (∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (k.pt.obj.obj (op n))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (c.pt.obj.obj (op n)))) ↔
    (∀ j : J,
      K.ideal (U j) ^ t ≤ Module.annihilator Γ(X, (U j).1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U j).1)))).hom) ∧
      K.ideal (U j) ^ t ≤ Module.annihilator Γ(X, (U j).1)
        (↥(limit (G.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op (U j).1)) :
          ModuleCat Γ(X, (U j).1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation X.ringCatSheaf (op (U j).1)))).hom)) := by sorry

end AlgebraicGeometry
