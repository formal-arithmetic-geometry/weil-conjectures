/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.Topology.RingedSpaceModuleCohomology

/-! # Uniform vanishing for kernels of coherent formal systems

Source: Stacks Project, Cohomology of Schemes, Lemma 0884 (lemma-vanishing-projective)
(blueprint: lem-weil-pbc-vanishing-projective).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- For a coherent formal system over a proper Noetherian base, an ample twist kills
first cohomology of every successive kernel with a single bound. The index `op k`
represents F_(k+1). The zero case uses ker(F_1 → 0) ≅ F_1. Tensor exponents are natural
numbers, as in the node's d-fold tensor product; the bound is an integer.
Source: Stacks Project, Cohomology of Schemes, Lemma 0884
(blueprint: lem-weil-pbc-vanishing-projective).

Proof:
1. Properness makes X Noetherian over Spec A
   (lem-weil-pbc-finite-type-over-noetherian); comap gives the quasi-coherent ideal I O_X
   (def-nagata-extended-ideal, lem-weil-pbc-module-pullback-ideal-quotient).
2. The graded algebra B = direct sum I^n/I^(n+1) is finitely generated over A:
   choose finite generators of I by def-weil-pbc-noetherian-ring; their degree-one
   classes generate B.
3. There is a surjection from f^* tilde B onto direct sum (I O_X)^n/(I O_X)^(n+1).
   On an affine open with coordinate ring C it sends a tensor c to c f-sharp(a).
   Local generators show surjectivity; multiplication shows it is a graded algebra map
   (lem-weil-pbc-associated-module-hom, def-pc-module-pullback,
   lem-weil-pbc-module-pullback-affine-sections). Only a surjection is needed, not the
   equality printed in the Stacks proof.
4. The direct sum G of the successive kernels is a finite type graded module over
   that quotient algebra (lem-weil-pbc-formal-systems-kernel-rees-finite), hence also
   over f^* tilde B by the surjection.
5. Apply lem-weil-pbc-formal-systems-graded-vanishing (Stacks 0897 (2)) to G and the
   ample invertible module to obtain one bound for H^1(X, G tensor L^d).
6. Each kernel is a direct summand of G. Tensoring and then applying the functor
   RingedSpace.moduleCohomology preserves this retraction, so its first cohomology
   is a retract of zero and therefore zero. This includes the kernel of F_1 to zero. -/
theorem coherentFormalModule_kernel_twist_vanishing
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (L : X.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple X L)
    (F : @CoherentFormalModule X (isNoetherian_of_locallyOfFiniteType f)
      ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)) :
    ∃ d₀ : ℤ, ∀ (n d : ℕ), d₀ ≤ (d : ℤ) →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
        (Scheme.Modules.tensorObj (match n with
          | 0 => F.obj.obj (op 0)
          | k + 1 => kernel (F.obj.map (homOfLE (Nat.le_succ k)).op)) (L.tensorPow d))) := by
  sorry

end AlgebraicGeometry
