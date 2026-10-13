/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModuleShiftedQuotient
public import Mathlib.Algebra.Homology.ShortComplex.Exact

import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Filtration
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Eventual exactness of shifted kernel quotient transitions

Source: Stacks Project, Lemma 087X, proof of claims (a)--(c).
(blueprint: lem-weil-pbc-formal-kernel-quotient-transition-exact-bound).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The kernel of each sufficiently shifted quotient transition is its ideal product.

Source: Stacks Project, Lemma 087X, proof of claims (a)--(c).
(blueprint: lem-weil-pbc-formal-kernel-quotient-transition-exact-bound).

Proof: Restrict to a finite affine cover. The affine formal-module equivalence represents
alpha by a map f : M to N over the Noetherian completed ring. Put L = ker f.
Artin--Rees for im f in N gives a constant a such that
f inverse(I^t N) = L + I^(t-a) f inverse(I^a N) for t >= a.
For l >= m+a, its image modulo I^(m+1) M is therefore the image of L.
Choose l also >= m+c, and use hc to identify the image at m+c with this image.
Thus the eventual kernel image in level m is L/(L intersect I^(m+1) M).
The isomorphisms hS transport this
identification to S_m; the equations with j and its naturality identify the transitions
with the reductions of L. Artin--Rees for L in M supplies a bound b on each affine
with L intersect I^(r+b) M contained in I^r L. Take the maximum on the finite cover.
For d >= max(c,b), the level n shifted quotient is L/I^(n+1) L: the extra intersection
L intersect I^(n+d+1) M is contained in I^(n+1) L. Its transition from n+1 to n
is reduction, whose kernel is I^(n+1)L/I^(n+2)L, the ideal product of its source.
The affine ideal-product calculation transports this equality to the sheaves.
Exactness is local, giving the asserted short-complex exactness and zero composite.
For I=0 these transitions are identities; for I=O_X or zero modules all terms vanish.
The empty scheme admits bound zero. -/
theorem coherentFormalModule_kernel_quotient_transition_exact_bound
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ) (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj)
    (hc : ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op)))
    (hS : ∀ m : ℕ, ∃ e : S.obj (op m) ≅
      Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op),
      e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m)) :
    ∃ b : ℕ, ∀ d : ℕ, max c b ≤ d → ∀ n : ℕ,
      ∃ hz : Scheme.idealModuleProductι
          (Scheme.idealSheafPower I.toModulesι (n + 1)).2
          ((formalShiftedQuotient I S d).obj (op (n + 1))) ≫
          (formalShiftedQuotient I S d).map (homOfLE (Nat.le_succ n)).op = 0,
        (ShortComplex.mk
          (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (n + 1)).2
            ((formalShiftedQuotient I S d).obj (op (n + 1))))
          ((formalShiftedQuotient I S d).map (homOfLE (Nat.le_succ n)).op) hz).Exact := by
  sorry

end AlgebraicGeometry
