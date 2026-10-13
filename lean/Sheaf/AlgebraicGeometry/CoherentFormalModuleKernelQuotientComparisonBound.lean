/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModuleShiftedQuotient
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Filtration
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Artin--Rees bounds for stabilized kernel quotients

Source: Stacks Project, Lemma 087X.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Sufficiently large shifts give the successive quotient comparisons.

Source: Stacks Project, Lemma 087X, claims (b)--(c).
(blueprint: lem-weil-pbc-formal-kernel-quotient-comparison-bound).

Proof: Choose a finite affine open cover of the Noetherian scheme. On each affine,
the formal-module equivalence represents alpha by a map f of finite modules over
the Noetherian completed ring. Put L = ker f. Artin--Rees for im f shows that the
eventual kernel images are (L + I^(m+1) M)/I^(m+1) M. For each m, choose l
large enough for this image calculation and l >= m+c.
The hypothesis hc identifies this image with the image at m+c, and hS identifies
its inclusion with j_m.
Thus S_m is canonically L/(L intersect I^(m+1) M), with its induced transitions.
Artin--Rees for L in M supplies b with L intersect I^(r+b) M contained in I^r L.
Take the maximum of these bounds on the finite cover. For every d at least c and b,
the shifted quotient at n is L/(L intersect I^(n+d+1) M + I^(n+1) L), hence
L/I^(n+1) L. This identification respects the explicit quotient transition maps.
Reducing the term at n+1 by I^(n+1) therefore gives the term at n, with
the factorization equation in the conclusion. These local comparison maps agree
on overlaps: their composites with the quotient projection are the prescribed
transition, and that projection is epic. Glue the maps; each is locally an
isomorphism, so the glued map is an isomorphism. The argument also
covers I=0, I=O_X, zero modules, and the empty scheme (take the bound zero).
-/
theorem coherentFormalModule_kernel_quotient_comparison_bound {X : Scheme.{u}} [IsNoetherian X]
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
    ∃ b : ℕ, ∀ d : ℕ, max c b ≤ d →
      ∀ n : ℕ, ∃ e :
        formalModuleQuotient I (n + 1)
          ((formalShiftedQuotient I S d).obj (op (n + 1))) ≅
          (formalShiftedQuotient I S d).obj (op n),
        formalModuleQuotientπ I (n + 1)
            ((formalShiftedQuotient I S d).obj (op (n + 1))) ≫ e.hom =
          (formalShiftedQuotient I S d).map (homOfLE (Nat.le_succ n)).op := by
  sorry

end AlgebraicGeometry
