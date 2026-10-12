/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineQuotient
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.FiniteModuleComplete
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # CoherentFormalModulesAffineComplete

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Applying a completed-module limit functor to the canonical quotient system recovers
any finite completed module. This is the finite-module half of the equivalence.
Source: Stacks Project, Lemma 087W, implicit converse; Algebra 0316, 05GG and 00MA (3).
(blueprint: lem-weil-pbc-coherent-formal-modules-affine-complete).

Proof: Put B = completion and K = I B. The completion quotient formula identifies
B/K^(n+1) with A/I^(n+1), and makes B K-adically complete. B is Noetherian by 0316.
Every finite B-module N is K-adically complete by 00MA (3); K^m N and I^m N coincide
as A-submodules. The affine ideal-product/cokernel comparison identifies the sections
of Q(N) with N/I^(n+1)N, compatibly with their reductions. The canonical quotient
maps therefore make restricted N a limit cone on these sections. Compare this cone
with the assumed limit cone p(Q(N)) to obtain an A-linear isomorphism N -> L(Q(N)).
It is B-linear: for any completed scalar and any coordinate, choose an A representative
of its residue modulo I^(n+1). Both cone projections carry its action to multiplication
by that representative, by hscalar and the quotient description. Limit projections
jointly distinguish maps, so scalar compatibility at all coordinates proves B-linearity
for this isomorphism and its inverse. Naturality follows by testing on the same
projections, using hnatural and naturality of the quotient maps. These isomorphisms
in the full finite-module subcategory form the asserted natural isomorphism. -/
theorem coherentFormalModules_affine_complete (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (L : CoherentFormalModule (Spec (CommRingCat.of A)) J ⥤
    ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N))
    (p : ∀ F : CoherentFormalModule (Spec (CommRingCat.of A)) J,
      (Functor.const ℕᵒᵖ).obj
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
          (L.obj F).obj) ⟶ F.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A))
    (hlimit : (∀ F, Nonempty (IsLimit (Cone.mk _ (p F)))))
    (hnatural : (∀ (F G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (f : F ⟶ G)
      (n : ℕ),
      (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map
        (L.map f).hom ≫ (p G).app (op n) =
      (p F).app (op n) ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map (f.hom.app (op n))))
    (hscalar : (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ)
      (r : AdicCompletion I A) (a : A) (x : (L.obj F).obj),
      AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a →
      (p F).app (op n) (r • x) = a • (p F).app (op n) x)) :
    Nonempty ((coherentFormalModules_affine_quotientFunctor A I J hJ) ⋙ L ≅ 𝟭 _) := by
  sorry

end AlgebraicGeometry
