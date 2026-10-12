/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.FiniteModuleComplete
import Mathlib.RingTheory.AdicCompletion.LocalRing

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The canonical cone from a module to the sections of its sheaf quotient system.
The maps are the tilde/global-sections unit followed by the actual quotient projections.
Source: Stacks Project, Tag 087W, implicit converse (blueprint:
def-weil-pbc-coherent-formal-modules-affine-quotient-cone). -/
noncomputable def coherentFormalModules_affine_quotientCone
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (N : ModuleCat.{u} (AdicCompletion I A)) :
    Cone ((formalCompletionFunctor J).obj
      ((tilde.functor (CommRingCat.of A)).obj
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N)) ⋙
      moduleSpecΓFunctor (R := CommRingCat.of A)) where
  pt := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N
  π :=
    { app := fun n ↦ (tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app _ ≫
        (moduleSpecΓFunctor (R := CommRingCat.of A)).map
          (formalModuleQuotientπ J (n.unop + 1) _)
      naturality := by
        intro n m f
        dsimp only [Functor.const, Functor.comp, formalCompletionFunctor,
          formalCompletionSystem]
        rw [Category.id_comp, Category.assoc, ← Functor.map_comp]
        congr 1
        simp [formalModuleQuotientπ, formalModuleQuotientMap] }

/-- The canonical quotient cone of a finite completed module is limiting, and its
projections use the residue of a completed scalar at their level. This assertion
concerns only the explicit quotient construction, not any candidate inverse functor.
Source: Stacks Project, Tag 087W, implicit converse; Algebra Tags 0316, 05GG, 00MA (3).
(blueprint: lem-weil-pbc-coherent-formal-modules-affine-quotient-cone).

Proof: Write B = AdicCompletion I A and K = I B. Since A is Noetherian, I is finitely
generated. The completion quotient formula identifies B/K^m with A/I^m for every
positive m, and B is K-adically complete and Noetherian (0316 and 05GG). The finite
B-module N is K-adically complete: 00MA (3) identifies its completion with
N tensor B-completion, hence with N itself. Restriction of scalars identifies
K^m N with I^m N: expand elements of the extended ideal as finite sums, and use
associativity of scalar multiplication; the reverse inclusion uses the algebra map.
The affine tilde/global-sections unit and ideal-product/cokernel comparison identify
our displayed projections with N -> N/I^(n+1)N and the transitions with reductions.
Completeness therefore supplies exactly the universal property of this cone; dropping
the zero quotient at exponent zero does not change compatible families. Finally, if
r has the residue of a modulo I^(n+1), the completion quotient formula puts
r - algebraMap A B a in K^(n+1). Its product with any x is killed by this quotient
projection, so the projection of r x equals a times the projection of x. The unit
and cokernel comparison transport this equality to the displayed sections maps.
For I = bottom this is the constant module cone; for I = top both B and N are zero. -/
theorem coherentFormalModules_affine_quotientCone_complete
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (N : ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N)) :
    Nonempty (IsLimit (coherentFormalModules_affine_quotientCone A I J N.obj)) ∧
    (∀ (n : ℕ) (r : AdicCompletion I A) (a : A) (x : N.obj),
      AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a →
      (coherentFormalModules_affine_quotientCone A I J N.obj).π.app (op n) (r • x) =
        a • (coherentFormalModules_affine_quotientCone A I J N.obj).π.app (op n) x) := by
  sorry

end AlgebraicGeometry
