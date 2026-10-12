/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra

import Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.RingTheory.NakayamaNilpotent
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # CoherentFormalModulesAffineLimit

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Construction of the finite completed-module limit functor, with its projections.
This asserts no equivalence and constructs no inverse functor.

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, proof paragraphs on
Nakayama, the surjective kernel tower and Mittag-Leffler; Schemes 01I7/01IB.
(blueprint: lem-weil-pbc-coherent-formal-modules-affine-limit).

Proof: For each F, apply coherent/finite-type correspondence on Spec A and the affine
sections formula for ideal products and cokernels. Its sections M_n are finite A-modules,
annihilated by I^(n+1), with surjective transitions whose kernels are I^(n+1)M_(n+1).
Form the ModuleCat limit of this tower. Each coordinate is an A/I^(n+1)-module;
act on compatible sequences by the coordinates of a completed scalar. This preserves
compatibility and satisfies the module laws coordinatewise. The underlying A-module
is the original limit, since restricted completed scalars act by their residues.
Surjectivity of tower projections allows lifts x_i of generators at level one. Their
coordinate maps (A/I^(n+1))^t -> M_n are surjective by nilpotent Nakayama. The kernels
have surjective transitions: lift a kernel vector, then subtract an element in
I^(n+1) times the free module to kill its next coordinate image. Mittag-Leffler gives
a surjection from the completed free module onto the limit, so it is finite.
For fixed n, a vector lifting a limit element with zero nth coordinate has nth
coordinate in the kernel tower. Lift that vector through the kernel limit and subtract
it. The difference belongs to I^(n+1) times the completed free module, by the completion
quotient formula. Thus the projection kernel is exactly I^(n+1) times the limit.
A morphism of formal systems induces an A-linear map of limits; the coordinatewise
scalar action makes it completion-linear. Uniqueness in the limit proves identity and
composition, giving L into the full finite-module subcategory. The limit cone supplies
p and its IsLimit witness. Its map equation gives naturality; the kernel calculation
gives the third assertion; componentwise scalar action gives the last assertion. -/
theorem coherentFormalModules_affine_limit (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) :
    ∃ L : CoherentFormalModule (Spec (CommRingCat.of A)) J ⥤
      ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N),
    ∃ p : ∀ F : CoherentFormalModule (Spec (CommRingCat.of A)) J,
      (Functor.const ℕᵒᵖ).obj
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
          (L.obj F).obj) ⟶ F.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A),
    (∀ F, Nonempty (IsLimit (Cone.mk _ (p F)))) ∧
    (∀ (F G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (f : F ⟶ G)
      (n : ℕ),
      (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map
        (L.map f).hom ≫ (p G).app (op n) =
      (p F).app (op n) ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map (f.hom.app (op n))) ∧
    (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ),
      Function.Surjective ((p F).app (op n)) ∧
      LinearMap.ker ((p F).app (op n)).hom =
        I ^ (n + 1) • (⊤ : Submodule A
          ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
            (L.obj F).obj))) ∧
    (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ)
      (r : AdicCompletion I A) (a : A) (x : (L.obj F).obj),
      AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a →
      (p F).app (op n) (r • x) = a • (p F).app (op n) x) := by
  sorry

end AlgebraicGeometry
