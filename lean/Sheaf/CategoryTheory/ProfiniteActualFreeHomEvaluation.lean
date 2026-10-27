/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.CategoryTheory.ProfiniteFreeHomResolutionEvaluation

/-! # Evaluation for the adjoint model of profinite free internal Hom

This transports the equalizer evaluation across uniqueness of right adjoints and
uses the explicit Cartesian product as test object.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction

namespace CategoryTheory.CondensedBar.ProfiniteHom

variable (A : Ring.{u})

/-- Evaluate the chosen right adjoint by its counit on the tautological free generator.
Source: Stacks 03EO; free-generator calculation in the profinite Hom comparison
(blueprint: lem-sfb-profinite-actual-free-hom-evaluation). -/
def actualValue (P S : Profinite.{u}) (N : Modules A)
    (x : sections A ((Mod.ihom (freeParameter A P)).obj N) S) :
    sections A N (Profinite.of (S × P)) :=
  (((colimit.ι ((Mod.tensorLeftDiagram A.X (freeParameter A P)).flip.obj
        ((Mod.ihom (freeParameter A P)).obj N))) WalkingParallelPair.one ≫
      (Mod.ihomAdjunction (freeParameter A P)).counit.app N).hom.hom.app
      (op (Profinite.of (S × P))))
    (((Functor.LaxMonoidal.μ
      (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
      ((Mod.ihom (freeParameter A P)).obj N).X (freeParameter A P).X).app
      (op (Profinite.of (S × P))))
        (TensorProduct.tmul ℤ
          (((Mod.ihom (freeParameter A P)).obj N).X.obj.map
            (CompHausLike.ofHom _ (ContinuousMap.fst : C(S × P, S))).op x)
          (generator A P (Profinite.of (S × P))
            (CompHausLike.ofHom _ (ContinuousMap.snd : C(S × P, P))))))

/-- Normalized evaluation for the adjoint model; all maps use the explicit product. -/
structure ActualEvaluation where
  evaluate : ∀ P S : Profinite.{u},
    Mod.ihom (freeParameter A P) ⋙ eval A S ≅ eval A (Profinite.of (S × P))
  tautological : ∀ (P S : Profinite.{u}) (N : Modules A)
      (x : sections A ((Mod.ihom (freeParameter A P)).obj N) S),
    (evaluate P S).hom.app N x = actualValue A P S N x
  scalar : ∀ (P S : Profinite.{u}) (N : Modules A) (a : sectionRing A S)
      (x : sections A ((Mod.ihom (freeParameter A P)).obj N) S),
    (evaluate P S).hom.app N (a • x) =
      (InternalAbelianSheafModule.sectionRingSheaf
        (coherentTopology Profinite.{u}) A.X).obj.map
          (CompHausLike.ofHom _ (ContinuousMap.fst : C(S × P, S))).op a •
        (@id (sections A N (Profinite.of (S × P))) ((evaluate P S).hom.app N x))
  restriction : ∀ (P S S' : Profinite.{u}) (v : S' ⟶ S) (N : Modules A)
      (x : sections A ((Mod.ihom (freeParameter A P)).obj N) S),
    (evaluate P S').hom.app N
        (((Mod.ihom (freeParameter A P)).obj N).X.obj.map v.op x) =
      N.X.obj.map (CompHausLike.ofHom _
        (ContinuousMap.prodMap v.hom.hom (ContinuousMap.id P))).op
          ((evaluate P S).hom.app N x)
  parameter : ∀ (P P' S : Profinite.{u}) (v : P' ⟶ P) (N : Modules A)
      (x : sections A ((Mod.ihom (freeParameter A P)).obj N) S),
    (evaluate P' S).hom.app N
        (((Mod.ihomMap ((InternalBar.free A.toMon).map
          (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).map v))).app N).hom.hom.app
            (op S) x) =
      N.X.obj.map (CompHausLike.ofHom _
        (ContinuousMap.prodMap (ContinuousMap.id S) v.hom.hom)).op
          ((evaluate P S).hom.app N x)

variable [HasDerivedCategory.{u + 2} (Modules A)]

/-- Transfer the equalizer model's free-generator evaluation to the chosen adjoint model.
Source: Stacks 03EO and the free-generator comparison, steps 1--2 of the parent node
(blueprint: lem-sfb-profinite-actual-free-hom-evaluation).

Proof: For each P, uniqueness of right adjoints to Mod.tensorLeft gives a natural
isomorphism from Mod.ihom to Mod.ihom'. Its defining counit equation says that
precomposing the equalizer counit with this isomorphism gives the chosen counit.
Whisker by section evaluation, compose with h.evaluate, and restrict along the
canonical isomorphism from the explicit product to the categorical product.
The counit equation and h.tautological identify the resulting map with actualValue.
The section ring action commutes with each component, which is a module morphism;
h.scalar therefore gives the first-projection action. Naturality of the isomorphism
and h.restriction give the test-object formula. Uniqueness of adjoint mates makes
precomposition by the free module map commute with the isomorphism; h.parameter
then gives the parameter formula. These arguments use neither field coefficients
nor acyclicity. They also apply to empty products and zero modules. -/
theorem actual_free_hom_evaluation (h : Evaluation A) : Nonempty (ActualEvaluation A) := by
  sorry

end CategoryTheory.CondensedBar.ProfiniteHom
