/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.AlgebraicGeometry.TensorPullbackTilde

/-! # Tensor coordinates for the two sides of affine base change

Source: Stacks Project, Schemes, Lemma 01I9 and Cohomology of Schemes, Lemma 02KG.
(blueprint: lem-weil-pbc-affine-base-change-tensor-comparisons).
-/

@[expose] public section

universe u
open CategoryTheory Opposite TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Tensor coordinates for the source and target, normalized by the pullback units.
Source: Stacks Project, Schemes, Lemma 01I9 (1),(2), and Cohomology of Schemes, Lemma 02KG.
(blueprint: lem-weil-pbc-affine-base-change-tensor-comparisons).
Proof: Pushforward of tilde along Spec of R to B is tilde of restriction of scalars,
with the same global sections and canonical section m. Compose its pullback with the
unit-compatible pullback-tilde isomorphism and the tilde global-sections unit to get a.
For b, apply the pullback-tilde comparison to B to R' tensor B, take global sections,
and restrict scalars along R' to R' tensor B. Both comparisons are isomorphisms by
01I9 and the tilde-Gamma adjunction. Their unit formulas give the first equation and
b.symm(((1 tensor 1) tensor z*m)) = eta(tilde.toOpen(z*m)). The balancing relation
over B identifies ((1 tensor z) tensor m) with ((1 tensor 1) tensor z*m), giving the
second equation. These constructions work also for the zero rings and zero module. -/
theorem exists_affineBaseChange_tensorComparisons
    (R B R' : Type u) [CommRing R] [CommRing B] [CommRing R']
    [Algebra R B] [Algebra R R'] (M : ModuleCat.{u} B) :
    letI : Module R M := Module.compHom M (algebraMap R B)
    letI : Algebra B (R' ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    ∃ (a : ((moduleSpecΓFunctor (R := .of R')).obj
        ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj
          ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
            (tilde (R := .of B) M)))) ≃ₗ[R'] R' ⊗[R] M)
      (b : ((moduleSpecΓFunctor (R := .of R')).obj
        ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] B))))).obj
          ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap B (R' ⊗[R] B))))).obj
            (tilde (R := .of B) M)))) ≃ₗ[R'] (R' ⊗[R] B) ⊗[B] M),
      (∀ m : M, a.symm ((1 : R') ⊗ₜ[R] m) =
        (((Classical.choose (exists_tensorPullbackAdjunction
            (Spec.map (CommRingCat.ofHom (algebraMap R R'))))).unit.app
          ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
            (tilde (R := .of B) M))).val.app (op ⊤)
            (tilde.toOpen (R := .of B) M ⊤ m) :
          (moduleSpecΓFunctor (R := .of R')).obj
            ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj
              ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
                (tilde (R := .of B) M))))) ∧
      (∀ (z : B) (m : M), b.symm (((1 : R') ⊗ₜ[R] z) ⊗ₜ[B] m) =
        (((Classical.choose (exists_tensorPullbackAdjunction
            (Spec.map (CommRingCat.ofHom (algebraMap B (R' ⊗[R] B)))))).unit.app
          (tilde (R := .of B) M)).val.app (op ⊤)
            (tilde.toOpen (R := .of B) M ⊤ (z • m)) :
          (moduleSpecΓFunctor (R := .of R')).obj
            ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] B))))).obj
              ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap B (R' ⊗[R] B))))).obj
                (tilde (R := .of B) M))))) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
