/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
import Sheaf.Algebra.LimitFinitePresentation
import Sheaf.Paper.DirectedColimitBaseChangeElementwise

/-!
# Finite-presentation approximation of modules

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00R1
(blueprint: lem-weil-pbc-limit-module-finite-presentation).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- Simultaneous finite-type approximation of a finitely presented algebra and module.
The three colimits are colimit cocones over the directed set `Λ` (in `CommRingCat` and
`AddCommGrpCat`); scalar-extension maps are specified on pure tensors, and the module
tensors put the new scalar ring first (tensor symmetry matches the source).

Source: Stacks Project, Algebra, Tag 00R1 (lemma-limit-module-finite-presentation),
with the non-local version of the proof of Tag 00QX.
(blueprint: lem-weil-pbc-limit-module-finite-presentation)

Proof:
1. Apply `lem-weil-pbc-limit-finite-presentation` (00R0) to obtain the ring systems,
   their colimits, finite-type properties, and canonical ring base-change isomorphisms.
2. Choose a finite presentation matrix for M. Lift its finitely many coefficients to
   one stage using `lem-pc-filtered-colimit-commrings-elementwise` and directedness.
3. Restrict to the cofinal tail above this stage; ring colimits persist by
   `lem-weil-pbc-colimit-initial-full-subcategory`.
4. Take cokernels of the lifted matrices. Their finite generating sets are the images
   of the standard basis; entrywise transition maps induce compatible semilinear maps.
5. Apply `lem-weil-pbc-tensor-right-exact` and `lem-weil-pbc-tensor-finite-product`
   to identify the base changes of these cokernels with the later cokernels and with M.
6. Apply `lem-weil-pbc-directed-colimit-base-change-elementwise` and transport its
   representative and eventual-zero criteria through these isomorphisms. Then use
   `lem-weil-pbc-filtered-colimit-modules-criterion` for abelian groups.
7. Apply `lem-weil-pbc-module-tensor-cancel-base-change` and the ring base-change
   isomorphism to identify the base change over Rₗ with M as well.
-/
theorem limitModuleFinitePresentation
    (R S : Type u) (M : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    [AddCommGroup M] [Module S M] [Module.FinitePresentation S M] :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (A B : Λ ⥤ CommRingCat.{u}) (η : A ⟶ B)
      (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
      (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
      (D : Λ ⥤ AddCommGrpCat.{v})
      (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
      (_ : ∀ i : Λ, Module (B.obj i) (D.obj i)),
      -- (1) the three colimits, compatible with `R → S` and the module actions
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)) ∧
      (∀ i, η.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom (algebraMap R S)) ∧
      (∀ (i j : Λ) (h : i ≤ j) (y : B.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ i (y : B.obj i) (x : D.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) ∧
      -- (2) finiteness of the stages
      (∀ i, Algebra.FiniteType ℤ (A.obj i)) ∧
      (∀ i, letI := (η.app i).hom.toAlgebra; Algebra.FiniteType (A.obj i) (B.obj i)) ∧
      (∀ i, Module.Finite (B.obj i) (D.obj i)) ∧
      -- (3) transition base changes
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (η.app i).hom.toAlgebra
        letI := (A.map (homOfLE h)).hom.toAlgebra
        ∃ e : B.obj i ⊗[A.obj i] A.obj j ≃+* B.obj j,
          ∀ (x : B.obj i) (y : A.obj j),
            e (x ⊗ₜ[A.obj i] y) = (B.map (homOfLE h)).hom x * (η.app j).hom y) ∧
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (B.map (homOfLE h)).hom.toAlgebra
        ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
          ∀ (y : B.obj j) (x : D.obj i),
            e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x) ∧
      -- (4) base changes to the limit
      (∀ i,
        letI := (η.app i).hom.toAlgebra
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)).toAlgebra
        ∃ e : B.obj i ⊗[A.obj i] R ≃+* S,
          ∀ (x : B.obj i) (y : R),
            e (x ⊗ₜ[A.obj i] y) =
              (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) x * algebraMap R S y) ∧
      (∀ i,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)).toAlgebra
        ∃ e : S ⊗[B.obj i] D.obj i ≃ₗ[S] M,
          ∀ (y : S) (x : D.obj i),
            e (y ⊗ₜ[B.obj i] x) = y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) ∧
      (∀ i,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)).toAlgebra
        letI : Module (A.obj i) (D.obj i) := Module.compHom (D.obj i) (η.app i).hom
        letI : Module R M := Module.compHom M (algebraMap R S)
        ∃ e : R ⊗[A.obj i] D.obj i ≃ₗ[R] M,
          ∀ (y : R) (x : D.obj i),
            e (y ⊗ₜ[A.obj i] x) =
              algebraMap R S y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) := by
  sorry

end Algebra
