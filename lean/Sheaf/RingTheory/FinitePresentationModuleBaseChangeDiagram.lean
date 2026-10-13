/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.RingTheory.FiniteType
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # The presentation-matrix diagram before its colimit verification
Source: Stacks Project, Algebra, Tags 00QX and 00R1.
(blueprint: lem-weil-pbc-finite-presentation-base-change-diagram).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

/-- Construct the diagram from a lifted finite presentation matrix and its tensor comparison maps.
Source: Stacks Project, Algebra, Tag 00QX, presentation-matrix paragraph,
non-local construction used in Tag 00R1.
(blueprint: lem-weil-pbc-finite-presentation-base-change-diagram)

Proof: The finite presentation f, g and its lifted matrix A₀ are given explicitly.
Restrict to the upper tail of i₀. It is nonempty and directed. Every original stage
maps to a tail stage, so its full inclusion is final.
At each tail stage take the quotient of its finite free module by the image of the
lifted matrix. The ring transition maps preserve these images and descend to additive
maps of quotients. Identities, compositions, and scalar compatibility follow on
representatives, producing D and ν. The images of the coordinate vectors generate
these modules. Each stage ring is countable: a finite-type integer algebra is a
quotient of a polynomial algebra in finitely many variables over ℤ. The finite powers
and their quotients are therefore countable and small in universe v. Transport the
explicit quotients, their actions and maps through `Shrink` equivalences to Type v.
Tensor right exactness identifies each base-changed quotient with the quotient by the
transported matrix, using the finite-product tensor equivalence for the free terms.
At a later stage this is precisely its defining quotient; over S it is the original
presentation of M. On pure tensors the resulting equivalences send y tensor x to y
times the image of x. No additive colimit property is asserted here.
-/
theorem exists_finitePresentation_baseChange_diagram
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (B : I ⥤ CommRingCat.{u}) (S : Type u) [CommRing S]
    (κ : B ⟶ (Functor.const I).obj (CommRingCat.of S))
    (hfinite : ∀ i, Algebra.FiniteType ℤ (B.obj i))
    (M : Type v) [AddCommGroup M] [Module S M]
    (n m : ℕ) (f : (Fin n → S) →ₗ[S] M)
    (g : (Fin m → S) →ₗ[S] (Fin n → S))
    (hf : Function.Surjective f) (hexact : Function.Exact g f)
    (i₀ : I) (A₀ : Matrix (Fin n) (Fin m) (B.obj i₀))
    (hA : ∀ a b, (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i₀)) (A₀ a b) =
      LinearMap.toMatrix' g a b) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (F : J ⥤ I) (_ : F.Final)
      (D : J ⥤ AddCommGrpCat.{v})
      (ν : D ⟶ (Functor.const J).obj (AddCommGrpCat.of M))
      (_ : ∀ j, Module (B.obj (F.obj j)) (D.obj j)),
      (∀ (i j : J) (h : i ≤ j) (y : B.obj (F.obj i)) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (F.map (homOfLE h))).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ j (y : B.obj (F.obj j)) (x : D.obj j),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app j)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app (F.obj j))) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app j)) x) ∧
      (∀ j, Module.Finite (B.obj (F.obj j)) (D.obj j)) ∧
      (∀ (i j : J) (h : i ≤ j),
        letI := (B.map (F.map (homOfLE h))).hom.toAlgebra
        ∃ e : B.obj (F.obj j) ⊗[B.obj (F.obj i)] D.obj i ≃ₗ[B.obj (F.obj j)] D.obj j,
          ∀ (y : B.obj (F.obj j)) (x : D.obj i),
            e (y ⊗ₜ[B.obj (F.obj i)] x) = y • (D.map (homOfLE h)).hom x) ∧
      (∀ j,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app (F.obj j))).toAlgebra
        ∃ e : S ⊗[B.obj (F.obj j)] D.obj j ≃ₗ[S] M,
          ∀ (y : S) (x : D.obj j),
            e (y ⊗ₜ[B.obj (F.obj j)] x) =
              y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app j)) x) := by sorry

end Module
