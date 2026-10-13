/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Category.Ring.Colimits

import Sheaf.Algebra.FinitePresentationColimit
import Sheaf.Paper.DirectedColimitBaseChangeElementwise
import Sheaf.RingTheory.ColimitCategoryFpAlgebras

/-! # Comparing a finite-presentation module model with prescribed stages

Source: Stacks Project, Algebra, Tag 02JO (3), final paragraph.
(blueprint: lem-pc-fp-module-tensor-model-comparison)
-/

@[expose] public section

universe v w x

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A finitely presented algebra and module model agrees with all sufficiently late stages.
No flatness of the model or of the limit is assumed.

Source: Stacks Project, Algebra, Tag 02JO (3), final paragraph; Tags 00QO, 05N9 and 05N7.
(blueprint: lem-pc-fp-module-tensor-model-comparison)

Proof:
1. Restrict to the cofinal tail above i. If needed, pass to its poset reflection:
   indices mutually below each other have inverse transition maps, so the diagram
   descends up to these canonical isomorphisms, with the same colimit. A stage in
   the reflection is represented by an original index; transport its comparisons
   back and extend them to all later original indices. Tensor products commute
   with the ring colimit, giving the A, B and compatible module colimits.
2. Finite presentation of P over the integers factors its map into the limit A algebra
   through one A stage. Above that stage regard all A stages as P-algebras.
3. The right inclusion followed by e gives a P-algebra map Q into the limit B algebra.
   Finite presentation of Q factors it through a B stage. Tensoring gives the comparison
   A_j tensor_P Q to B_j, compatible with the A_j-action by the left-inclusion identity.
4. The comparison is an isomorphism at the limit. Both algebras are finitely presented
   over A_j. Descend its inverse by Tag 05N9 (2) and descend both inverse identities
   by Tag 05N9 (3), taking a common later stage. Every later comparison is an isomorphism.
5. At that stage the model L and the prescribed M give two finitely presented modules
   over B_j. The specified limit linear equivalence identifies their limit base changes.
   Descend it and its inverse by Tag 05N7, then descend both inverse identities on finite
   generators. At a common later stage the descended maps are mutually inverse.
6. Extend these isomorphisms to every later stage. Tensor associativity and the algebra
   comparison identify B_j tensor_Q L with A_j tensor_P L and the prescribed base-change
   module with A_j tensor_A M. Restrict scalars to A_j to obtain the displayed equivalence.
   No flatness enters any step. Zero modules, zero rings, and empty presentations are
   allowed; a common upper bound is used for every finite collection of indices.
-/
theorem exists_eventually_tensor_model_equiv
    {I : Type v} [Preorder I] [IsDirectedOrder I]
    (F : I ⥤ CommRingCat.{v}) (c : Cocone F) (hc : IsColimit c)
    {i : I} {A B M : Type w}
    [CommRing A] [CommRing B] [AddCommMonoid M]
    [Algebra (F.obj i : Type v) A] [Algebra (F.obj i : Type v) B]
    [Algebra.FinitePresentation (F.obj i : Type v) A]
    [Algebra.FinitePresentation (F.obj i : Type v) B]
    [Module B M] [Module.FinitePresentation B M] (f : A →ₐ[F.obj i] B)
    (P Q L : Type x) [CommRing P] [CommRing Q] [Algebra P Q]
    [AddCommMonoid L] [Module Q L]
    [Algebra.FinitePresentation ℤ P] [Algebra.FinitePresentation P Q]
    [Module.FinitePresentation Q L]
    (aP : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      Algebra P ((c.pt : Type v) ⊗[F.obj i] A))
    (e : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      letI := aP
      ((c.pt : Type v) ⊗[F.obj i] A) ⊗[P] Q ≃+* (c.pt : Type v) ⊗[F.obj i] B)
    (he : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      letI := aP
      e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
        (Algebra.TensorProduct.map (Algebra.ofId (c.pt : Type v) (c.pt : Type v))
          f).toRingHom)
    (eM : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      letI := aP
      letI : Algebra Q ((c.pt : Type v) ⊗[F.obj i] B) :=
        (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom).toAlgebra
      letI : Algebra B ((c.pt : Type v) ⊗[F.obj i] B) :=
        Algebra.TensorProduct.rightAlgebra
      Nonempty (((c.pt : Type v) ⊗[F.obj i] B) ⊗[Q] L ≃ₗ[
        (c.pt : Type v) ⊗[F.obj i] B] ((c.pt : Type v) ⊗[F.obj i] B) ⊗[B] M)) :
    letI : Module A M := Module.compHom M f.toRingHom
    letI : Module P L := Module.compHom L (algebraMap P Q)
    ∃ j₀ : I, i ≤ j₀ ∧ ∀ (j : I) (h₀ : i ≤ j₀) (h₁ : j₀ ≤ j),
      letI := (F.map (homOfLE (h₀.trans h₁))).hom.toAlgebra
      letI : Algebra A ((F.obj j : Type v) ⊗[F.obj i] A) :=
        Algebra.TensorProduct.rightAlgebra
      ∃ aPj : Algebra P ((F.obj j : Type v) ⊗[F.obj i] A),
        letI := aPj
        Nonempty (((F.obj j : Type v) ⊗[F.obj i] A) ⊗[P] L ≃ₗ[
          (F.obj j : Type v) ⊗[F.obj i] A] ((F.obj j : Type v) ⊗[F.obj i] A) ⊗[A] M) := by
  sorry

end AlgebraicGeometry
