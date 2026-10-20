/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y5
-/
module

public import Sheaf.Algebra.Homology.RingedDerivedTensorNative

/-! # Pure-section formulas for the tensor constraints of module-sheaf complexes

Source: Stacks Project, Tag 0FPQ, and the sign rules of More on Algebra.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory WeilConjectures
open Functor.LaxMonoidal Functor.OplaxMonoidal
namespace CategoryTheory.RingedDerivedNative

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

/-- The symmetry equation on homogeneous pure sections.
Source: Stacks 0FPQ (blueprint: lem-sf-ringed-tensor-complex-constraints). -/
def symmetryPure : Prop :=
  ∀ (P Q : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (p q n : ℤ) (h : p + q = n) (h' : q + p = n) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    ((β_ P Q).hom.f n).val.app U
      (coefficientTensorGenerator.{u, c, v} J R P Q p q n h U x y) =
    (p * q).negOnePow • coefficientTensorGenerator.{u, c, v} J R Q P q p n h' U y x

/-- The associator equation on homogeneous pure sections.
Source: Stacks 0FPQ (blueprint: lem-sf-ringed-tensor-complex-constraints). -/
def associatorPure : Prop :=
  ∀ (P Q N : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (p q r pq qr n : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
    (hn : pq + r = n) (hn' : p + qr = n) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (N.X r).val.obj U),
    ((α_ P Q N).hom.f n).val.app U
      (coefficientTensorGenerator.{u, c, v} J R (P ⊗ Q) N pq r n hn U
        (coefficientTensorGenerator.{u, c, v} J R P Q p q pq hpq U x y) z) =
    coefficientTensorGenerator.{u, c, v} J R P (Q ⊗ N) p qr n hn' U x
      (coefficientTensorGenerator.{u, c, v} J R Q N q r qr hqr U y z)

/-- The leftUnitor equation on homogeneous pure sections.
Source: Stacks 0FPQ (blueprint: lem-sf-ringed-tensor-complex-constraints). -/
def leftUnitorPure : Prop :=
  ∀ (P : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (n : ℤ) (h : 0 + n = n) (U : Cᵒᵖ) (a : R.obj.obj U) (x : (P.X n).val.obj U),
    ((λ_ P).hom.f n).val.app U
      (coefficientTensorGenerator.{u, c, v} J R (𝟙_ _) P 0 n n h U
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (𝟙_ (Modules.{c, v, u} J R))).inv.val.app U) a) x) = a • x

/-- The rightUnitor equation on homogeneous pure sections.
Source: Stacks 0FPQ (blueprint: lem-sf-ringed-tensor-complex-constraints). -/
def rightUnitorPure : Prop :=
  ∀ (P : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (n : ℤ) (h : n + 0 = n) (U : Cᵒᵖ) (a : R.obj.obj U) (x : (P.X n).val.obj U),
    ((ρ_ P).hom.f n).val.app U
      (coefficientTensorGenerator.{u, c, v} J R P (𝟙_ _) n 0 n h U x
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (𝟙_ (Modules.{c, v, u} J R))).inv.val.app U) a)) = a • x

/-- Pure-section descriptions of the constructed complex constraints.
Source: Stacks 0FPQ (blueprint: lem-sf-ringed-tensor-complex-constraints). -/
structure ComplexConstraints : Prop where
  symmetry : symmetryPure.{c, v, u} J R
  associator : associatorPure.{c, v, u} J R
  leftUnitor : leftUnitorPure.{c, v, u} J R
  rightUnitor : rightUnitorPure.{c, v, u} J R

/-- The native complex constraints have the usual signed pure-section formulas.
Source: Stacks Project, Tag 0FPQ, and More on Algebra, sign rules
(blueprint: lem-sf-ringed-tensor-complex-constraints).

Proof: write a generator as the sheafification unit on a presheaf pure tensor,
followed by the inverse tensor-sheafification comparison and the inclusion of its
bidegree summand. The sheafification functor is braided monoidal. Its tensorator's
naturality and the counit's naturality identify the sheaf symmetry on this generator
with the presheaf swap. The complex braiding on the (p,q) summand is the sheaf swap
multiplied by (-1)^(pq); apply the component formula for the Koszul braiding.
For the associator, use its formula on the (p,q,r) summand of the iterated direct sum.
Naturality of the sheafification unit in each tensor factor and the associativity
identity of its monoidal tensorator reduce both sides to the image of
(x tensor y) tensor z under the ordinary module associator, which is
x tensor (y tensor z). There is no interchange of homogeneous factors and no sign.
For the unitors, all summands except degree zero in the unit complex vanish.
The surviving summand is the coefficient ring tensor P^n, respectively P^n tensor
the coefficient ring. The single-complex degree-zero comparison identifies its
specified section with a. The unitality identities of the sheafification tensorator
reduce the maps to the ordinary module unitors, both sending the pure tensor to a*x.
These equalities hold on every object U and every indicated section, independently
of K-flatness, boundedness, the characteristic, and whether the coefficient ring is zero. -/
theorem complexConstraints : ComplexConstraints.{c, v, u} J R := by
  sorry

end CategoryTheory.RingedDerivedNative
