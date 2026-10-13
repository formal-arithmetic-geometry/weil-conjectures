/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization

/-! # Geometric cofaces of normalized singleton tensor sections
Source: Stacks Project, Tag 03P2; Tag 03DR for section restrictions.
(blueprint: lem-sc-singleton-tensor-cech-normalized-coface)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The geometric Čech coface preserves the inserted-unit normalization.
Source: Stacks Project, Tag 03P2, affine Čech restriction formula; Tag 03DR.
(blueprint: lem-sc-singleton-tensor-cech-normalized-coface)

Proof: the formal-coproduct Čech face has index map precomposition with
`j.succAbove` and component the product map omitting the j-th projection.
The extended presheaf sends this face to a product lift of projection followed
by restriction. Composing with the singleton-tuple projection selects that
component by `Pi.lift_π`. The selected source tuple is again the constant zero
tuple. The underlying presheaf is precisely the ULift of tensor sections, so
its map is ULift of the section restriction along the displayed product map.
Set s = f(m tensor tprod(b)); its normalization is supplied by hf.
Semilinearity moves the product of
functions outside the restriction, and restriction composition gives the direct
coefficient restriction from U. The retained product projections compose to the
j.succAbove projections. The target j-th factor is the pullback of one, so is
one. Isolating this factor identifies the target scalar product with the
restricted source scalar product.
Set t = f'(m tensor tprod(j.insertNth 1 b)). Its normalization, supplied by hf',
has this same value. The singleton product
projection is an isomorphism and ULift.down is injective, so equality of these
evaluations implies equality of the two Čech sections.
This works for n=0 and all j and does not require affine schemes or invertibility.
The Amitsur coface map and its action on tensors are not asserted here.
-/
theorem singletonTensorCech_normalized_coface
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ) (j : Fin (n + 2))
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (f' : (singletonTensorAmitsur X F U W g).X (n + 1) ⟶
      (singletonTensorCech X F U W g).X (n + 1))
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f)
    (hf' : IsSingletonTensorDegreeComparisonHom X F U W g (n + 1) f')
    (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
    (b : Fin (n + 1) → Γ(W.left, ⊤)) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    (singletonTensorCechCosimplicial X F U W g).δ j
      (f (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b))) =
    f' (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)]
      PiTensorProduct.tprod Γ(U.left, ⊤) (j.insertNth 1 b))) := by
  sorry

end
end AlgebraicGeometry.Scheme
