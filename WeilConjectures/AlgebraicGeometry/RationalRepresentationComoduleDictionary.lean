/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie
public import WeilConjectures.AlgebraicGeometry.LinearGroupSchemes
public import WeilConjectures.AlgebraicGeometry.HopfCoactionLinearization
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Rational representations and coordinate Hopf comodules

Source: Milne, Algebraic Groups (2017), Chapter 4(a), printed pp.83--84,
Remark 4.1, equations (24)--(25), and Chapter 4(e), printed pp.87--89.
(blueprint: lem-sfb-rational-representation-comodule-dictionary)

Scalar extensions use R tensor V, as in Mathlib's LinearMap.baseChange and Milne p.83;
coactions use V tensor k[G]. The symmetry map in the generic-element construction
records the identification explicitly. Test algebras and individual vector spaces
have the same fixed universe; the type of natural families lives one universe higher.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.RationalRepresentation

variable {k : Type u} [Field k]
variable (G : Scheme.{u}) [G.Over (Spec (.of k))]
variable [GrpObj (G.asOver (Spec (.of k)))] [IsAffine G]
variable (V : Type u) [AddCommGroup V] [Module k V]

/-- Natural group actions on the actual scalar extensions R tensor V.
Source: Milne, Chapter 4(a), p.83 (blueprint: lem-sfb-rational-representation-comodule-dictionary).
-/
structure NaturalRepresentation where
  /-- An R-linear automorphism for each algebra-valued point, respecting the group law. -/
  action : ∀ (R : Type u) [CommRing R] [Algebra k R],
    points (G.asOver (Spec (.of k))) R →* (R ⊗[k] V ≃ₗ[R] R ⊗[k] V)
  /-- Compatibility with every homomorphism of test algebras. -/
  naturality : ∀ (R T : Type u) [CommRing R] [Algebra k R]
    [CommRing T] [Algebra k T] (α : R →ₐ[k] T)
    (x : points (G.asOver (Spec (.of k))) R) (z : R ⊗[k] V),
    α.toLinearMap.rTensor V (action R x z) =
      action T (points.map (G.asOver (Spec (.of k))) α x) (α.toLinearMap.rTensor V z)

/-- The universal coordinate-valued point, induced by id on the coordinate algebra.
Source: Milne, Remark 4.1, p.84
(blueprint: lem-sfb-rational-representation-comodule-dictionary). -/
noncomputable def genericPoint : points (G.asOver (Spec (.of k))) Γ(G, ⊤) :=
  G.isoSpec.inv.asOver (Spec (.of k))

/-- The algebra-valued point associated to x : k[G] to R, using the affine Spec dictionary.
Source: Milne, Remark 4.1, p.84
(blueprint: lem-sfb-rational-representation-comodule-dictionary). -/
noncomputable def coordinatePoint (R : Type u) [CommRing R] [Algebra k R]
    (x : Γ(G, ⊤) →ₐ[k] R) : points (G.asOver (Spec (.of k))) R :=
  Spec.mapMulEquiv (WithConv.toConv x) ≫ genericPoint (k := k) G

/-- Restrict the universal action to 1 tensor V, and switch to the right-coaction order.
Source: Milne, Remark 4.1, p.84
(blueprint: lem-sfb-rational-representation-comodule-dictionary). -/
noncomputable def genericCoaction (r : NaturalRepresentation (k := k) G V) :
    V →ₗ[k] V ⊗[k] Γ(G, ⊤) :=
  (TensorProduct.comm k Γ(G, ⊤) V).toLinearMap ∘ₗ
    (r.action Γ(G, ⊤) (genericPoint (k := k) G)).toLinearMap.restrictScalars k ∘ₗ
    TensorProduct.mk k Γ(G, ⊤) V 1

/-- The right coordinate comodules, using the already defined counit and coassociativity laws.
Source: Milne, (24), p.84
(blueprint: lem-sfb-rational-representation-comodule-dictionary). -/
abbrev CoordinateComodule :=
  {c : V →ₗ[k] V ⊗[k] Γ(G, ⊤) //
    HopfAction.Coassociative k Γ(G, ⊤) V c ∧ HopfAction.Counital k Γ(G, ⊤) V c}

/-- Rational representations correspond bijectively to coordinate comodules, with both formulas.
Source: Milne, Remark 4.1, equations (24)--(25), printed p.84
(blueprint: lem-sfb-rational-representation-comodule-dictionary).

Proof: (1) The tensor universal property gives the associativity, symmetry and unit
identifications. The coordinate Hopf maps give xy=(x tensor y)Delta, e=u epsilon and
inverse xS (lem-sfb-affine-group-coordinate-hopf and affine tensor pushout/product).
(2) Naturality along x : A to R determines every operator from its value at id_A,
restricted to 1 tensor V, by the module-base-change universal property.
(3) Conversely extend (1 tensor x)c R-linearly; its values are the displayed finite sums.
The tensor universal property makes them independent of a presentation and natural in R.
(4) Applying x and y to coassociativity proves the multiplication law on pure tensors.
(5) Counitality proves the identity law, and xS supplies a two-sided inverse.
(6) Conversely evaluate the multiplication law at the two universal points in A tensor A;
the affine-product dictionary identifies their product with Delta and gives coassociativity.
(7) Evaluation at epsilon gives counitality. The two generic-element constructions are
inverse, even in infinite dimension; each tensor has a finite presentation.
These are steps 1--7 of the node, using its tensor, base-change and Hopf dependencies. -/
theorem dictionary [LocallyOfFiniteType (G ↘ Spec (.of k))]
    [QuasiCompact (G ↘ Spec (.of k))] :
    ∃ E : NaturalRepresentation (k := k) G V ≃ CoordinateComodule (k := k) G V,
      (∀ r, (E r).val = genericCoaction (k := k) G V r) ∧
      (∀ (c : CoordinateComodule (k := k) G V) (R : Type u) [CommRing R] [Algebra k R]
        (x : Γ(G, ⊤) →ₐ[k] R) (v : V) (b : R)
        (n : ℕ) (vi : Fin n → V) (ai : Fin n → Γ(G, ⊤)),
        c.val v = ∑ i, vi i ⊗ₜ[k] ai i →
        (E.symm c).action R (coordinatePoint (k := k) G R x) (b ⊗ₜ[k] v) =
          ∑ i, (x (ai i) * b) ⊗ₜ[k] vi i) := by
  sorry

variable (W : Type u) [AddCommGroup W] [Module k W]

/-- Intertwiners are exactly coordinate-comodule maps.
Source: Milne, Remark 4.1, p.84, and Remark 4.18, p.90
(blueprint: lem-sfb-rational-representation-comodule-dictionary).
Proof: step 8 evaluates the intertwining equation at the universal point and 1 tensor v.
Conversely apply x to the coefficient factor and multiply by b. The formula of steps
2--3 gives intertwining on pure tensors, hence everywhere by the tensor universal property. -/
theorem intertwines_iff [LocallyOfFiniteType (G ↘ Spec (.of k))]
    [QuasiCompact (G ↘ Spec (.of k))]
    (r : NaturalRepresentation (k := k) G V) (s : NaturalRepresentation (k := k) G W)
    (f : V →ₗ[k] W) :
    (∀ (R : Type u) [CommRing R] [Algebra k R]
      (x : points (G.asOver (Spec (.of k))) R),
      f.baseChange R ∘ₗ (r.action R x).toLinearMap =
        (s.action R x).toLinearMap ∘ₗ f.baseChange R) ↔
      f.rTensor Γ(G, ⊤) ∘ₗ genericCoaction (k := k) G V r =
        genericCoaction (k := k) G W s ∘ₗ f := by
  sorry

/-- The lifted finite index type for a finite-dimensional vector space, including dimension zero.
Source: Milne, Chapter 4(a), p.83
(blueprint: lem-sfb-rational-representation-comodule-dictionary). -/
abbrev FiniteIndex [FiniteDimensional k V] := ULift.{u} (Fin (Module.finrank k V))

/-- A genuine finite basis identifying GL(V) with the existing general linear group scheme.
Source: Milne, Chapter 4(a), p.83
(blueprint: lem-sfb-rational-representation-comodule-dictionary). -/
noncomputable def finiteBasis [FiniteDimensional k V] : Module.Basis (FiniteIndex (k := k) V) k V :=
  (Module.finBasis k V).reindex Equiv.ulift.symm

/-- In finite dimension the natural representations are precisely group-scheme homomorphisms.
Source: Milne, Chapter 4(a), p.83, and Remark 4.1, p.84
(blueprint: lem-sfb-rational-representation-comodule-dictionary).
Proof: step 9 uses a finite basis to identify R tensor V with R^n, whose automorphism
functor is represented by the existing GeneralLinearGroup. Yoneda for affine schemes
turns natural point maps into unique scheme morphisms; the group laws on all test
algebras detect compatibility with multiplication. Conversely a group-scheme map induces
the natural homomorphisms on points. Step 10 includes the zero space: the empty matrix
scheme GL_0 is Spec k and its automorphism group is trivial. No nonzero hypothesis occurs. -/
theorem finite_dictionary [LocallyOfFiniteType (G ↘ Spec (.of k))]
    [QuasiCompact (G ↘ Spec (.of k))] [FiniteDimensional k V] :
    ∃ E : {f : GeneralLinearGroup.RationalHom (G.asOver (Spec (.of k))) (FiniteIndex (k := k) V) //
        IsMonHom f} ≃ NaturalRepresentation (k := k) G V,
      ∀ (f : {f : GeneralLinearGroup.RationalHom
        (G.asOver (Spec (.of k))) (FiniteIndex (k := k) V) //
        IsMonHom f}) (R : Type u) [CommRing R] [Algebra k R]
        (x : points (G.asOver (Spec (.of k))) R) (z : R ⊗[k] V),
        (E f).action R x z =
          (Matrix.GeneralLinearGroup.toLin' ((finiteBasis (k := k) V).baseChange R)
            (GeneralLinearGroup.homMulEquiv (FiniteIndex (k := k) V) k R
              (x ≫ f.val))).toLinearEquiv z := by
  sorry

/-- Trivial representations have exactly the coaction v tensor 1.
Source: Milne, Chapter 4(a), p.83, and Remark 4.1, p.84
(blueprint: lem-sfb-rational-representation-comodule-dictionary).
Proof: step 11 applies the universal action, which is the identity, to 1 tensor v.
Conversely the evaluation formula of steps 2--3 recovers identity operators on all tensors. -/
theorem trivial_coaction [LocallyOfFiniteType (G ↘ Spec (.of k))]
    [QuasiCompact (G ↘ Spec (.of k))] :
    ∃! r : NaturalRepresentation (k := k) G V,
      (∀ (R : Type u) [CommRing R] [Algebra k R]
        (x : points (G.asOver (Spec (.of k))) R), r.action R x = 1) ∧
      ∀ v : V, genericCoaction (k := k) G V r v = v ⊗ₜ[k] (1 : Γ(G, ⊤)) := by
  sorry

/-- The tensor representation and its coefficient-multiplication coaction in arbitrary dimension.
Source: Milne, Chapter 4(e), pp.88--89, and Remark 4.1, p.84
(blueprint: lem-sfb-rational-representation-comodule-dictionary).
Proof: step 11 uses the canonical distribBaseChange equivalence sending
b tensor (v tensor w) to (b tensor v) tensor_R (1 tensor w). Its inverse multiplies
coefficients. Tensoring the two point automorphisms is natural and respects multiplication
and identities on pure tensors. Evaluate at the universal point and 1 tensor (v tensor w);
the inverse identification yields the displayed double sum of multiplied coefficients.
The empty tensor presentations and the zero vector spaces satisfy the same formula. -/
theorem tensor_coaction [LocallyOfFiniteType (G ↘ Spec (.of k))]
    [QuasiCompact (G ↘ Spec (.of k))]
    (r : NaturalRepresentation (k := k) G V) (s : NaturalRepresentation (k := k) G W) :
    ∃! t : NaturalRepresentation (k := k) G (V ⊗[k] W),
      (∀ (R : Type u) [CommRing R] [Algebra k R]
        (x : points (G.asOver (Spec (.of k))) R) (z : R ⊗[k] (V ⊗[k] W)),
        TensorProduct.AlgebraTensorModule.distribBaseChange k R V W (t.action R x z) =
          TensorProduct.map (r.action R x).toLinearMap (s.action R x).toLinearMap
            (TensorProduct.AlgebraTensorModule.distribBaseChange k R V W z)) ∧
      (∀ (v : V) (w : W) (n m : ℕ) (vi : Fin n → V) (ai : Fin n → Γ(G, ⊤))
        (wi : Fin m → W) (bi : Fin m → Γ(G, ⊤)),
        genericCoaction (k := k) G V r v = ∑ i, vi i ⊗ₜ[k] ai i →
        genericCoaction (k := k) G W s w = ∑ j, wi j ⊗ₜ[k] bi j →
        genericCoaction (k := k) G (V ⊗[k] W) t (v ⊗ₜ[k] w) =
          ∑ i, ∑ j, (vi i ⊗ₜ[k] wi j) ⊗ₜ[k] (ai i * bi j)) := by
  sorry

end AlgebraicGeometry.RationalRepresentation
