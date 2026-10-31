/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # Finite Hopf duals and primitive-generator pairings

Source: Milne, Algebraic Groups, Proposition 11.35, pp.222--223, Definition 3.3,
pp.65--66; the finite-free ring pairing argument underlying Proposition 11.36.
(blueprint: lem-sfb-finite-hopf-dual-pairing)

`WithConv` is Mathlib's linear dual with convolution, with unchanged additive module.
The coproduct below is the actual inverse tensor-duality image of transposed multiplication.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

universe u v w z v' w'

open scoped TensorProduct

namespace HopfAlgebra

variable (R : Type u) [CommRing R] (B : Type v) [Ring B] [HopfAlgebra R B]
  [Module.Free R B] [Module.Finite R B] [Coalgebra.IsCocomm R B]

/-- Transpose multiplication through finite tensor duality, and evaluate the counit at 1.
Source: Milne 11.35, pp.222--223 (blueprint: lem-sfb-finite-hopf-dual-pairing). -/
@[instance_reducible]
def finiteDualCoalgebraData : CoalgebraStruct R (WithConv (Module.Dual R B)) where
  comul :=
    (TensorProduct.congr (WithConv.linearEquiv R (Module.Dual R B)).symm
      (WithConv.linearEquiv R (Module.Dual R B)).symm).toLinearMap ∘ₗ
    (TensorProduct.dualDistribEquiv R B B).symm.toLinearMap ∘ₗ
    (LinearMap.mul' R B).dualMap ∘ₗ
    (WithConv.linearEquiv R (Module.Dual R B)).toLinearMap
  counit := (Module.Dual.eval R B 1).comp
    (WithConv.linearEquiv R (Module.Dual R B)).toLinearMap

/-- The concrete dual coproduct is coassociative, counital, and multiplicative.
Source: Milne 11.35, pp.222--223 (blueprint: lem-sfb-finite-hopf-dual-pairing).

Proof: choose a finite basis and its dual basis (def-weil-pbc-free-module).
The tensor-duality equivalence (lem-sfb-finite-free-tensor-dual) detects equalities on
pairs and triples. Both iterated coproducts evaluate as f((bb')b'')=f(b(b'b''));
the counit equations evaluate as f(1b)=f(b)=f(b1). Convolution is associative and
unital by lem-sfb-convolution-linear-map-algebra and commutative by cocommutativity.
Since Delta_B and epsilon_B are algebra maps, evaluation on b,b' shows the dual
coproduct preserves products and 1. Evaluation at 1_B preserves products since
Delta_B(1)=1 tensor 1, and preserves 1 since epsilon_B(1)=1. -/
theorem finiteDual_bialgebra_axioms :
    (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ
        (finiteDualCoalgebraData R B).comul.rTensor _ ∘ₗ
          (finiteDualCoalgebraData R B).comul =
      (finiteDualCoalgebraData R B).comul.lTensor _ ∘ₗ
        (finiteDualCoalgebraData R B).comul ∧
    (finiteDualCoalgebraData R B).counit.rTensor _ ∘ₗ
        (finiteDualCoalgebraData R B).comul = TensorProduct.mk R _ _ 1 ∧
    (finiteDualCoalgebraData R B).counit.lTensor _ ∘ₗ
        (finiteDualCoalgebraData R B).comul = (TensorProduct.mk R _ _).flip 1 ∧
    (finiteDualCoalgebraData R B).counit 1 = 1 ∧
    (∀ f g, (finiteDualCoalgebraData R B).counit (f * g) =
      (finiteDualCoalgebraData R B).counit f * (finiteDualCoalgebraData R B).counit g) ∧
    (finiteDualCoalgebraData R B).comul 1 = 1 ∧
    (∀ f g, (finiteDualCoalgebraData R B).comul (f * g) =
      (finiteDualCoalgebraData R B).comul f * (finiteDualCoalgebraData R B).comul g) := by
  sorry

/-- The dual coalgebra, with explicitly constructed data and the preceding named axioms.
Source: Milne 11.35 (blueprint: lem-sfb-finite-hopf-dual-pairing). -/
instance finiteDualCoalgebra : Coalgebra R (WithConv (Module.Dual R B)) where
  __ := finiteDualCoalgebraData R B
  coassoc := (finiteDual_bialgebra_axioms R B).1
  rTensor_counit_comp_comul := (finiteDual_bialgebra_axioms R B).2.1
  lTensor_counit_comp_comul := (finiteDual_bialgebra_axioms R B).2.2.1

/-- The dual bialgebra uses the existing convolution algebra, with no changed scalar action.
Source: Milne 11.35 (blueprint: lem-sfb-finite-hopf-dual-pairing). -/
instance finiteDualBialgebra : Bialgebra R (WithConv (Module.Dual R B)) :=
  Bialgebra.mk' R _ (finiteDual_bialgebra_axioms R B).2.2.2.1
    (fun {f g} ↦ (finiteDual_bialgebra_axioms R B).2.2.2.2.1 f g)
    (finiteDual_bialgebra_axioms R B).2.2.2.2.2.1
    (fun {f g} ↦ (finiteDual_bialgebra_axioms R B).2.2.2.2.2.2 f g)

/-- The dual antipode is precomposition with the original antipode.
Source: Milne Definition 3.3 and 11.35 (blueprint: lem-sfb-finite-hopf-dual-pairing). -/
def finiteDualAntipode : WithConv (Module.Dual R B) →ₗ[R] WithConv (Module.Dual R B) :=
  (WithConv.linearEquiv R _).symm.toLinearMap ∘ₗ (antipode R (A := B)).dualMap ∘ₗ
    (WithConv.linearEquiv R _).toLinearMap

/-- Both dual antipode identities hold.
Source: Milne 3.3, 11.35 (blueprint: lem-sfb-finite-hopf-dual-pairing).
Proof: evaluate at b. The two left sides are respectively sum f(S(b_1)b_2) and
sum f(b_1 S(b_2)). The original antipode identities reduce both to epsilon_B(b)f(1).
Tensor evaluation is justified by lem-sfb-finite-free-tensor-dual. -/
theorem finiteDual_antipode_axioms :
    LinearMap.mul' R _ ∘ₗ (finiteDualAntipode R B).rTensor _ ∘ₗ Coalgebra.comul =
        Algebra.linearMap R _ ∘ₗ Coalgebra.counit ∧
    LinearMap.mul' R _ ∘ₗ (finiteDualAntipode R B).lTensor _ ∘ₗ Coalgebra.comul =
        Algebra.linearMap R _ ∘ₗ Coalgebra.counit := by
  sorry

/-- The canonical commutative Hopf dual of a finite free cocommutative Hopf algebra.
Source: Milne 11.35 (blueprint: lem-sfb-finite-hopf-dual-pairing). -/
instance finiteDualHopfAlgebra : HopfAlgebra R (WithConv (Module.Dual R B)) where
  antipode := finiteDualAntipode R B
  mul_antipode_rTensor_comul := (finiteDual_antipode_axioms R B).1
  mul_antipode_lTensor_comul := (finiteDual_antipode_axioms R B).2

/-- The defining evaluation formulas for all five dual Hopf operations.
Source: Milne 3.3 and 11.35, pp.65--66,222--223.
(blueprint: lem-sfb-finite-hopf-dual-pairing).
Proof: the product and unit are the formulas of lem-sfb-convolution-linear-map-algebra.
Apply tensor duality and its inverse to the transposed multiplication for the coproduct
formula (lem-sfb-finite-free-tensor-dual). The counit evaluates at 1 by definition,
and the antipode is precomposition with S_B. These are node proof steps 1--4. -/
theorem finiteDual_formulas :
    (∀ (f g : WithConv (Module.Dual R B)) (b : B),
      (f * g) b = LinearMap.mul' R R
        (TensorProduct.map f.ofConv g.ofConv (Coalgebra.comul b))) ∧
    (∀ b : B, (1 : WithConv (Module.Dual R B)) b = Coalgebra.counit b) ∧
    (∀ (f : WithConv (Module.Dual R B)) (b b' : B),
      TensorProduct.dualDistrib R B B
        (TensorProduct.map (WithConv.linearEquiv R _).toLinearMap
          (WithConv.linearEquiv R _).toLinearMap (Coalgebra.comul f))
        (b ⊗ₜ[R] b') = f (b * b')) ∧
    (∀ f : WithConv (Module.Dual R B), Coalgebra.counit f = f 1) ∧
    (∀ (f : WithConv (Module.Dual R B)) (b : B),
      antipode R f b = f (antipode R b)) := by
  sorry

omit [Module.Free R B] [Module.Finite R B] [Coalgebra.IsCocomm R B] in
/-- Scalar extension of functionals, including the `WithConv` identifications.
Source: Milne 11.35, scalar comparison (blueprint: lem-sfb-finite-hopf-dual-pairing). -/
def finiteDualBaseChange (T : Type z) [CommRing T] [Algebra R T] :
    T ⊗[R] WithConv (Module.Dual R B) →ₗ[T]
      WithConv (Module.Dual T (T ⊗[R] B)) :=
  (WithConv.linearEquiv T _).symm.toLinearMap ∘ₗ
    ((Module.Dual.baseChange T).comp
      (WithConv.linearEquiv R (Module.Dual R B)).toLinearMap).liftBaseChange T

/-- The evaluation map is a Hopf isomorphism, without flatness of the new base.
Source: Milne 11.35, pp.222--223 (blueprint: lem-sfb-finite-hopf-dual-pairing).
Proof: for a finite basis e_i the inverse sends h to sum h(1 tensor e_i) tensor e_i^*.
The resulting bijection respects convolution on pure tensors by the comultiplication
formula for base change; its coproduct compatibility is detected on pairs by
lem-sfb-finite-free-tensor-dual over T. Unit, counit and antipode compatibility evaluate
to epsilon_B(b), f(1_B), and f(S_B(b)), multiplied by the input scalars.
No flatness enters; pure tensors generate by def-weil-pbc-module-tensor-product. -/
theorem finiteDual_baseChange (T : Type z) [CommRing T] [Algebra R T] :
    ∃ e : (T ⊗[R] WithConv (Module.Dual R B)) ≃ₐc[T]
        WithConv (Module.Dual T (T ⊗[R] B)),
      e.toLinearMap = finiteDualBaseChange R B T ∧
      (∀ x, e (antipode T x) = antipode T (e x)) ∧
      (∀ (t t' : T) (f : WithConv (Module.Dual R B)) (b : B),
        e (t ⊗ₜ[R] f) (t' ⊗ₜ[R] b) = t * t' * algebraMap R T (f b)) := by
  sorry

/-- Compatibility of the dual comparison with successive scalar extensions.
Source: Milne 11.35--11.36, scalar-extension calculation in node proof step 11.
(blueprint: lem-sfb-finite-hopf-dual-pairing).
Proof: evaluate on u tensor (t tensor f) and u' tensor (t' tensor b). Both maps give
u u' times the image of t t' f(b). Associativity and the scalar-tower identity identify
these values. Tensor generators and extensionality prove the equality of maps. -/
theorem finiteDual_baseChange_comp
    (T : Type z) [CommRing T] [Algebra R T]
    (U : Type w) [CommRing U] [Algebra R U] [Algebra T U] [IsScalarTower R T U] :
    (finiteDualBaseChange T (T ⊗[R] B) U).comp
        ((finiteDualBaseChange R B T).baseChange U) =
      ((WithConv.linearEquiv U _).symm.toLinearMap.comp
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R T U U B).toLinearMap.dualMap.comp
          (WithConv.linearEquiv U _).toLinearMap)).comp
        ((finiteDualBaseChange R B U).comp
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R T U U
            (WithConv (Module.Dual R B))).toLinearMap) := by
  sorry

section Pairings

variable {R} {B}

/-- Transpose an R-bilinear pairing, keeping Mathlib's convolution dual synonym.
Source: the pairing calculation underlying Milne 11.36, p.223.
(blueprint: lem-sfb-finite-hopf-dual-pairing) -/
def finitePairingTranspose {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (r : M →ₗ[R] WithConv (Module.Dual R N)) :
    N →ₗ[R] WithConv (Module.Dual R M) :=
  (WithConv.linearEquiv R _).symm.toLinearMap ∘ₗ
    ((WithConv.linearEquiv R _).toLinearMap.comp r).flip

/-- The primitive-generator criterion, and the unique converse convolution transpose.
Source: Milne 11.35--11.36, pp.222--223; the finite-free ring argument is the
agent-supplied argument recorded in the DAG (blueprint: lem-sfb-finite-hopf-dual-pairing).

Proof plan (the remaining steps of the node):
6. Transpose r(b)(c). Since r preserves multiplication and 1, evaluations at b,b'
show Delta_A(t(c))=(t tensor t)Delta_C(c), and evaluation at 1 gives counit
compatibility. Use lem-sfb-finite-free-tensor-dual to detect the tensor equality.
7. The generator identity at c=c'=1 gives r(p)(1)=2r(p)(1), hence r(p)(1)=0
by subtraction in R, in every characteristic. Evaluation at 1_C is an algebra map
on convolution. It therefore agrees with epsilon_B on the algebra generated by P,
which is all of B; thus t(1_C)=epsilon_B.
8. For each b, let E(b) be the full multiplicativity pairing identity. It holds on
scalars and on P by primitivity and the assumed derivation identity. It is closed
under sums and scalar products. For xy, expand r(xy) by convolution and Delta_C(cc')
by multiplicativity; apply E(x),E(y), commute scalars in R and use convolution twice.
This proves E(xy) since Delta_B(xy)=Delta_B(x)Delta_B(y). Algebra induction proves
E(b) for every b, so t preserves multiplication. This uses
lem-sfb-convolution-linear-map-algebra, with no finite or flat condition on C.
9. In convolution Hom_R(C,A), t composed with S_C and S_A composed with t are both
two-sided inverses of t. Associativity gives their equality, hence antipode
compatibility. Conversely, multiplicativity of t evaluated on p gives the stated
identity after substituting Delta_B(p)=p tensor 1+1 tensor p.
10. Given a Hopf map t, transpose back. Its coproduct and counit compatibilities give
r(bb')=r(b)*r(b') and r(1)=epsilon_C. Transposing twice fixes every pairing value,
so the converse is unique. -/
theorem finiteDual_pairing_criterion (C : Type w) [CommRing C] [HopfAlgebra R C]
    (P : Set B) (hgen : Algebra.adjoin R P = ⊤)
    (hprim : ∀ b ∈ P, Coalgebra.comul (R := R) b =
      b ⊗ₜ[R] (1 : B) + (1 : B) ⊗ₜ[R] b ∧ Coalgebra.counit (R := R) b = 0) :
    (∀ r : B →ₐ[R] WithConv (Module.Dual R C),
      ((∃ t : C →ₐc[R] WithConv (Module.Dual R B),
          t.toLinearMap = finitePairingTranspose r.toLinearMap ∧
          ∀ c, t (antipode R c) = antipode R (t c)) ↔
        ∀ b ∈ P, ∀ c c' : C,
          r b (c * c') = Coalgebra.counit c * r b c' + r b c * Coalgebra.counit c')) ∧
    (∀ t : C →ₐc[R] WithConv (Module.Dual R B),
      ∃! r : B →ₐ[R] WithConv (Module.Dual R C),
        finitePairingTranspose r.toLinearMap = t.toLinearMap) := by
  sorry

/-- Naturality of transposition in both Hopf algebra arguments.
Source: the pairing calculation underlying Milne 11.36, p.223.
(blueprint: lem-sfb-finite-hopf-dual-pairing).
Proof: replace the pairing by r(beta(b'))(gamma(c')). Both orders of transposition
and precomposition have exactly this value; extensionality gives the equalities.
This is step 11 of the node's proof. -/
theorem finiteDual_pairing_natural
    (B' : Type v') [Ring B'] [HopfAlgebra R B']
    (C : Type w) [CommRing C] [HopfAlgebra R C]
    (C' : Type w') [CommRing C'] [HopfAlgebra R C']
    (β : B' →ₐc[R] B) (γ : C' →ₐc[R] C)
    (r : B →ₐ[R] WithConv (Module.Dual R C)) :
    (∀ (b' : B') (c : C),
      finitePairingTranspose (r.toLinearMap.comp β.toLinearMap) c b' =
        finitePairingTranspose r.toLinearMap c (β b')) ∧
    (∀ (b : B) (c' : C'),
      finitePairingTranspose
          ((WithConv.linearEquiv R _).symm.toLinearMap.comp
            (γ.toLinearMap.dualMap.comp
              ((WithConv.linearEquiv R _).toLinearMap.comp r.toLinearMap))) c' b =
        finitePairingTranspose r.toLinearMap (γ c') b) := by
  sorry

/-- Scalar-extended pairings commute with transposition; no dual base-change isomorphism
for the possibly infinite C is asserted.
Source: Milne 11.35--11.36, scalar-extension calculation in node proof step 11.
(blueprint: lem-sfb-finite-hopf-dual-pairing).
Proof: the extended pairing on u tensor b, v tensor c is uv r(b)(c), by balancing.
Both transposes thus have the same values on pure tensors. These generate the tensor
modules (def-weil-pbc-module-tensor-product), giving the equality of maps. Each Hopf
formula is multilinear and the scalar-extended formula multiplies its old value by
the participating scalars. For successive extensions, multiplication of those scalars
is associative. Primitive generators extend to 1 tensor P and still generate the
base-changed algebra. No isomorphism between T tensor C^* and (T tensor C)^* is used. -/
theorem finiteDual_pairing_baseChange
    (C : Type w) [CommRing C] [HopfAlgebra R C]
    (T : Type z) [CommRing T] [Algebra R T]
    (r : B →ₐ[R] WithConv (Module.Dual R C)) :
    (∃ rT : (T ⊗[R] B) →ₐ[T] WithConv (Module.Dual T (T ⊗[R] C)),
      rT.toLinearMap = (finiteDualBaseChange R C T).comp (r.toLinearMap.baseChange T)) ∧
    finitePairingTranspose
        ((finiteDualBaseChange R C T).comp (r.toLinearMap.baseChange T)) =
      (finiteDualBaseChange R B T).comp
        ((finitePairingTranspose r.toLinearMap).baseChange T) ∧
    (∀ (u v : T) (b : B) (c : C),
      (finiteDualBaseChange R C T) ((r.toLinearMap.baseChange T) (u ⊗ₜ[R] b))
        (v ⊗ₜ[R] c) = u * v * algebraMap R T (r b c)) := by
  sorry

end Pairings

end HopfAlgebra
