module

public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import Sheaf.AlgebraicGeometry.GroupSchemeCharacters
public import Mathlib.LinearAlgebra.Contraction

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Cartier duals of finite commutative group schemes

Source: Milne, Algebraic Groups (2017), Section 11c, Lemma 11.11 and Theorem 11.12,
printed pp.212--214; the scheme-valued extension is by Zariski gluing.
(blueprint: lem-sfb-finite-commutative-cartier-representability)

The specified linear identification with the full coordinate dual fixes every Hopf
operation. A finite coordinate basis gives an explicit normalization of the character
bijection on every parameter scheme, including nonaffine and nonreduced schemes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry

/-- The canonical coordinate Hopf algebra of a finite group scheme. Affineness follows
from finiteness over the affine base; the Hopf structure is the recorded canonical one.
Source: Milne, Section 11c, p.212; Mathlib Group/Affine.
(blueprint: lem-sfb-finite-commutative-cartier-representability) -/
def finiteCartierCoordinates (k : Type u) [Field k] (G : Scheme.{u})
    [G.Over (Spec (.of k))] [GrpObj (G.asOver (Spec (.of k)))]
    [IsFinite (G ↘ Spec (.of k))] : CommHopfAlgCat.{u} k := by
  letI : IsAffine G := isAffine_of_isAffineHom (G ↘ Spec (.of k))
  letI := HopfAction.coordinateHopfAlgebra k G
  exact CommHopfAlgCat.of k Γ(G, ⊤)

/-- The transposed coordinate Hopf algebra represents characters, naturally as groups.
The linear equivalence identifies its coordinate vector space with the full linear dual;
it is not a replacement by functions on geometric points. The final equation fixes the
canonical character by its Laurent coordinate, using a finite coordinate basis.

Source: Milne, Section 11c, pp.212--214, Lemma 11.11 and Theorem 11.12; Stacks
Tag 01I1 for morphisms into affine schemes.
(blueprint: lem-sfb-finite-commutative-cartier-representability)

Proof plan, following the ten steps of the accepted DAG split:
1. Finiteness makes G affine with finite-dimensional coordinates H. Choose a finite
basis b and its dual. Evaluation identifies H with its double dual. The tensor-dual
isomorphism is lem-sfb-finite-free-tensor-dual, and dimensions are preserved by
lem-sfb-linear-dual-dimension-rank. Transpose all five structure maps.
2. Evaluate associativity, units, coassociativity and counits on basis tensors.
They are exactly the dual identities for H. Commutativity of G makes the dual product
commutative; commutativity of H makes the dual coproduct cocommutative.
3. Evaluate bialgebra compatibility on a tensor a tensor b: both sides are the sum
of f(a_1 b_1)g(a_2 b_2). The unit and counit calculations are identical. Use the
algebra tensor multiplication of lem-weil-pbc-algebra-tensor-pushout-universal-property.
4. The two antipode cancellations transpose to the dual antipode cancellations.
Inversion preserves multiplication because G is commutative. Apply
lem-sfb-hopf-spectrum-functor to form the finite commutative spectrum of the dual.
5. For an arbitrary k-algebra R, finite-projective tensor-Hom duality
(lem-pc-finite-projective-module-tensor-hom) identifies a linear map alpha on the
dual with x_alpha = sum_i b_i tensor alpha(b_i^*). The map alpha preserves product
and unit exactly when x_alpha is group-like with counit one.
6. The antipode makes every group-like x a unit. Send the Laurent coordinate t to x,
uniquely extending to R[t,t^-1]. This identifies group-like elements with characters
by def-sc-gm-ga, affine spectrum and lem-weil-pbc-fibre-product-affine-spectra.
7. The coproduct on the dual gives x_(alpha star beta) = x_alpha x_beta, so characters
multiply pointwise. Scalar extension sends x_alpha to (id tensor u)(x_alpha).
8. Cover an arbitrary T by affine opens. On every affine open inside an overlap,
the characters agree by scalar naturality. Their Laurent coordinates and inverses
glue. Tag 01I1, lem-weil-pbc-morphism-into-affine-scheme, gives the global character.
9. Conversely the local algebra maps from a character glue coordinate by coordinate
to a map into Spec of the dual. The two constructions are inverse on each affine
open, hence globally, including the empty scheme.
10. Check arbitrary base change on affine covers of inverse images, and multiplication
on affine covers. Separatedness gives both identities globally. No perfection,
reducedness, characteristic restriction or division by the order is used. -/
theorem finite_commutative_cartier_representability
    (k : Type u) [Field k] (G : Scheme.{u}) [G.Over (Spec (.of k))]
    [GrpObj (G.asOver (Spec (.of k)))] [IsCommMonObj (G.asOver (Spec (.of k)))]
    [IsFinite (G ↘ Spec (.of k))] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k (finiteCartierCoordinates k G))
      (D : CommHopfAlgCat.{u} k)
      (e : D ≃ₗ[k] Module.Dual k (finiteCartierCoordinates k G)),
      (∀ (d d' : D) (h : finiteCartierCoordinates k G),
        e (d * d') h =
          TensorProduct.dualDistrib k (finiteCartierCoordinates k G)
            (finiteCartierCoordinates k G) (e d ⊗ₜ[k] e d') (Coalgebra.comul h)) ∧
      (∀ h : finiteCartierCoordinates k G, e (1 : D) h = Coalgebra.counit h) ∧
      (∀ (a : k) (h : finiteCartierCoordinates k G),
        e (algebraMap k D a) h = a * Coalgebra.counit h) ∧
      (∀ (d : D) (a b' : finiteCartierCoordinates k G),
        TensorProduct.dualDistrib k (finiteCartierCoordinates k G)
            (finiteCartierCoordinates k G)
            (TensorProduct.map e.toLinearMap e.toLinearMap (Coalgebra.comul d))
            (a ⊗ₜ[k] b') = e d (a * b')) ∧
      (∀ d : D, Coalgebra.counit d = e d 1) ∧
      (∀ (d : D) (h : finiteCartierCoordinates k G),
        e (HopfAlgebra.antipode k d) h = e d (HopfAlgebra.antipode k h)) ∧
      IsFinite ((hopfSpec (.of k)).obj (op D)).X.hom ∧
      IsCommMonObj ((hopfSpec (.of k)).obj (op D)).X ∧
      ∃ (c : ∀ T : Over (Spec (.of k)),
          CommGroup (GroupSchemeCharacters.Characters (G.asOver (Spec (.of k))) T))
        (Φ : ∀ T : Over (Spec (.of k)),
          @MulEquiv (T ⟶ ((hopfSpec (.of k)).obj (op D)).X)
            (GroupSchemeCharacters.Characters (G.asOver (Spec (.of k))) T)
            inferInstance (c T).toMul),
        (∀ (T S : Over (Spec (.of k)))
          (χ ψ : GroupSchemeCharacters.Characters (G.asOver (Spec (.of k))) T)
          (z : S ⟶ G.asOver (Spec (.of k)) ⊗ T),
          GroupSchemeCharacters.value (@Mul.mul _ (c T).toMul χ ψ) z =
            GroupSchemeCharacters.value χ z * GroupSchemeCharacters.value ψ z) ∧
        (∀ (T T' S : Over (Spec (.of k))) (v : T' ⟶ T)
          (f : T ⟶ ((hopfSpec (.of k)).obj (op D)).X)
          (z : S ⟶ G.asOver (Spec (.of k)) ⊗ T'),
          GroupSchemeCharacters.value (Φ T' (v ≫ f)) z =
            GroupSchemeCharacters.value (Φ T f) (z ≫ (G.asOver (Spec (.of k)) ◁ v))) ∧
        (∀ (T : Over (Spec (.of k)))
          (f : T ⟶ ((hopfSpec (.of k)).obj (op D)).X),
          GroupSchemeCharacters.value (Φ T f) (𝟙 (G.asOver (Spec (.of k)) ⊗ T)) =
            ∑ i : Fin n,
              (fst (G.asOver (Spec (.of k))) T).left.appTop (b i) *
                (snd (G.asOver (Spec (.of k))) T).left.appTop
                  (f.left.appTop ((Scheme.ΓSpecIso (.of D)).inv (e.symm (b.coord i))))) := by
  sorry

end AlgebraicGeometry
