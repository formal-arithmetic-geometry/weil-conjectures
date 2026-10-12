module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.FieldTheory.SeparableRootPthPower

@[expose] public section
set_option autoImplicit false
universe w
namespace FieldExtension

/-- One coefficient-root construction strictly decreases the inseparable degree.
Source: Stacks Project, Algebra, Tag 04KM, the induction step (steps 4--9 of
`lem-weil-pbc-make-separably-generated`).

Proof. Put E = k(s) and let K_s be its relative separable closure in K. Since
[K : K_s] is not one, the extension is not separable. In characteristic zero this
is impossible, so k has prime characteristic p. Choose beta outside K_s with
alpha = beta^p in K_s by taking the penultimate power in a shortest Frobenius
chain. The minimal polynomial P of alpha over E is separable. Write its
coefficients as f_j(s)/g_j(s), and put h_j = f_j g_j^(p-1). In an algebraic closure
of K, adjoin to k the p-th roots of the finitely many coefficients of the h_j,
forming l. Put E_1 = l(s^(1/p)) and L = K E_1. Frobenius shows that each
coefficient of P is a p-th power in E_1. The elements whose p-th powers lie in
k (respectively K) form a subfield; hence l/k and L/K are purely inseparable.
They are finite because only finitely many algebraic roots were adjoined.
The rooted tuple is algebraically independent over l: raising a polynomial
relation to the p-th power gives a nonzero relation over k among s, since
l^p lies in k. The compositum degree bound makes L/E_1 finite, so the rooted
tuple is a finite transcendence basis t of L/l; L/l is finitely generated.
Let L_s be the relative separable closure of E_1 in L. Separable polynomials
remain separable after extending the base, so K_s lies in L_s. Apply Fields
Tag 031V (2) to P over E_1 in L_s: alpha has a p-th root in L_s, which by
injectivity of Frobenius equals beta. Thus K_s(beta) lies in L_s. Since
K L_s = L, the compositum bound gives [L : L_s] <= [K : K_s(beta)]. The tower
law and beta outside K_s give [K : K_s(beta)] < [K : K_s]. This is the asserted
strict decrease. All fields here are subfields of an algebraic closure of K,
so remain in Type w. Their inclusions give the two scalar towers.
(blueprint: lem-weil-pbc-inseparable-degree-drop) -/
theorem exists_inseparableDegree_drop
    (k K : Type w) [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) (s : Finset K)
    (hs : IsTranscendenceBasis k ((↑) : s → K))
    [Module.Finite (IntermediateField.adjoin k (s : Set K)) K]
    (hne : Field.finInsepDegree (IntermediateField.adjoin k (s : Set K)) K ≠ 1) :
    ∃ (l : Type w) (hl : Field l) (akl : Algebra k l)
      (L : Type w) (hL : Field L) (aKL : Algebra K L) (alL : Algebra l L)
      (akL : Algebra k L) (htl : IsScalarTower k l L) (htK : IsScalarTower k K L),
      Module.Finite k l ∧ IsPurelyInseparable k l ∧
      Module.Finite K L ∧ IsPurelyInseparable K L ∧
      (⊤ : IntermediateField l L).FG ∧
      ∃ t : Finset L, IsTranscendenceBasis l ((↑) : t → L) ∧
        Module.Finite (IntermediateField.adjoin l (t : Set L)) L ∧
        Field.finInsepDegree (IntermediateField.adjoin l (t : Set L)) L <
          Field.finInsepDegree (IntermediateField.adjoin k (s : Set K)) K := by
  sorry

end FieldExtension
