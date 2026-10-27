module

public import Sheaf.RingTheory.DividedPowerDGA
public import Sheaf.RingTheory.DividedPowerVariableAdjunction

/-!
# Adjoining a variable whose differential is a prescribed cycle

Source: Stacks Project, `dpa.tex`, Tag 09PM (`lemma-extend-differential`), using the
single-variable presentations of Tags 09PH and 09PI.
(blueprint: lem-sfb-adjoin-dga-cycle)

The odd and even cases use the recorded free-module presentations. The divided powers on
both algebras are fixed. Uniqueness is among all compatible differentials extending the old
one and taking the prescribed value on the new generator; it does not assume the explicit
formula on monomials. Preservation of divided powers and commutation with the differentials
express that the given graded algebra inclusion is a morphism of divided-power DGAs.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace GradedAlgebra.VariableAdjunction

/-- Adjoining one odd variable with a prescribed cycle as its differential gives a unique
compatible differential, with the signed Leibniz formula on every homogeneous coefficient.
Source: Stacks Project, Tag 09PM, on the odd presentation of Tag 09PH
(blueprint: lem-sfb-adjoin-dga-cycle).

Proof:
1. Use the free left B-module coordinates from
`lem-sfb-divided-power-variable-adjunction`. Define D on the two summands by D(b)=d(b)
and D(bT)=d(b)T+(-1)^p bz for b in degree p. Extend R-linearly using the homogeneous
decomposition. Both terms lower degree by one; D vanishes in degree zero, restricts to d
on B, and takes T to z.
2. Check the Leibniz rule on the four pairs of free summands, using the signed multiplication
of the odd presentation and the old Leibniz rule from `def-sfb-divided-power-dga`.
The constant pair is the old rule. The mixed pairs follow by moving T past a homogeneous
coefficient with the prescribed sign. For bT and cT the product is zero; the two remaining
terms cancel as (-1)^p bczT+(-1)^(p+1) bczT, since z has even degree.
3. On bT the square of D is d²(b)T+((-1)^(p-1)+(-1)^p)d(b)z+bd(z)=0.
For p=0 the terms involving d(b) are zero. On constants it is the old square-zero rule.
4. Any positive even element is x+yT with x positive even and y odd. The adjunction lemma
gives gamma_n(x+yT)=gamma_n(x)+gamma_(n-1)(x)yT for n>0. For n>=2 differentiate this
formula using old compatibility and Leibniz. Expanding D(x+yT)gamma_(n-1)(x+yT) gives the
same four terms. The extra terms vanish by T²=0 and yzyT=zy²T=0. Strict graded
commutativity makes y²=0 even for an inhomogeneous odd y: homogeneous squares vanish and
cross terms cancel in pairs. The n=1 identity uses gamma_0=1. No division by two is used.
5. Any other compatible differential extending d with D'(T)=z has the same displayed
values on bT by Leibniz. The free coordinates and additivity give uniqueness. The inclusion
is already an injective graded algebra map preserving divided powers; the extension equation
makes it commute with the differentials. -/
theorem odd_differential_extension (R : Type u) [CommRing R]
    (B : AlgebraData.{u, v} R) (d : DividedPowerDGA B.grade)
    (e : ℕ) (he : 0 < e) (heodd : Odd e)
    (z : B.Carrier) (hz : z ∈ B.grade (e - 1)) (hcycle : d.d z = 0)
    (C : AlgebraData.{u, w} R) (p : OddPresentation B C e)
    (δ : GradedDividedPowers C.grade)
    (hδ : Preserves p.inclusion d.toGradedDividedPowers δ) :
    ∃ D : DividedPowerDGA C.grade,
      D.toGradedDividedPowers = δ ∧
      (∀ b : B.Carrier, D.d (p.inclusion.toAlgHom b) = p.inclusion.toAlgHom (d.d b)) ∧
      D.d (p.coordinates.symm (0, 1)) = p.inclusion.toAlgHom z ∧
      (∀ D' : DividedPowerDGA C.grade,
        D'.toGradedDividedPowers = δ →
        (∀ b : B.Carrier, D'.d (p.inclusion.toAlgHom b) = p.inclusion.toAlgHom (d.d b)) →
        D'.d (p.coordinates.symm (0, 1)) = p.inclusion.toAlgHom z → D' = D) ∧
      ∀ (i : ℕ) (b : B.Carrier), b ∈ B.grade i →
        D.d (p.inclusion.toAlgHom b * p.coordinates.symm (0, 1)) =
          p.inclusion.toAlgHom (d.d b) * p.coordinates.symm (0, 1) +
            (-1 : C.Carrier) ^ i * (p.inclusion.toAlgHom b * p.inclusion.toAlgHom z) := by
  sorry

/-- Adjoining one even divided-power variable with a prescribed cycle as its differential
gives a unique compatible differential, with its formula on all positive divided monomials.
Source: Stacks Project, Tag 09PM, on the normalized even presentation of Tag 09PI
(blueprint: lem-sfb-adjoin-dga-cycle).

Proof:
1. Use the free summands B t_a, t_a=T^[a], of
`lem-sfb-divided-power-variable-adjunction`. Put D(bt_0)=d(b) and
D(bt_a)=d(b)t_a+(-1)^p bz t_(a-1) for a>=1 and b of degree p. Extend R-linearly across
the homogeneous decomposition and finite sums. This lowers degree by one, is zero in degree
zero, extends d, and takes T to z.
2. Verify Leibniz on bt_a and ct_s using the binomial multiplication of the presentation
and the old DGA axioms from `def-sfb-divided-power-dga`. The coefficient of t_(a+s) is
the old Leibniz rule times choose(a+s,a). For a+s>0 the other coefficient agrees by
choose(a+s-1,a-1)+choose(a+s-1,a)=choose(a+s,a), omitting the first term for a=0 and
the second for s=0. Moving the odd z past c gives (-1)^deg(c). For a=s=0 use the old rule.
3. Applying D twice leaves d²(b)t_a, the two opposite signed d(b)z terms, bd(z)t_(a-1),
and, for a>=2, -bz²t_(a-2). The first terms vanish by d²=0 and the cycle hypothesis.
The last vanishes by strict odd-square-zero for z of degree e-1, also in characteristic two.
The cases p=0, a=0 and a=1 omit the corresponding absent terms.
4. On a positive even monomial bt_a with a>=1, the adjunction lemma gives
 gamma_n(bt_a)=K_(n,a)b^n t_(na), K_(n,a)=(na)!/(n!(a!)^n). Differentiating yields
coefficients n K_(n,a) and K_(n,a). Multiplying D(bt_a) by gamma_(n-1)(bt_a) gives
K_(n-1,a) choose(na,a) and K_(n-1,a) choose(na-1,a-1). The respective coefficients
agree as integer factorial identities, including n=1 with K_(0,a)=1. For a=0 use old
compatibility on positive even coefficients. No integer is inverted in R.
5. Extend compatibility to sums using the divided-power addition formula. Differentiate
 gamma_n(u+v)=sum_(i+j=n) gamma_i(u)gamma_j(v); all divided-power factors have even
parity. Reindex the two sums to obtain (D(u)+D(v))gamma_(n-1)(u+v); gamma_0=1 has zero
derivative. Every positive even element is a finite sum of the monomials just checked.
6. Any competing differential satisfies D'(t_a)=z t_(a-1) by compatibility with the
normalized divided powers of T. Leibniz forces the displayed formula on bt_a. The free
summands and additivity give uniqueness. The existing inclusion preserves grading, algebra
operations and divided powers and is injective by its coordinates. The extension equation
makes it a morphism of divided-power DGAs. -/
theorem even_differential_extension (R : Type u) [CommRing R]
    (B : AlgebraData.{u, v} R) (d : DividedPowerDGA B.grade)
    (e : ℕ) (he : 0 < e) (heeven : Even e)
    (z : B.Carrier) (hz : z ∈ B.grade (e - 1)) (hcycle : d.d z = 0)
    (C : AlgebraData.{u, w} R) (p : EvenPresentation B C e)
    (δ : GradedDividedPowers C.grade)
    (hδ : Preserves p.inclusion d.toGradedDividedPowers δ)
    (hnormalized : EvenNormalized p δ) :
    ∃ D : DividedPowerDGA C.grade,
      D.toGradedDividedPowers = δ ∧
      (∀ b : B.Carrier, D.d (p.inclusion.toAlgHom b) = p.inclusion.toAlgHom (d.d b)) ∧
      D.d (p.coordinates.symm (Finsupp.single 1 1)) = p.inclusion.toAlgHom z ∧
      (∀ D' : DividedPowerDGA C.grade,
        D'.toGradedDividedPowers = δ →
        (∀ b : B.Carrier, D'.d (p.inclusion.toAlgHom b) = p.inclusion.toAlgHom (d.d b)) →
        D'.d (p.coordinates.symm (Finsupp.single 1 1)) = p.inclusion.toAlgHom z → D' = D) ∧
      ∀ (i a : ℕ) (b : B.Carrier), b ∈ B.grade i → 0 < a →
        D.d (p.inclusion.toAlgHom b * p.coordinates.symm (Finsupp.single a 1)) =
          p.inclusion.toAlgHom (d.d b) * p.coordinates.symm (Finsupp.single a 1) +
            (-1 : C.Carrier) ^ i *
              (p.inclusion.toAlgHom b * p.inclusion.toAlgHom z *
                p.coordinates.symm (Finsupp.single (a - 1) 1)) := by
  sorry

end GradedAlgebra.VariableAdjunction
