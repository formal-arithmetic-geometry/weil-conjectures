/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.ValuationValueGroupTorsion
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite
import Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import WeilConjectures.RingTheory.HenselianLocalRootLifting
import Sheaf.RingTheory.ValuationRingNormal
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! # Completed factors of a finite separable valued extension

Source: Temkin, Stable modification of relative curves, Proposition 2.2.1,
proof, printed pp. 11--12, and the valued-field preliminaries in section 2.1
(blueprint: lem-trf-separable-valued-completion-factors).

The factor completions are Mathlib's `AbsoluteValue.Completion`. The maps `j` are
characterized as `UniformSpace.Completion.map` of the original inclusions, and the
algebra equivalence is specified on pure tensors. No arbitrary scalar map is used.
The residue-field isomorphisms are pinned to reduction `c/s ↦ c̄/s̄` on elements of `C`.
-/

@[expose] public section

universe u v w

open scoped TensorProduct
open UniformSpace

namespace WeilConjectures

/-- Completed factors, their valuation rings, and the factorization of a primitive
integral element's minimal polynomial.

Source: Temkin, Stable modification of relative curves, section 2.1 and
Proposition 2.2.1, proof, printed pp. 11--12
(blueprint: lem-trf-separable-valued-completion-factors).

Proof plan (the eleven steps in the node):

1. First normalize any valuation ring $W$ in an algebraic extension $H/F$ with $W\cap F=A$.
Order $\Gamma=H^\times/W^\times$ multiplicatively, so $[z]\leq1$ means $z\in W$. The subgroup
$F^\times/A^\times$ identifies with $|F^\times|$. By [lem-trf-valuation-value-group-torsion],
every $\gamma=[z]$ has $\gamma^n=[a]$ for some $n>0$ and $a\in F^\times$. Define
$w(z)=|a|^{1/n}$ and $w(0)=0$. This is independent of choices: if also $\gamma^m=[b]$, then
$a^m/b^n\in W^\times\cap F=A^\times$, so $|a|^m=|b|^n$. Taking common powers proves
multiplicativity and order preservation, strictly so because $|a|=1$ forces $\gamma^n=1$ and an
ordered group is torsion-free. The valuation-ring inequality for classes follows directly from
$z/t\in W\Rightarrow(z+t)/t\in W$; thus $w(z+t)\leq\max(w(z),w(t))$. Its unit ball is exactly
$W$ and it extends $|\cdot|$. Any other extending absolute value with unit ball $W$ is $1$ on
$W^\times$ and must satisfy $w(z)^n=|a|$, proving uniqueness. This argument needs algebraicity,
not separability.

2. Apply [lem-trf-valuation-normalization-localizations] to $A\subset F\subset E$. It gives that
$C$ is a nonzero domain with fraction field $E$, a nonempty set of maximal ideals, and the
bijection $\mathfrak m\mapsto C_{\mathfrak m}$ onto extending valuation rings. Step 1 makes
these equivalently the extending real absolute values. For a maximal $\mathfrak m$, reduction
gives $C_{\mathfrak m}/\mathfrak mC_{\mathfrak m}\cong C/\mathfrak m$: an element
$s\notin\mathfrak m$ already has invertible residue in the field $C/\mathfrak m$, so $c/s$ maps
to $\bar c/\bar s$. We prove finiteness of this set below, without assuming that $C$ is finite
over $A$.

3. Put $K=\widehat F$ and $N=E\otimes_F K$. By [def-weil-vector-space-scalar-extension], $N$ has
dimension $d=[E:F]\geq1$ over $K$; by [lem-weil-pbc-finite-separable-tensor-field-reduced] it is
reduced. It is Noetherian: an ascending chain of ideals is a chain of subspaces, whose
dimensions increase at every strict inclusion and are bounded by $d$. Multiplication by a
nonzerodivisor is an injective endomorphism of this finite-dimensional space, hence surjective,
so the nonzerodivisor is a unit. Therefore $Q(N)=N$. Apply
[lem-weil-pbc-reduced-noetherian-total-ring-fractions] to obtain a $K$-algebra decomposition
$N\cong\prod_{j=1}^t L_j$ with $t\geq1$ and every $L_j/K$ finite. The maps preserve $K$ because
the cited decomposition is compatible with the maps from $N$. Every map $E\to L_j$,
$e\mapsto\pi_j(e\otimes1)$, is a unital field map, hence injective.

4. Give each $L_j$ the extending nonarchimedean absolute value of
[lem-trf-spectral-norm-algebraic-extension]. It is complete by
[lem-per-finite-normed-space-complete], since $K$ is complete, its norm is nontrivial on $F$,
and $L_j/K$ is finite. Use [lem-zl-finite-separable-tensor-primitive-presentation] with $k=F$,
$K=\widehat F$: there is a primitive $\alpha\in E$ such that $N=K[\alpha\otimes1]$ (interchange
tensor factors in the displayed presentation). Consequently $L_j=K[\alpha_j]$. If
$y=\sum_{h=0}^n b_h\alpha_j^h$, choose $a_{h,m}\in F$ converging to each $b_h\in K$. Then
$\sum_h a_{h,m}\alpha_j^h$ lies in the image of $E$ and its distance to $y$ is at most
$\max_h|a_{h,m}-b_h|\,|\alpha_j|^h$, tending to zero. Thus $E$ is dense in $L_j$. The map from
its metric completion sends a Cauchy class $[e_m]$ to $\lim_m e_m$ in $L_j$; definiteness of the
distance gives injectivity, density gives surjectivity, and limits preserve addition and
multiplication. It is therefore a $K$-algebra isomorphism from the completion for the restricted
absolute value to $L_j$.

5. Conversely take any extending absolute value $v$ on $E$ and let $H$ be its metric completion.
Sending a Cauchy sequence in $F$ to the same sequence in $E$ embeds $K$ isometrically into $H$.
The map $q_v:N\to H$, $e\otimes b\mapsto eb$, is a unital $K$-algebra map. In the product
decomposition of Step 3 its coordinate idempotents are orthogonal and sum to $1$. A field has
only idempotents $0,1$, so exactly one maps to $1$. Hence $q_v$ factors through a field
embedding $L_j\hookrightarrow H$. Its image is finite-dimensional over $K$ with the norm
inherited from $H$, and is complete by [lem-per-finite-normed-space-complete]. It is closed: any
sequence from the image converging in $H$ is Cauchy there, converges in the image by
completeness, and the two limits agree. Since the image contains the dense subfield $E$, it
equals $H$. The pullback of the norm of $H$ to $L_j$ agrees with its spectral norm by
[lem-sfb-algebraic-absolute-value-unique], since both extend the given norm on the complete
field $K$. Therefore $v$ is precisely the restriction constructed in Step 4.

6. Different $j$ give different restrictions to $E$. Indeed, if two restrictions agreed, the
maps of Step 4 would identify both $L_j$ and $L_k$ with the same Cauchy completion by
isomorphisms fixing $E$ and $K$. The induced maps $N\to H$ would agree on every $e\otimes b$,
hence have the same kernel. But a coordinate idempotent is in exactly one of the two coordinate
kernels, a contradiction. Steps 4--5 give a bijection between the finite nonempty set of factors
and the absolute values; Step 2 identifies this set with all maximal ideals of $C$. Enumerate it
by $i=1,\ldots,r$. Combining the coordinate isomorphisms identifies $N$ with $\prod_i\widehat
E_i$, and its $i$th component sends $e\otimes b$ to $eb$ because each identification fixes $E$
and $K$. This proves the specified canonical algebra isomorphism, not just an abstract
isomorphism of products.

7. For henselianity put $R=\widehat A=\{b\in K:|b|\leq1\}$ and $\mathfrak n=\{|b|<1\}$. The
valuation inequalities show that $R$ is a local ring with maximal ideal $\mathfrak n$: precisely
its norm-one elements are units. Let $g\in R[T]$ be monic and $\bar a$ a simple root of its
residue polynomial. Choose a lift $a_0\in R$, so $\rho=|g(a_0)|<1$ and $|g'(a_0)|=1$. If
$g(a_0)=0$ we are done; otherwise set $a_{n+1}=a_n-g(a_n)/g'(a_n)$. For $a,h\in R$, binomial
expansion gives $g(a+h)=g(a)+g'(a)h+h^2 B$ and $g'(a+h)-g'(a)=hD$ with $B,D\in R$. Induction
therefore gives $a_n\in R$, $|g'(a_n)|=1$, $|g(a_n)|\leq\rho^{2^n}$ and
$|a_{n+1}-a_n|\leq\rho^{2^n}$. The ultrametric inequality makes $(a_n)$ Cauchy, since for $m>n$
the distance is at most $\rho^{2^n}$. Its limit $a$ exists in $K$, lies in the closed unit ball,
satisfies $g(a)=0$ by the polynomial continuity estimate, and $|a-a_0|\leq\rho<1$. Thus it lifts
$\bar a$. Apply [lem-weil-pbc-henselian-local-root-lifting] to conclude that $R$ is henselian in
the stated idempotent-lifting sense.

8. Let $H/K$ now be any finite extension, including inseparable ones. By
[lem-trf-spectral-norm-algebraic-extension] it has a spectral absolute value $s$. Step 1,
applied with base $K$, normalizes every valuation ring extending $R$. By
[lem-sfb-algebraic-absolute-value-unique], every such normalized absolute value is $s$, so its
ring is $W=\{z:s(z)\leq1\}$. Apply [lem-trf-valuation-normalization-localizations] to the
integral closure $D$ of $R$ in $H$. Its maximal ideals are nonempty and their localizations are
exactly these extending valuation rings, with unique maximal ideal for each such ring. Thus $D$
has one maximal ideal and $D=D_{\mathfrak n_D}=W$. Taking $H=\widehat E_i$ is legitimate by
Steps 3--6, which proved this field is finite over $K$. Its existing absolute value equals $s$
by uniqueness; hence $D$ is its closed unit ball, as claimed.

9. Suppose $x\in C$ and $E=F(x)$. By [lem-weil-pbc-valuation-ring-normal], $A$ is integrally
closed, and $C$ has fraction field $E$ by Step 2. Applying
[lem-sfb-integral-minpoly-fraction-descent] to $A\subset C$ shows that the monic minimal
polynomial $f$ of $x$ belongs to $A[T]$. Let $d=\deg f$. By
[lem-weil-pbc-minimal-polynomial-quotient-field-iso], $E=F[x]$ and $1,x,\ldots,x^{d-1}$ is a
basis (division by the monic $f$ spans the quotient; a relation of smaller degree contradicts
minimality). By [def-weil-vector-space-scalar-extension] its tensor images form a $K$-basis of
$N$. Thus evaluation $K[T]\to N$, $T\mapsto x\otimes1$, is surjective with kernel $(f)$, and
projection to $L_i=\widehat E_i$ is surjective with kernel $(f_i)$, where $f_i$ is the monic
minimal polynomial of $x_i$. The same quotient-basis argument gives $\deg f_i=[L_i:K]$.

10. Each $f_i$ divides $f$, by division with remainder and minimality at $x_i$. A minimal
polynomial is irreducible: a nontrivial factorization would give a smaller-degree vanishing
factor in the field $L_i$. The ideals $(f_i)$ are distinct, because the coordinate kernels in
$N$ are distinct and $K[T]\to N$ is surjective. Hence these distinct monic irreducibles are
pairwise coprime; repeated Euclidean division (Bezout) gives $\prod_i f_i\mid f$. On the other
hand, $\sum_i\deg f_i=\sum_i[L_i:K]=\dim_KN=d$, by the product decomposition and Step 9's basis.
Since all polynomials are monic, $f=\prod_i f_i$. The image $x_i$ is integral over $R$ because
the monic relation for $x\in C$ maps from $A[T]$ to $R[T]$. Its integral closure $D_i\subset
L_i$ is the valuation ring from Step 8 and has fraction field $L_i$. Normality of $R$ by
[lem-weil-pbc-valuation-ring-normal] and [lem-sfb-integral-minpoly-fraction-descent] applied to
$R\subset D_i$ give $f_i\in R[T]$.

11. Fix an algebraic closure $\Omega$ of $K$ with an extending absolute value, and any root
$\beta\in\Omega$ of $f_i$. The polynomial-quotient isomorphism of
[lem-weil-pbc-minimal-polynomial-quotient-field-iso] identifies $L_i=K(x_i)$ with $K[T]/(f_i)$.
Evaluation at $\beta$ gives a field embedding $\sigma:L_i\hookrightarrow\Omega$ sending $x_i$ to
$\beta$. Pulling back the given absolute value along $\sigma$ gives an absolute value on $L_i$
extending that of $K$. By [lem-sfb-algebraic-absolute-value-unique] it equals the norm already
on $L_i$, so $|\beta|=|x_i|=|x|_i$. This includes $x=0$ when $E=F$; in that case the polynomial
is $T$ and the equality is $0=0$.
-/
theorem separable_valued_completion_factors
    (F : Type u) [NontriviallyNormedField F] [IsUltrametricDist F]
    (A : ValuationSubring F) (hA : ∀ a : F, a ∈ A ↔ ‖a‖ ≤ 1)
    (E : Type v) [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ Â : ValuationSubring (Completion F),
      (∀ a : Completion F, a ∈ Â ↔ ‖a‖ ≤ 1) ∧ HenselianLocalRing Â ∧
      (∀ (H : Type (max u w)) [Field H] [Algebra (Completion F) H]
          [FiniteDimensional (Completion F) H],
        ∃ W : ValuationSubring H,
          W.comap (algebraMap (Completion F) H) = Â ∧
          (∀ z : H, z ∈ W ↔ IsIntegral Â z) ∧
          ∀ W' : ValuationSubring H,
            W'.comap (algebraMap (Completion F) H) = Â → W' = W) ∧
      ∃ r : ℕ, 0 < r ∧
        ∃ m : Fin r ≃ MaximalSpectrum (integralClosure A E),
        ∃ W : Fin r → ValuationSubring E,
          (∀ (i : Fin r) (z : E), z ∈ W i ↔
            ∃ c s : integralClosure A E,
              s ∉ (m i).asIdeal ∧ z = (c : E) / (s : E)) ∧
          (∀ V : ValuationSubring E,
            V.comap (algebraMap F E) = A ↔ ∃ i : Fin r, V = W i) ∧
          (∀ i : Fin r,
            ∃ e : IsLocalRing.ResidueField (W i) ≃+*
                ((integralClosure A E) ⧸ (m i).asIdeal),
              ∀ (c : integralClosure A E) (w : W i), (w : E) = (c : E) →
                e (IsLocalRing.residue (W i) w) = Ideal.Quotient.mk (m i).asIdeal c) ∧
          ∃ b : Fin r → AbsoluteValue E ℝ,
            (∀ i : Fin r,
              (∀ a : F, b i (algebraMap F E a) = ‖a‖) ∧
              (∀ x y : E, b i (x + y) ≤ max (b i x) (b i y)) ∧
              (∀ z : E, b i z ≤ 1 ↔ z ∈ W i) ∧
              ∀ b' : AbsoluteValue E ℝ,
                (∀ a : F, b' (algebraMap F E a) = ‖a‖) →
                (∀ z : E, b' z ≤ 1 ↔ z ∈ W i) → b' = b i) ∧
            ∃ j : ∀ i : Fin r, Completion F →+* (b i).Completion,
              (∀ (i : Fin r) (a : Completion F),
                j i a = Completion.map
                  ((WithAbs.equiv (b i)).symm.toRingHom.comp (algebraMap F E)) a) ∧
              (∀ (i : Fin r) (z : (b i).Completion),
                @IsIntegral Â (b i).Completion _ _
                  (((j i).comp Â.subtype).toAlgebra) z ↔ ‖z‖ ≤ 1) ∧
              ∃ Φ : @AlgEquiv (Completion F) (E ⊗[F] Completion F)
                  (∀ i : Fin r, (b i).Completion) _ _ _
                  (Algebra.TensorProduct.rightAlgebra) (RingHom.pi j).toAlgebra,
                (∀ (x : E) (a : Completion F) (i : Fin r),
                  Φ (x ⊗ₜ[F] a) i = (x : (b i).Completion) * j i a) ∧
                ∀ x : E, x ∈ integralClosure A E →
                  IntermediateField.adjoin F {x} = ⊤ →
                  ∃ f : Polynomial A,
                    f.Monic ∧ f.map (algebraMap A F) = minpoly F x ∧
                    ∃ g : Fin r → Polynomial Â,
                      (∀ i : Fin r, (g i).Monic ∧
                        (g i).map (algebraMap Â (Completion F)) =
                          @minpoly (Completion F) (b i).Completion _ _
                            (j i).toAlgebra (x : (b i).Completion) ∧
                        (g i).natDegree =
                          @Module.finrank (Completion F) (b i).Completion _ _
                            (j i).toAlgebra.toModule) ∧
                      (minpoly F x).map (algebraMap F (Completion F)) =
                        ∏ i : Fin r, (g i).map (algebraMap Â (Completion F)) ∧
                      ∀ (Ω : Type (max u w)) [Field Ω] [Algebra (Completion F) Ω]
                          [IsAlgClosure (Completion F) Ω] (c : AbsoluteValue Ω ℝ),
                        (∀ a : Completion F, c (algebraMap (Completion F) Ω a) = ‖a‖) →
                        ∀ (i : Fin r) (β : Ω),
                          Polynomial.aeval β ((g i).map (algebraMap Â (Completion F))) = 0 →
                          c β = b i x := by
  sorry

end WeilConjectures
