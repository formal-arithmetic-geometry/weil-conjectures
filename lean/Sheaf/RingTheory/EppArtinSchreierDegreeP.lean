/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Sheaf.RingTheory.CompleteDVRFiniteNormalization

/-! # The Artin–Schreier degree-p case of Epp's theorem

Source: Stacks Project, More on Algebra, Tag 09F1, lemma-characteristic-p-case.
(blueprint: lem-sfb-epp-artin-schreier-degree-p)
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y z

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- A separable totally ramified coefficient extension eliminates ramification
in the equal-characteristic degree-p case.

Source: Stacks Project, More on Algebra, Tag 09F1, lemma-characteristic-p-case;
the finite separable conclusion, without the stronger Galois assertion.
(blueprint: lem-sfb-epp-artin-schreier-degree-p)

The lower normalization is `integralClosure A K₁` and the upper one is the integral
closure of `C` in `(M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁)`. The normalization map between
them is the unique ring map `φ` restricting `x ↦ 1 ⊗ x` followed by reduction; it is
quantified with this pin, so contractions are taken along the actual canonical map.

Proof:
1. By the Artin–Schreier presentation, choose $z\in M$ with $M=L[z]$, $\xi=z^p-z\in L$, and
$M\cong L[T]/(T^p-T-\xi)$. Write $\wp(x)=x^p-x$. For every $h\in L$, replacing $z$ by $z+h$
preserves $L[z]=M$ and replaces $\xi$ by $\xi+\wp(h)$, by direct expansion in characteristic
$p$.
   Uses: lem-sfb-epp-artin-schreier-presentation.
2. Apply the complete-DVR normalization node to $B$ and the finite extension $M/L$. Its
uniqueness clause identifies the given local DVR $C$ with the integral closure of $B$ in $M$,
and its other clauses give completeness and module finiteness. Subsequently normalizations over
$B$ and over $C$ in a field extension of $M$ coincide: the normalization $D'$ over $B$ contains
$C$, is integral over $C$ (the same monic equations work), and is integrally closed, so every
element integral over $C$ lies in $D'$. This holds in each factor of a product of fields as
well. Thus the normalizations computed from Artin–Schreier polynomials below are exactly those
of $C$ required in the item.
   Uses: lem-per-complete-dvr-finite-normalization, def-weil-pbc-integral-closure.
3. Put $k=k_A$ and $l=k_B$. The perfect core $\bigcap_m l^{p^m}$ is perfect: the unique $p$th
root in $l$ of an element in this intersection belongs to every $l^{p^m}$, using its $p^{m+1}$th
roots. Hence $k$ is perfect. Choose a uniformizer $\pi$ of $A$, also of $B$. If $\xi\in B$, test
(A) gives $\mathfrak m_BC=\mathfrak m_C$, so the identity extension $K_1=K$ works. Otherwise fix
$N>0$ with $\pi^N\xi\in B$. Apply the compatible-section node to $A/\pi^N A\to B/\pi^N B$; both
maximal ideals are nilpotent and the lower residue is perfect. Lift its upper section to a set
map $\sigma:l\to B$, with $\sigma(0)=0$. It preserves sums and products modulo $\pi^N B$, and
$\sigma(k)\subset A+\pi^N B$. Successively subtract the residue digit and divide by $\pi$ to
write $\xi=\sum_{i=1}^N\sigma(\lambda_i)\pi^{-i}+b$ with $b\in B$. Put $J=\{i:\lambda_i\notin
k\}$ and $I=\{1,\ldots,N\}\setminus J$.
   Uses: lem-sfb-epp-compatible-truncated-coefficients,
lem-sfb-epp-artin-schreier-valuation-tests, def-sc-discrete-valuation-ring.
4. Keep $N$ and these sections fixed. If $j,j'=p^s j$ both belong to $J$ with $s>0$, put
$h=\sum_{a=0}^{s-1}\sigma(\lambda_j^{p^a})\pi^{-jp^a}$ and replace $z$ by $z+h$. Telescoping
gives $\wp(h)=-\sigma(\lambda_j)\pi^{-j}+\sigma(\lambda_j^{p^s})\pi^{-j'}$ modulo $B$. All lift
errors lie in $\pi^N B$ before multiplication by a pole of order at most $j'\leq N$, so they are
integral. Thus $\lambda_j$ becomes zero, $\lambda_{j'}$ becomes $\lambda_{j'}+\lambda_j^{p^s}$,
and the other digits are unchanged. The number of indices outside $k$ strictly decreases: $j$
disappears and only $j'$ can change its membership. Repeating this finite descent leaves either
$J=\varnothing$ or no two indices of $J$ related by multiplication by a positive power of $p$.
This is the finite induction of the source, with the sign of the generator replacement
corrected.
   Uses: .
5. If $J=\varnothing$, choose $a_i\in A$ with $\sigma(\lambda_i)-a_i\in\pi^N B$ and write
$\xi=\alpha+b$, $\alpha=\sum_i a_i\pi^{-i}\in K$, $b\in B$. Reduce the pole order of $\alpha$
over $K$ as follows. If $\alpha=\pi^{-d}u$, $u\in A^\times$, and $p\mid d$, choose $a\in A$ with
$\bar a^p=\bar u$ (perfectness of $k$). Replacing both $\alpha$ by $\alpha-\wp(a\pi^{-d/p})$ and
$z$ by $z-a\pi^{-d/p}$ strictly lowers the pole order, since $u-a^p\in\pi A$ and $d/p<d$. The
nonnegative integer pole order strictly decreases, so eventually either $\alpha\in A$ (then
$\xi\in B$), or its positive pole order is prime to $p$. The unchanged integral remainder is
still denoted $b$.
   Uses: .
6. In the integral case of the preceding step, test (A) again gives the identity weak solution.
Otherwise adjoin $w$ with $w^p-w=\alpha$ to $K$. Test (B) over $A$ makes $K_1=K[w]$ a field of
degree $p$, totally ramified with $A_1$ a complete DVR; it is separable (indeed normal and
separable) by the converse clause of the Artin–Schreier presentation node, since $K_1$ is the
field case of $K[T]/(T^p-T-\alpha)$. The base-change node supplies the field $L_1=L\otimes_KK_1$
and its complete normalization $B_1=B\otimes_AA_1$, with $\mathfrak m_{A_1}B_1=\mathfrak
m_{B_1}$. In $M\otimes_KK_1$, the variable $z-w$ satisfies $\wp(z-w)=b\in B_1$; substituting
$T\mapsto T+w$ identifies this algebra with $L_1[T]/(T^p-T-b)$. This algebra is reduced (the
polynomial has derivative $-1$), hence a finite product of finite field extensions of $L_1$;
applying the complete-DVR normalization node to $B_1$ and each factor, the integral closure $D$
of $B_1$ is the product of the complete DVRs of the factors, so each localization $D_q$ at a
maximal ideal is one of these DVRs. Test (A) over $B_1$ says $\mathfrak m_{B_1}D_q=qD_q$, i.e.
each branch has ramification index one over $B_1$, and hence over $A_1$. Step 2 identifies these
with the required normalizations of $C$. Their maximal ideals contract to $\mathfrak m_{A_1}$,
since a uniformizer of $A_1$ generates each branch maximal ideal. This proves the weak-solution
condition when $J=\varnothing$.
   Uses: lem-sfb-epp-artin-schreier-valuation-tests, lem-sfb-epp-totally-ramified-base-change,
lem-sfb-epp-artin-schreier-presentation, lem-per-complete-dvr-finite-normalization.
7. Now assume $J\ne\varnothing$ after the finite descent. For $j\in J$, take the largest
$r_j\geq0$ such that $\lambda_j\in l^{p^{r_j}}$ and write $\lambda_j=\mu_j^{p^{r_j}}$. This
largest integer exists because $\lambda_j\notin\bigcap_m l^{p^m}=k$; thus $\mu_j\notin l^p$. The
rational numbers $j p^{-r_j}$ are pairwise distinct: equality would make two indices differ by a
power of $p$. Choose $r>\max_j r_j$ so large that every $d_j=j p^{r-r_j}>N$, and put $q=p^r$.
Apply the approximate-root node with $h=N+1>1$ to obtain a separable totally ramified degree-$q$
extension $K_1/K$ with uniformizer $t$ of $A_1$ and $t^q=\pi+\pi^{N+1}a$. The base-change node
gives a field $L_1$, complete DVR $B_1=B\otimes_AA_1$, uniformizer $t$, and residue field $l$,
with $\mathfrak m_{A_1}B_1=\mathfrak m_{B_1}$.
   Uses: lem-sfb-epp-approximate-uniformizer-root, lem-sfb-epp-totally-ramified-base-change.
8. For $1\leq i\leq N$, the identity $t^q=\pi(1+\pi^Na)$ gives $\pi^{-i}=t^{-iq}(1+\pi^Na)^i$,
so $\pi^{-i}-t^{-iq}\in B_1$: its $t$-valuation is at least $q(N-i)\geq0$. For $j\in J$, section
multiplicativity gives $\sigma(\lambda_j)-\sigma(\mu_j)^{p^{r_j}}\in\pi^N B$. For $i\in I$, take
the unique $q$th root $\nu_i\in k$ of $\lambda_i$ and put $x_i=\sigma(\nu_i)$. Then
$\sigma(\lambda_i)-x_i^q\in\pi^N B$. After multiplication by $t^{-iq}$ all these errors are
still integral. Consequently, for some $b_1\in B_1$, $\xi=\sum_{i\in I}(x_i t^{-i})^q+\sum_{j\in
J}(\sigma(\mu_j)t^{-d_j})^{p^{r_j}}+b_1$.
   Uses: .
9. For any $v$ and integer $s\geq0$, $\wp(\sum_{a=0}^{s-1}v^{p^a})=v^{p^s}-v$, with the sum
empty at $s=0$. Subtract from $z$ the sums with $(v,s)=(x_i t^{-i},r)$ for $i\in I$ and
$(v,s)=(\sigma(\mu_j)t^{-d_j},r_j)$ for $j\in J$. The resulting variable $z'$ satisfies
$\wp(z')=\eta=\sum_{i\in I}x_i t^{-i}+\sum_{j\in J}\sigma(\mu_j)t^{-d_j}+b_1$. Substitution in
the polynomial quotient gives $M\otimes_KK_1\cong L_1[T]/(T^p-T-\eta)$. Let $j_0$ maximize
$d_j$. Its maximum is unique, $d_{j_0}>N\geq i$ for $i\in I$, and $p\mid d_{j_0}$ because
$r>r_{j_0}$. Thus $\eta=t^{-d_{j_0}}u$ with $u\in B_1^\times$ and residue $\bar
u=\mu_{j_0}\notin l^p$.
   Uses: .
10. Apply test (C) to the last equation over the complete DVR $B_1$. It says $M\otimes_KK_1$ is
a field and its normalization $C_1$ is a complete DVR with $\mathfrak m_{B_1}C_1=\mathfrak
m_{C_1}$. By the base-change node, $\mathfrak m_{A_1}B_1=\mathfrak m_{B_1}$, hence $\mathfrak
m_{A_1}C_1=\mathfrak m_{C_1}$. Step 2 identifies $C_1$ with the integral closure of $C$ required
in the item; its maximal ideal contracts to the maximal ideal of $A_1$ because $t$ generates
both maximal ideals. The extension $K_1/K$ was finite separable and totally ramified by its
construction. This proves every clause of the weak-solution assertion in the nonempty-$J$ case
as well.
   Uses: lem-sfb-epp-artin-schreier-valuation-tests, lem-sfb-epp-totally-ramified-base-change.
-/
theorem exists_epp_artin_schreier_degree_p
    (p : ℕ) (hp : p.Prime)
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type v) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (C : Type w) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
    (hinjAB : Function.Injective (algebraMap A B))
    (hinjBC : Function.Injective (algebraMap B C))
    (K : Type x) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type y) [Field L] [Algebra B L] [IsFractionRing B L]
    (M : Type z) [Field M] [Algebra C M] [IsFractionRing C M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra B M] [IsScalarTower B C M] [IsScalarTower B L M]
    [Algebra A M] [IsScalarTower A C M] [IsScalarTower A K M]
    [Module.Finite L M] [IsGalois L M]
    (hdegree : Module.finrank L M = p)
    (hindex : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B)
    [CharP (IsLocalRing.ResidueField A) p] [CharP K p]
    (hcore : Set.range (IsLocalRing.ResidueField.map (algebraMap A B)) =
      {b : IsLocalRing.ResidueField B | ∀ n : ℕ, ∃ c : IsLocalRing.ResidueField B,
        c ^ (p ^ n) = b}) :
    ∃ (K₁ : Type (max u v w x y z)) (_ : Field K₁) (_ : Algebra K K₁)
      (_ : Algebra A K₁) (_ : IsScalarTower A K K₁),
      Module.Finite K K₁ ∧ Algebra.IsSeparable K K₁ ∧
      ∃ hDVR : IsDiscreteValuationRing (integralClosure A K₁),
        ∃ hlocal : IsLocalHom (algebraMap A (integralClosure A K₁)),
          Function.Bijective
            (@IsLocalRing.ResidueField.map A (integralClosure A K₁) _ _ _
              hDVR.toIsLocalRing (algebraMap A (integralClosure A K₁)) hlocal) ∧
          Ideal.map (algebraMap A (integralClosure A K₁)) (IsLocalRing.maximalIdeal A) =
            (@IsLocalRing.maximalIdeal (integralClosure A K₁) _ hDVR.toIsLocalRing) ^
              Module.finrank K K₁ ∧
          ∀ (φ : integralClosure A K₁ →+*
              integralClosure C ((M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁))),
            (∀ x : integralClosure A K₁,
              (φ x : (M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁)) =
                Ideal.Quotient.mk (nilradical (M ⊗[K] K₁)) ((1 : M) ⊗ₜ[K] (x : K₁))) →
            ∀ (q : Ideal (integralClosure C ((M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁))))
              [q.IsMaximal],
              (q.comap φ).IsMaximal ∧
              IsDiscreteValuationRing (Localization.AtPrime (q.comap φ)) ∧
              (∃ hdom : IsDomain (Localization.AtPrime q),
                @IsDiscreteValuationRing (Localization.AtPrime q) _ hdom) ∧
              Ideal.map ((algebraMap (integralClosure C ((M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁)))
                  (Localization.AtPrime q)).comp φ) (q.comap φ) =
                Ideal.map (algebraMap (integralClosure C ((M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁)))
                  (Localization.AtPrime q)) q := by
  sorry

end IsDiscreteValuationRing
