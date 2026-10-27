module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompleteLocalQuotient

/-! # Implicit elimination in completed sharp monoid algebras

Source: ILO, Travaux de Gabber, Exposé VI 2.3, printed pp. 72--73.
The unit-twisted implicit elimination is an agent-formulated algebraic refinement
of the completed chart calculation (blueprint: lem-sfb-formal-monoid-implicit-elimination).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace AddMonoidAlgebra

open Classical in
/-- Continuous elimination of unit-twisted formal monoid variables, preserving the
coefficient stratum. The ideals `aS`, `aT`, `aH` are fixed by their displayed equalities.
The inverse-limit topologies have discrete finite-level quotients, and `H/I` has the
quotient topology. Continuity and the monomial formulas characterize the canonical maps.

Source: ILO VI 2.3, printed pp. 72--73; agent-formulated algebraic refinement
(blueprint: lem-sfb-formal-monoid-implicit-elimination).

Proof plan (the cited evaluation node is presently unstated in the published library):
1. Put $A=D[[T]]$, $\mathfrak m_A=(\mathfrak n,Y^t:t\ne0)$, and $\mathfrak m_H=(\mathfrak
n,X^s,Y^t:s,t\ne0)$. Finite generation of $S,T$ gives surjections from finite-variable polynomial
$D$-algebras onto $D[S],D[T],D[S\oplus T]$: send one variable to each chosen monoid generator.
Thus these algebras are Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian]. Their
displayed defining ideals are finitely generated. Their completions, including $A,H$, are
Noetherian by [lem-weil-pbc-adic-completion-noetherian], and complete and separated for the
extended defining ideals by [lem-weil-pbc-adic-completion-mod-ideal]. The same node identifies
their residue quotients with $D/\mathfrak n$, a nonzero field.

2. These defining ideals are the maximal ideals of the completed rings. Indeed, if $f$ has nonzero
residue in $D/\mathfrak n$, choose $d\in D^\times$ with the same residue and write $f=d(1-v)$ with
$v$ in the defining ideal. The partial sums $1+v+\cdots+v^N$ have compatible residues modulo every
power, and their limit is inverse to $1-v$. Thus every element outside the defining ideal is
invertible, while an element inside cannot be invertible because the residue field is nonzero. In
particular $A,H$ are nonzero complete Noetherian local rings.

3. Choose nonzero generators $s_1,\ldots,s_h$ of $S$. For a monoid homomorphism $a:S\to(A,\cdot)$
taking nonzero elements into $\mathfrak m_A$, let $E_a:D[[S]]\to A$ be
[lem-per-formal-monoid-adic-evaluation] with coefficient inclusion. Define
$F(a)(s)=E_a(u(s))Y^{\beta(s)}$. Both factors are multiplicative in $s$, and $F(a)(0)=1$. Since
$\beta(s)\ne0$ for $s\ne0$, $F(a)(s)\in\mathfrak m_A$. If $a(s_i)-b(s_i)\in\mathfrak m_A^r$, the
congruence clause of the cited node gives $E_a(u(s))-E_b(u(s))\in\mathfrak m_A^r$ for every $s$.
Consequently $F(a)(s)-F(b)(s)\in\mathfrak m_A^{r+1}$ for every nonzero $s$. This contraction
preserves every relation of $S$ because its arguments and outputs are monoid homomorphisms.

4. Set $a_0(0)=1$ and $a_0(s)=0$ for $s\ne0$. This is multiplicative: sharpness implies that
$s+s'=0$ only when $s=s'=0$. Define $a_{k+1}=F(a_k)$. First $a_1(s)-a_0(s)\in\mathfrak m_A$ for
every nonzero $s$. Induction using the contraction gives $a_{k+1}(s)-a_k(s)\in\mathfrak
m_A^{k+1}$. For each $s$, its residues modulo $\mathfrak m_A^r$ therefore stabilize as
$k\to\infty$. Completeness gives a unique element $a(s)$ with these stabilized residues. The
identities $a_k(0)=1$ and $a_k(s+s')=a_k(s)a_k(s')$ hold modulo every power at the limit, so
separatedness gives $a(0)=1$ and $a(s+s')=a(s)a(s')$. Also $a(s)\in\mathfrak m_A$ for $s\ne0$.

5. For every $r\ge1$, the construction gives $a(s_i)-a_k(s_i)\in\mathfrak m_A^r$ whenever $k\ge
r$. The congruence clause of [lem-per-formal-monoid-adic-evaluation] shows that
$E_a(u(s))-E_{a_k}(u(s))\in\mathfrak m_A^r$. Passing to stabilized residues in
$a_{k+1}(s)=E_{a_k}(u(s))Y^{\beta(s)}$, and using separatedness, yields the exact fixed-point
equations $a(s)=E_a(u(s))Y^{\beta(s)}$ for every $s$. In particular every nonzero $a(s)$ (with
$s\ne0$) is a multiple of the individual monomial $Y^{\beta(s)}$; no closedness assertion about
the monomial ideal is needed.

6. Apply [lem-per-formal-monoid-adic-evaluation] to $S\oplus T$ and the monoid homomorphism
$(s,t)\mapsto a(s)Y^t$. It gives a continuous $D$-algebra map $\phi:H\to A$ fixing every $Y^t$.
Its restriction to $D[[S]]$ is $E_a$ by uniqueness of evaluation. The fixed-point equations imply
$\phi(X^s-u(s)Y^{\beta(s)})=0$, hence $I\subseteq\ker\phi$. Since $\phi(1)=1$ and $A\ne0$, $I$ is
proper. There is an induced continuous map $\bar\phi:C=H/I\to A$ for the quotient topology.

7. By [lem-weil-pbc-complete-local-quotient], $C$ is a Noetherian complete local ring with maximal
ideal $\mathfrak m_C=\mathfrak m_H/I$. Apply [lem-per-formal-monoid-adic-evaluation] to $T$, with
target $C$ and $t\mapsto\overline{Y^t}$, to obtain the continuous coefficient-and-monomial map
$j:A\to C$ in the statement. The quotient topology on $C$ is precisely its maximal-ideal-adic
topology since the images of $\mathfrak m_H^r$ are $\mathfrak m_C^r$. The composite $\bar\phi j$
fixes $D$ and all $Y^t$, so uniqueness of evaluation gives $\bar\phi j=\operatorname{id}_A$.

8. In $C$, put $b(s)=\overline{X^s}$ and $c(s)=j(a(s))$. These are monoid homomorphisms sending
nonzero elements to $\mathfrak m_C$. Evaluation uniqueness shows that evaluation at $b$ is the
quotient map restricted to $D[[S]]$, and evaluation at $c$ is $jE_a$. Thus the defining relations
and Step 5 give $b(s)=E_b(u(s))\overline{Y^{\beta(s)}}$ and
$c(s)=E_c(u(s))\overline{Y^{\beta(s)}}$. Initially $b(s)-c(s)\in\mathfrak m_C$. If the generator
differences lie in $\mathfrak m_C^r$, the congruence clause of
[lem-per-formal-monoid-adic-evaluation], followed by multiplication by
$\overline{Y^{\beta(s)}}\in\mathfrak m_C$, places all differences in $\mathfrak m_C^{r+1}$.
Induction and separatedness give $b(s)=c(s)$ for every $s$.

9. Let $q:H\to C$ be the quotient map. The continuous maps $q$ and $j\bar\phi q$ agree on $D$, all
$X^s$ by Step 8, and all $Y^t$ by construction. Uniqueness in
[lem-per-formal-monoid-adic-evaluation], now for $S\oplus T$, gives $q=j\bar\phi q$. Surjectivity
of $q$ gives $j\bar\phi=\operatorname{id}_C$. Together with Step 7 this proves that $j$ is a
continuous isomorphism with continuous inverse $\bar\phi$.

10. For $s\ne0$, the inverse sends $\overline{X^s}$ to
$a(s)=E_a(u(s))Y^{\beta(s)}\in(Y^t:t\ne0)A$, since $\beta(s)\ne0$. It fixes every coefficient
$d\in D$. Reducing modulo the nonzero $T$-monomials therefore leaves $d$ unchanged and kills each
nonzero $X$-monomial. Equivalently, compose with the continuous augmentation $A\to D$, given by
evaluation at $Y^0=1$ and $Y^t=0$ for $t\ne0$; the evaluation node applies because $D$ is
$\mathfrak n$-adically complete. This composite is the identity on $D$, as required.
-/
theorem exists_formalMonoid_implicitElimination (D : Type u) [CommRing D] [IsNoetherianRing D]
    [IsLocalRing D] [IsAdicComplete (IsLocalRing.maximalIdeal D) D] (S : Type v) [AddCommMonoid S]
    (T : Type w) [AddCommMonoid T] (hS : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative
    S)) (hT : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative T)) (hsharpS : ∀ s : S,
    IsUnit (Multiplicative.ofAdd s) → s = 0) (hsharpT : ∀ t : T, IsUnit (Multiplicative.ofAdd t) →
    t = 0) (β : S →+ T) (hβ : ∀ s : S, β s = 0 → s = 0) (aS : Ideal (AddMonoidAlgebra D S)) (haS :
    aS = Ideal.map (algebraMap D (AddMonoidAlgebra D S)) (IsLocalRing.maximalIdeal D) ⊔ Ideal.span
    {z | ∃ s : S, s ≠ 0 ∧ z = single s (1 : D)}) (aT : Ideal (AddMonoidAlgebra D T)) (haT : aT =
    Ideal.map (algebraMap D (AddMonoidAlgebra D T)) (IsLocalRing.maximalIdeal D) ⊔ Ideal.span {z |
    ∃ t : T, t ≠ 0 ∧ z = single t (1 : D)}) (aH : Ideal (AddMonoidAlgebra D (S × T))) (haH : aH =
    Ideal.map (algebraMap D (AddMonoidAlgebra D (S × T))) (IsLocalRing.maximalIdeal D) ⊔
    Ideal.span {z | ∃ p : S × T, p ≠ 0 ∧ z = single p (1 : D)}) (u : Multiplicative S →*
    (AdicCompletion aS (AddMonoidAlgebra D S))ˣ) : ∃ ι : AdicCompletion aS (AddMonoidAlgebra D S)
    →+* AdicCompletion aH (AddMonoidAlgebra D (S × T)), @Continuous _ _ (⨅ n : ℕ,
    TopologicalSpace.induced (AdicCompletion.evalₐ aS n) ⊥) (⨅ n : ℕ, TopologicalSpace.induced
    (AdicCompletion.evalₐ aH n) ⊥) ι ∧ (∀ (s : S) (d : D), ι (AdicCompletion.of aS
    (AddMonoidAlgebra D S) (single s d)) = AdicCompletion.of aH (AddMonoidAlgebra D (S × T))
    (single (s, 0) d)) ∧ ∃ I : Ideal (AdicCompletion aH (AddMonoidAlgebra D (S × T))), I =
    Ideal.span {z | ∃ s : S, z = AdicCompletion.of aH (AddMonoidAlgebra D (S × T)) (single (s, 0)
    1) - ι (u (Multiplicative.ofAdd s) : AdicCompletion aS (AddMonoidAlgebra D S)) *
    AdicCompletion.of aH (AddMonoidAlgebra D (S × T)) (single (0, β s) 1)} ∧ ∃ e : AdicCompletion
    aT (AddMonoidAlgebra D T) ≃+* (AdicCompletion aH (AddMonoidAlgebra D (S × T)) ⧸ I), (∀ (t : T)
    (d : D), e (AdicCompletion.of aT (AddMonoidAlgebra D T) (single t d)) = Ideal.Quotient.mk I
    (AdicCompletion.of aH (AddMonoidAlgebra D (S × T)) (single (0, t) d))) ∧ @Continuous _ _ (⨅ n
    : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ aT n) ⊥) (TopologicalSpace.coinduced
    (Ideal.Quotient.mk I) (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ aH n) ⊥)) e ∧
    @Continuous _ _ (TopologicalSpace.coinduced (Ideal.Quotient.mk I) (⨅ n : ℕ,
    TopologicalSpace.induced (AdicCompletion.evalₐ aH n) ⊥)) (⨅ n : ℕ, TopologicalSpace.induced
    (AdicCompletion.evalₐ aT n) ⊥) e.symm ∧ (∀ s : S, s ≠ 0 → e.symm (Ideal.Quotient.mk I
    (AdicCompletion.of aH (AddMonoidAlgebra D (S × T)) (single (s, 0) 1))) ∈ Ideal.span {z | ∃ t :
    T, t ≠ 0 ∧ z = AdicCompletion.of aT (AddMonoidAlgebra D T) (single t 1)}) ∧ ∃ ε :
    AdicCompletion aT (AddMonoidAlgebra D T) →+* D, @Continuous _ _ (⨅ n : ℕ,
    TopologicalSpace.induced (AdicCompletion.evalₐ aT n) ⊥) (IsLocalRing.maximalIdeal
    D).adicTopology ε ∧ (∀ (t : T) (d : D), ε (AdicCompletion.of aT (AddMonoidAlgebra D T) (single
    t d)) = if t = 0 then d else 0) ∧ ∀ d : D, ε (e.symm (Ideal.Quotient.mk I (algebraMap D
    (AdicCompletion aH (AddMonoidAlgebra D (S × T))) d))) = d := by
  sorry

end AddMonoidAlgebra
