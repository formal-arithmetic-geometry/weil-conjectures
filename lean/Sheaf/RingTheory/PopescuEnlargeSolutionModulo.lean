/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.RingTheory.PopescuSolutionModulo
import Sheaf.RingTheory.ArtinianSeparableResidueLift
import Sheaf.RingTheory.ArtinianTranscendentalLocalization
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Enlarging a solution modulo a prime power

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FI (lemma-enlarge-solution-modulo),
Section 07FF (blueprint: lem-weil-pbc-popescu-enlarge-solution-modulo).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

private theorem pow_eq_of_residue_eq
    {S : Type u} [CommRing S] [IsLocalRing S] [IsArtinianRing S]
    (p : ℕ) [Fact p.Prime] [CharP S p] {x y : S}
    (h : IsLocalRing.residue S x = IsLocalRing.residue S y) :
    ∃ e : ℕ, x ^ p ^ e = y ^ p ^ e := by
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal S).mp inferInstance
  have hmem : x - y ∈ IsLocalRing.maximalIdeal S := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, h, sub_self]
  have hbound : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have hz := Ideal.pow_eq_zero_of_mem hN hbound hmem
  rw [sub_pow_char_pow x y N] at hz
  exact ⟨N, sub_eq_zero.mp hz⟩

private theorem exists_separable_pow
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    (p : ℕ) [Fact p.Prime] [CharP F p] {a : E} (ha : IsAlgebraic F a) :
    ∃ e : ℕ, IsSeparable F (a ^ p ^ e) := by
  let K := IntermediateField.adjoin F {a}
  have : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional ha.isIntegral
  let aK : K := ⟨a, IntermediateField.mem_adjoin_simple_self F a⟩
  obtain ⟨e, b, hb⟩ := IsPurelyInseparable.pow_mem (separableClosure F K) p aK
  have hsep : IsSeparable F (aK ^ p ^ e) := by
    rw [← hb]
    exact (Algebra.IsSeparable.isSeparable F b).map
      (IsScalarTower.toAlgHom F (separableClosure F K) K)
        (IsScalarTower.toAlgHom F (separableClosure F K) K).injective
  refine ⟨e, ?_⟩
  exact hsep.map K.val K.val.injective

private theorem essentiallySmooth_of_smooth
    {R : Type u} [CommRing R] (S : Type (max u v)) [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] : Algebra.EssentiallySmooth R S := by
  refine ⟨S, inferInstance, inferInstance, inferInstance, ⊥, ?_⟩
  exact ⟨(IsLocalization.atUnits S (⊥ : Submonoid S) (S := Localization (⊥ : Submonoid S))
    (bot_le : (⊥ : Submonoid S) ≤ IsUnit.submonoid S)).restrictScalars R⟩


set_option linter.unusedVariables false in
/-- Enlarge the given local Artinian factorization so that a positive power of the specified
unit lies in its image. Source: Stacks Project, Smoothing Ring Maps, Lemma 07FI
(blueprint: lem-weil-pbc-popescu-enlarge-solution-modulo).

Proof, following the node's split of Stacks 07FI:
1. (Setup.) Write $\bar\Lambda=\Lambda_{\mathfrak q}/\mathfrak q^n\Lambda_{\mathfrak q}$,
$\psi:D\to\bar\Lambda$ for the given flat local homomorphism, $\mathfrak m_D$ and $F=D/\mathfrak
m_D$ for the maximal ideal and residue field of $D$. $\Lambda_{\mathfrak q}$ is local with maximal
ideal $\mathfrak q\Lambda_{\mathfrak q}$ and residue field $\kappa(\mathfrak q)$
[def-weil-pbc-localization-at-prime], so $\bar\Lambda$ is local with maximal ideal $\mathfrak
m_{\bar\Lambda}=\mathfrak q\bar\Lambda$, $\mathfrak m_{\bar\Lambda}^n=0$, and residue field
$\kappa(\mathfrak q)$. Since $\psi$ is local it induces a field homomorphism $F\to\kappa(\mathfrak
q)$, through which we regard $F\subseteq\kappa(\mathfrak q)$ (Stacks: $k\subset
F\subset\kappa(\mathfrak q)$). $\bar\Lambda$ is a $k$-algebra, so $p\cdot1=0$ in $\bar\Lambda$.
Let $\bar\lambda$ be the image of $\lambda$ in $\bar\Lambda$ and $\alpha\in\kappa(\mathfrak q)$
the image of $\lambda$; $\alpha\neq0$ as $\lambda\notin\mathfrak q$. By
[lem-weil-pbc-artinian-local-noetherian-nilpotent] $D$ and $\bar\Lambda$ are Noetherian and
$\mathfrak m_D$ is nilpotent; by [lem-weil-pbc-artinian-local-unique-prime] their only primes are
their maximal ideals. Exactly one of three cases occurs: $\alpha\in F$; $\alpha$ algebraic over
$F$ but not in $F$; $\alpha$ transcendental over $F$ (not a root of a nonzero polynomial over $F$
[def-weil-algebraic-element]). Uses: def-weil-pbc-localization-at-prime,
lem-weil-pbc-artinian-local-noetherian-nilpotent, lem-weil-pbc-artinian-local-unique-prime,
def-weil-algebraic-element.

2. (Claim, the first part of the Stacks argument.) Let $D_1$ be a local ring with residue field
$F_1$ and $\psi_1:D_1\to\bar\Lambda$ a local homomorphism, and let $\mu\in\bar\Lambda$ have
residue $\mu_0\in\kappa(\mathfrak q)$ with $\mu_0\neq0$ and $\mu_0$ in the image of
$F_1\to\kappa(\mathfrak q)$. Then $\mu^{q}\in\psi_1(D_1)$ for every power $q=p^e$ of $p$ with
$q\ge n$. Proof: choose $x\in D_1$ whose residue maps to $\mu_0^{-1}$; then $x\notin\mathfrak
m_{D_1}$, so $x$ is a unit of $D_1$, and $\varepsilon=\psi_1(x)\mu-1$ has residue $0$, i.e.
$\varepsilon\in\mathfrak m_{\bar\Lambda}$ (Stacks: $x\bar\lambda=1\bmod\mathfrak q$). As $p=0$ in
$\bar\Lambda$, $(a+b)^p=a^p+b^p$, hence by induction on $e$
$(1+\varepsilon)^{p^e}=1+\varepsilon^{p^e}$, and $\varepsilon^{q}\in\mathfrak
m_{\bar\Lambda}^{q}\subseteq\mathfrak m_{\bar\Lambda}^n=0$. So $(\psi_1(x)\mu)^q=1$ and
$\mu^q=\psi_1(x)^{-q}=\psi_1(x^{-q})\in\psi_1(D_1)$. (Stacks says '$q$ divisible by $p$'; what is
needed is a $p$-power $q\ge n$.) Uses: def-weil-pbc-localization-at-prime.

3. (Case $\alpha\in F$.) Take $D'=D$ with the identity $D\to D$ and $D'\to\bar\Lambda$ equal to
$\psi$ (flat by hypothesis). The identity is $D\to D[y_1,\dots,y_0]=D$, smooth by
[lem-weil-pbc-polynomial-ring-smooth] with $n=0$, hence essentially smooth (take $P=D$, $S=\{1\}$
in [def-weil-pbc-essentially-smooth-ring-map]). By the Claim (step 2) with $D_1=D$,
$\mu=\bar\lambda$, $\mu_0=\alpha$, the image of $\lambda^q$ lies in $\psi(D)$ for $q=p^e\ge n$.
Uses: lem-weil-pbc-polynomial-ring-smooth, def-weil-pbc-essentially-smooth-ring-map.

4. (Case $\alpha$ transcendental: $D[\bar\lambda]$ is a polynomial algebra over $D$; Stacks: 'this
works because $D[\bar\lambda]$ is in fact a polynomial algebra over $D$ in this case', written
out.) Let $\theta:D[t]\to\bar\Lambda$ be the $D$-algebra map $t\mapsto\bar\lambda$. The $F$-vector
space $V=\bar\Lambda/\mathfrak m_D\bar\Lambda$ maps $F$-linearly onto $\kappa(\mathfrak q)$ (as
$\mathfrak m_D\bar\Lambda\subseteq\mathfrak m_{\bar\Lambda}$), sending the class $v_i$ of
$\bar\lambda^i$ to $\alpha^i$; the $\alpha^i$ ($i\ge0$) are $F$-linearly independent because
$\alpha$ is transcendental over $F$, hence so are the $v_i$. Extend $(v_i)_{i\ge0}$ to an
$F$-basis $(v_i)_{i\ge0}\cup(w_\beta)_{\beta\in B}$ of $V$ and lift each $w_\beta$ to
$\bar\Lambda$. $D$ is local with nilpotent maximal ideal (step 1) and $\bar\Lambda$ is a flat
$D$-module, so by [lem-weil-pbc-local-artinian-basis-when-flat] the family
$(\bar\lambda^i)_{i\ge0}$ together with the lifts is a $D$-basis of $\bar\Lambda$. In particular
the $\bar\lambda^i$ are $D$-linearly independent, i.e. $\theta$ is injective:
$D[\bar\lambda]=\theta(D[t])\cong D[t]$. Uses: lem-weil-pbc-local-artinian-basis-when-flat,
def-weil-pbc-flat-ring-map.

5. (Case $\alpha$ transcendental: the ring $D'$.) Let $\mathfrak m=\theta^{-1}(\mathfrak
m_{\bar\Lambda})$ (Stacks: $\mathfrak m=D[\bar\lambda]\cap\mathfrak q\bar\Lambda$). Since $\psi$
is local, $\mathfrak m_D[t]\subseteq\mathfrak m$, and modulo $\mathfrak m_D[t]$ the map
$D[t]\to\kappa(\mathfrak q)$ is $F[t]\to\kappa(\mathfrak q)$, $t\mapsto\alpha$, which is injective
as $\alpha$ is transcendental; hence $\mathfrak m=\mathfrak m_D[t]$, a prime ideal
($D[t]/\mathfrak m=F[t]$ is a domain). Set $D'=D[t]_{\mathfrak m}$
[def-weil-pbc-localization-at-prime] (Stacks: $D'=(D[\bar\lambda])_{\mathfrak m}$, the same ring
by step 4). $D[t]$ is Noetherian [lem-weil-pbc-finite-type-algebra-noetherian] and so is $D'$
[lem-weil-pbc-localization-noetherian]; $D'$ is local with maximal ideal $\mathfrak mD'=\mathfrak
m_DD'$, which is nilpotent because $\mathfrak m_D$ is (step 1), so $D'$ is an Artinian local ring
by [lem-weil-pbc-noetherian-local-quotient-artinian-local] (with $K=0$); its residue field is
$D'/\mathfrak m_DD'=F[t]_{(0)}=F(t)$. $D\to D[t]$ is smooth [lem-weil-pbc-polynomial-ring-smooth],
so $D\to D'$, a localization of it, is essentially smooth
[def-weil-pbc-essentially-smooth-ring-map], and it is local ($\mathfrak m_D\mapsto\mathfrak
m_DD'$). Every $s\in D[t]\setminus\mathfrak m$ has $\theta(s)\notin\mathfrak m_{\bar\Lambda}$, a
unit of the local ring $\bar\Lambda$, so $\theta$ extends uniquely to $\psi':D'\to\bar\Lambda$
[def-weil-pbc-localization-at-prime]; $\psi'$ is local ($\psi'^{-1}(\mathfrak
m_{\bar\Lambda})=\mathfrak mD'$), its composite with $D\to D'$ is $\psi$, and
$\psi'(t/1)=\bar\lambda$. Uses: def-weil-pbc-localization-at-prime,
lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian,
lem-weil-pbc-noetherian-local-quotient-artinian-local, lem-weil-pbc-polynomial-ring-smooth,
def-weil-pbc-essentially-smooth-ring-map.

6. (Case $\alpha$ transcendental: flatness and conclusion.) Apply
[lem-weil-pbc-criterion-flatness-fibre-noetherian] to $R=D$, $S=D'$, $S'=M=\bar\Lambda$: these are
Noetherian local rings (steps 1 and 5) and $D\to D'\to\bar\Lambda$ are local homomorphisms; $M$ is
finitely generated (by $1$) and nonzero over $\bar\Lambda$; $M/\mathfrak m_DM$ is a module over
the field $D'/\mathfrak m_DD'=F(t)$, hence free and so flat [def-weil-pbc-flat-ring-map]; $M$ is
flat over $D$ by hypothesis. Hence $\psi':D'\to\bar\Lambda$ is flat. With $q=1$,
$\bar\lambda=\psi'(t/1)$ lies in the image of $D'$. Uses:
lem-weil-pbc-criterion-flatness-fibre-noetherian, def-weil-pbc-flat-ring-map.

7. (Case $\alpha$ algebraic: a $p$-power making $\alpha$ separable; Stacks cites Fields, Section
'algebraic' (Tag 037H, a label no longer in fields.tex).) $F(\alpha)/F$ is algebraic, so by
[lem-weil-pbc-separable-first-purely-inseparable] there is $e\ge0$ with $\beta:=\alpha^q$,
$q=p^e$, separable over $F$ [def-weil-pbc-separable-algebraic-extension]; let $\bar g\in F[T]$ be
its minimal polynomial, separable and irreducible, so $F(\beta)\cong F[T]/(\bar g)$ is a finite
field extension of $F$ inside $\kappa(\mathfrak q)$. The elements of $F(\beta)$ separable over $F$
form a subfield containing $F$ and $\beta$ [lem-weil-pbc-separable-first-purely-inseparable], so
$F(\beta)/F$ is finite and separable algebraic; hence
$\operatorname{Spec}F(\beta)\to\operatorname{Spec}F$ is etale
[lem-weil-pbc-finite-separable-extension-etale], i.e. $F(\beta)$ is a finite etale $F$-algebra.
Uses: lem-weil-pbc-separable-first-purely-inseparable, def-weil-pbc-separable-algebraic-extension,
lem-weil-pbc-finite-separable-extension-etale.

8. (Case $\alpha$ algebraic: the finite etale extension $D\to D'$.) $D$ and $\bar\Lambda$ are
local rings whose only prime is the maximal ideal (step 1), hence henselian
[lem-weil-pbc-local-dimension-zero-henselian] (Stacks: Algebra, Lemma 06RS). By the essential
surjectivity in [lem-weil-pbc-henselian-finite-etale-equivalence] (Stacks: Algebra, Lemma 04GK)
applied to $D$ and the finite etale $F$-algebra $F(\beta)$ (step 7) there is a finite etale
$D$-algebra $D'$ with an $F$-algebra isomorphism $D'/\mathfrak m_DD'\cong F(\beta)$. $D'$ is a
finite $D$-algebra, hence of finite type and Noetherian
[lem-weil-pbc-finite-type-algebra-noetherian]; $\mathfrak m_DD'$ is nilpotent (step 1) and
$D'/\mathfrak m_DD'$ is a field, so every element outside $\mathfrak m_DD'$ is a unit modulo a
nilpotent ideal, hence a unit: $D'$ is local with maximal ideal $\mathfrak m_DD'$, residue field
$F(\beta)$, and Artinian [lem-weil-pbc-noetherian-local-quotient-artinian-local] (with $K=0$).
$D\to D'$ is local, and it is etale, hence essentially smooth
[def-weil-pbc-essentially-smooth-ring-map] (remark (a) there). Uses:
lem-weil-pbc-local-dimension-zero-henselian, lem-weil-pbc-henselian-finite-etale-equivalence,
lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-noetherian-local-quotient-artinian-local, def-weil-pbc-essentially-smooth-ring-map.

9. (Case $\alpha$ algebraic: the factorization $D'\to\bar\Lambda$; Stacks: 'since $\bar\Lambda$ is
henselian and $F(\alpha^q)$ is contained in its residue field we can find a factorization',
written out.) Let $B=D'\otimes_D\bar\Lambda$; $\bar\Lambda\to B$ is etale
[lem-weil-pbc-etale-ring-base-change]. Its fibre is $B/\mathfrak
m_{\bar\Lambda}B=D'\otimes_D\kappa(\mathfrak q)=(D'/\mathfrak m_DD')\otimes_F\kappa(\mathfrak
q)\cong F(\beta)\otimes_F\kappa(\mathfrak q)\cong\kappa(\mathfrak q)[T]/(\bar g)$, and $\bar
g(\alpha^q)=0$ in $\kappa(\mathfrak q)$, so $T\mapsto\alpha^q$ gives a surjective
$\kappa(\mathfrak q)$-algebra map $\pi:B\to\kappa(\mathfrak q)$, $b\otimes1\mapsto$ (image of $b$
in $F(\beta)\subseteq\kappa(\mathfrak q)$). Its kernel $\mathfrak q'$ is a prime of $B$ over
$\mathfrak m_{\bar\Lambda}$ with $\kappa(\mathfrak q)\to\kappa(\mathfrak q')$ an isomorphism. As
$\bar\Lambda$ is henselian (step 8), [lem-weil-pbc-henselian-etale-retraction] gives a
$\bar\Lambda$-algebra map $\sigma:B\to\bar\Lambda$ with $\sigma^{-1}(\mathfrak
m_{\bar\Lambda})=\mathfrak q'$. Put $\psi'(b)=\sigma(b\otimes1)$, $\psi':D'\to\bar\Lambda$. For
$d\in D$, $\psi'(d)=\sigma(1\otimes\psi(d))=\psi(d)$: $\psi'$ factors $\psi$. Reducing $\sigma$
modulo $\mathfrak m_{\bar\Lambda}$ gives a $\kappa(\mathfrak q)$-algebra map $B/\mathfrak
q'\to\kappa(\mathfrak q)$, necessarily the inverse of the isomorphism induced by $\pi$; so
$\psi'(b)\bmod\mathfrak m_{\bar\Lambda}=\pi(b\otimes1)$, and the residue field $F(\beta)$ of $D'$
maps onto $F(\beta)=F(\alpha^q)\subseteq\kappa(\mathfrak q)$; in particular $\alpha^q$ is in its
image. $\psi'^{-1}(\mathfrak m_{\bar\Lambda})$ is a prime of $D'$, hence $\mathfrak m_DD'$
[lem-weil-pbc-artinian-local-unique-prime]: $\psi'$ is local. Uses:
lem-weil-pbc-etale-ring-base-change, lem-weil-pbc-henselian-etale-retraction,
lem-weil-pbc-local-dimension-zero-henselian, lem-weil-pbc-artinian-local-unique-prime.

10. (Case $\alpha$ algebraic: flatness and conclusion.) As in step 6,
[lem-weil-pbc-criterion-flatness-fibre-noetherian] applied to $D\to D'\to\bar\Lambda$ and
$M=\bar\Lambda$ (Noetherian local rings and local maps by steps 1, 8, 9; $M/\mathfrak m_DM$ is a
module over the field $D'/\mathfrak m_DD'\cong F(\beta)$, hence flat [def-weil-pbc-flat-ring-map];
$M$ flat over $D$) shows that $\psi'$ is flat. Now apply the Claim (step 2) to $D_1=D'$,
$\psi_1=\psi'$ and $\mu=\bar\lambda^q$, whose residue $\alpha^q\neq0$ lies in the image of the
residue field of $D'$ (step 9): $(\bar\lambda^q)^{q'}\in\psi'(D')$ for a $p$-power $q'\ge n$. So
the integer $qq'>0$ and the factorization $D\to D'\to\bar\Lambda$ (step 8: $D\to D'$ essentially
smooth; $D'\to\bar\Lambda$ flat) satisfy the lemma. Together with steps 3 and 6 this covers all
three cases of step 1. Uses: lem-weil-pbc-criterion-flatness-fibre-noetherian,
def-weil-pbc-flat-ring-map.
-/
theorem exists_essentiallySmooth_artinian_enlargement
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
    (ψ : Localization.AtPrime (q.comap φ.toRingHom) →+* Localization.AtPrime q)
    (hψ : ψ.comp (algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (q.comap φ.toRingHom))) =
      (algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom)
    (hideal : q.map (algebraMap Λ (Localization.AtPrime q)) =
      (q.comap φ.toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom))
    (hflat : ψ.Flat)
    [IsLocalRing (Localization.AtPrime (q.comap φ.toRingHom) ⧸
      ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n)]
    [IsArtinianRing (Localization.AtPrime (q.comap φ.toRingHom) ⧸
      ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n)]
    [IsLocalRing (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)]
    [IsArtinianRing (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)]
    (D : Type w) [CommRing D] [IsLocalRing D] [IsArtinianRing D]
    [Algebra (Localization.AtPrime (q.comap φ.toRingHom) ⧸
      ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) D]
    (g : D →+* (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))
    [IsLocalHom (algebraMap (Localization.AtPrime (q.comap φ.toRingHom) ⧸
      ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) D)]
    [IsLocalHom g]
    (hsmooth : EssentiallySmooth (Localization.AtPrime (q.comap φ.toRingHom) ⧸
      ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) D)
    (hgflat : g.Flat)
    (hfactor : (g.comp (algebraMap (Localization.AtPrime (q.comap φ.toRingHom) ⧸
      ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) D)).comp
        (Ideal.Quotient.mk (((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n)) =
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)).comp ψ)
    (l : Λ) (hl : l ∉ q) :
    ∃ (r : ℕ), 0 < r ∧
      ∃ (D' : Type (max u v w)) (_ : CommRing D') (_ : Algebra D D')
        (g' : D' →+* (Localization.AtPrime q ⧸
          (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)),
        IsLocalRing D' ∧ IsArtinianRing D' ∧
        IsLocalHom (algebraMap D D') ∧ IsLocalHom g' ∧
        EssentiallySmooth D D' ∧ g'.Flat ∧
        g'.comp (algebraMap D D') = g ∧
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))
          ((algebraMap Λ (Localization.AtPrime q)) (l ^ r)) ∈ Set.range g' := by
  classical
  let S := Localization.AtPrime q ⧸
    (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n
  let x : S := Ideal.Quotient.mk
    ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
    (algebraMap Λ (Localization.AtPrime q) l)
  let : Algebra D S := g.toAlgebra
  have : IsLocalHom (algebraMap D S) := ‹IsLocalHom g›
  have hprime : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right hp.ne'
  have : Fact p.Prime := ⟨hprime⟩
  have : CharP S p :=
    charP_of_injective_algebraMap (algebraMap k S).injective p
  have : CharP (IsLocalRing.ResidueField S) p :=
    charP_of_injective_algebraMap (algebraMap k (IsLocalRing.ResidueField S)).injective p
  have : CharP (IsLocalRing.ResidueField D) p :=
    (IsLocalRing.ResidueField.map g).charP (IsLocalRing.ResidueField.map g).injective p
  by_cases ha : IsAlgebraic (IsLocalRing.ResidueField D) (IsLocalRing.residue S x)
  · obtain ⟨e, hsep⟩ := exists_separable_pow p ha
    obtain ⟨D', hD', hDD', g', hlocal, hart, hmap, hg', het, hfin, hflat', hcomp,
      d, hd⟩ := exists_finiteEtale_artinian_residue_lift.{w, v, u}
        D S hgflat ((IsLocalRing.residue S x) ^ p ^ e) hsep
    let : CommRing D' := hD'
    let : Algebra D D' := hDD'
    have : IsLocalRing D' := hlocal
    have : IsArtinianRing D' := hart
    have : IsLocalHom (algebraMap D D') := hmap
    have : IsLocalHom g' := hg'
    have : Etale D D' := het
    obtain ⟨f, hf⟩ := pow_eq_of_residue_eq p
      (x := g' d) (y := x ^ p ^ e) (by simpa only [map_pow] using hd)
    refine ⟨p ^ e * p ^ f, Nat.mul_pos (pow_pos hp e) (pow_pos hp f),
      D', hD', hDD', g', hlocal, hart, hmap, hg',
      essentiallySmooth_of_smooth D', hflat', hcomp, ?_⟩
    refine ⟨d ^ p ^ f, ?_⟩
    simpa only [map_pow, ← pow_mul] using hf
  · obtain ⟨hlocal, hart, hmap, hsmooth', g', hg', hflat', hcomp, hx⟩ :=
      artinian_transcendental_polynomial_localization.{w, v, u} D S hgflat x ha
    refine ⟨1, Nat.zero_lt_one, _, inferInstance, inferInstance, g',
      hlocal, hart, hmap, hg', hsmooth', hflat', hcomp, ?_⟩
    simpa only [pow_one] using hx

end Algebra
