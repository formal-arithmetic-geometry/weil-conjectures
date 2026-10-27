/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.RingTheory.CompleteLocalExcellence
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.RingTheory.FiniteRingMapQuasiFinite
import Sheaf.TraceFormula.HenselizationQuasiFiniteRing
import Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.CompletionFiniteExtension
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.RingTheory.QuotientHenselianPair
import Sheaf.TraceFormula.HenselizationQuotientAtPrime
import WeilConjectures.RingTheory.CompleteLocalSubideal
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

/-!
# Finite coefficient change on henselian polynomial cylinders

Source: ILO, Travaux de Gabber, V 1.1.3, 1.2.3 and 3.2.3;
Stacks Project, Algebra, Tags 05WP and 07N9; More on Algebra, Tags 07QU and 07QW
(blueprint: lem-per-finite-coefficient-henselian-cylinder).
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace Algebra

/-- The polynomial structure map of an ordinary henselization at a prime.
Source: ILO V 1.1.3 and Stacks Project, Algebra, Tag 04GQ
(blueprint: lem-per-finite-coefficient-henselian-cylinder). -/
noncomputable def cylinderStructureMap {B : Type u} [CommRing B]
    (p : Ideal (Polynomial B)) [p.IsPrime] (H : Type v) [CommRing H]
    [Algebra (Localization.AtPrime p) H] : Polynomial B →+* H :=
  (algebraMap (Localization.AtPrime p) H).comp
    (algebraMap (Polynomial B) (Localization.AtPrime p))

/-- Finite injective local coefficient changes preserve henselian cylinders and their
canonical maximal-ideal and distinguished-polynomial completions.

Source: ILO V 1.1.3, 1.2.3 and 3.2.3; Stacks Project, Algebra, Tags 05WP and 07N9;
More on Algebra, Tags 07QU and 07QW
(blueprint: lem-per-finite-coefficient-henselian-cylinder).

Proof:
1. A field is Noetherian, local, complete for its zero maximal ideal, and a domain. A complete DVR
has these properties by its definition (every ideal is principal). Apply
[lem-weil-pbc-power-series-noetherian], [lem-weil-pbc-power-series-local-ring],
[lem-weil-pbc-power-series-complete-over-complete-base] and [lem-weil-pbc-power-series-domain] to
each coefficient ring, in $e$ variables and in $e+1$ variables. Thus $D,E,R,R_V$ are complete
Noetherian local domains. Their maximal ideals consist of the series whose constant coefficient
lies in the maximal ideal of the coefficient ring. Regrouping coefficients identifies the
$(e+1)$-variable rings with $D[[T]],E[[T]]$: the coefficient of $u^aT^j$ is the coefficient of
$u^a$ in the $T^j$ coefficient, and the finite convolution formulas for multiplication coincide.
This includes $e=0$.
2. Choose finitely many $\Lambda$-module generators $v_1,\ldots,v_d$ of $V$. For a series
$F=\sum_a c_a u^a\in E$, choose expressions $c_a=\sum_i\lambda_{ia}v_i$. Then $F=\sum_i
v_i(\sum_a\lambda_{ia}u^a)$; equality is coefficientwise. Consequently $E$ is finite over $D$. The
same argument with the additional $T$ exponent shows directly that $R_V$ is finite over $R$.
Grouping the finitely many coefficients of a polynomial shows that the same $v_i$ generate $E[T]$
over $D[T]$. Coefficientwise injectivity gives $D\hookrightarrow E$. Since $\Lambda\to V$ is
local, the constant-coefficient criterion of Step 1 gives $\mathfrak m_E\cap D=\mathfrak m_D$, and
hence $(\mathfrak m_E,T)\cap D[T]=(\mathfrak m_D,T)$.
3. Apply [lem-per-weierstrass-henselian-cylinder] twice, with coefficient ring $D$ and then $E$,
with $r=1$ and input $f=T$. The hypotheses hold by Step 1, and $T$ is a nonunit with nonzero
reduction modulo the coefficient maximal ideal. The henselizations in that statement are exactly
$S$ and $S_V$. Its conclusions give that they are Noetherian local henselian, that their canonical
maximal-ideal completions are $R$ and $R_V$, and that the maps to those completions are faithfully
flat. Only these conclusions are used here; its existential distinguished polynomial is not
identified with the prescribed $g$.
4. By [lem-per-complete-local-excellence], $D$ and $E$ are excellent. Apply
[lem-exc-finite-type-localization-excellent] to their one-variable polynomial rings and the
indicated prime localizations. These localized rings are excellent and therefore quasi-excellent
by [def-exc-excellent-ring]. They are reduced: a polynomial ring over a domain has no zero
divisors by the leading-coefficient formula, and localization at a prime preserves this by the
fraction multiplication rule. Apply the first clause of
[lem-per-henselian-normal-completion-preparation] to each of these reduced quasi-excellent
Noetherian local rings. It gives excellence of $S,S_V$. By
[lem-weil-pbc-faithfully-flat-universally-injective], applied to the base ring as its own module
and its completion map from Step 3, $S\to R$ and $S_V\to R_V$ are injective (identify $A\otimes_A
B$ with $B$ by multiplication). Since the targets are nonzero domains, the sources are nonzero
domains as well.
5. Step 2 makes $D[T]\to E[T]$ finite. By [lem-weil-pbc-finite-ring-map-quasi-finite], it is
finite type and quasi-finite at $(\mathfrak m_E,T)$. This prime lies over $(\mathfrak m_D,T)$ by
the explicit contraction calculation in Step 2. Therefore
[lem-trf-henselization-quasi-finite-ring], applied to these polynomial rings and primes, gives a
finite local canonical map $S\to S_V$. The maps $S\to S_V\to R_V$ and $S\to R\to R_V$ agree: both
are local extensions of $D[T]_{(\mathfrak m_D,T)}\to R_V$, and uniqueness in
[def-weil-pbc-henselization-at-prime] applies because $R_V$ is complete local and hence henselian
by [lem-weil-pbc-complete-pair-henselian].
6. Apply [lem-weil-pbc-finite-algebra-is-integral] to $S\to S_V$. Any prime of $S_V$ lying over
$\mathfrak m_S$ is maximal by [lem-weil-pbc-integral-prime-over-maximal-maximal]. Since $S_V$ is
local, there is precisely one such prime, namely $\mathfrak m_{S_V}$; it lies over $\mathfrak m_S$
since the map is local. Now [lem-weil-pbc-completion-finite-extension], with base $S$, finite
algebra $S_V$ and prime $\mathfrak m_S$, gives $\widehat S\otimes_S S_V\cong\widehat {S_V}$.
Localization at the maximal ideal changes neither local ring, and the product on the right has one
factor. Substitute the canonical identifications of Step 3. Compatibility of the comparison with
the $\widehat S$-algebra and $S_V$-algebra structures makes it send $a\otimes b$ to
$\widehat\varphi(a)$ times the image of $b$, where $\widehat\varphi:\widehat S\to\widehat{S_V}$ is
induced by $\varphi:S\to S_V$ on the quotients $S/\mathfrak m_S^k\to S_V/\mathfrak m_{S_V}^k$.
Under Step 3, $S/\mathfrak m_S^k=R/\mathfrak m_R^k$ and $S_V/\mathfrak m_{S_V}^k=R_V/\mathfrak
m_{R_V}^k$; by Step 5 the map on these quotients is induced by the coefficient inclusion $R\to
R_V$, which is local and so maps $\mathfrak m_R^k$ into $\mathfrak m_{R_V}^k$. Taking the inverse
limit over $k$, $\widehat\varphi$ is the inclusion $R\to R_V$, so the comparison sends $a\otimes
b$ to $ab$. Thus it is exactly the map in the statement, not merely an abstract isomorphism.
Finiteness of $R_V/R$ was already proved by generators in Step 2.
7. Let $g$ be as in the statement. It belongs to $\mathfrak m_S$ and to $\mathfrak m_{S_V}$:
modulo the coefficient maximal ideal its image is $T^n$ with $n>0$. To check the henselian-pair
assertion for either local henselian ring $H=S,S_V$, take a finite $H$-algebra $B$. By
[lem-weil-pbc-finite-over-henselian-local-product], $B$ is a finite product of local $H$-algebras
$B_j$ whose structural maps are local. Then $gB_j$ is contained in the maximal ideal, so
$B_j/gB_j$ is nonzero local. In a local ring an idempotent is $0$ or $1$: from $x(1-x)=0$, one of
$x,1-x$ is a unit. Thus reduction is a bijection on idempotents in every factor, and in their
product, including the empty product. This is precisely [def-weil-pbc-henselian-terminology] for
$(H,gH)$.
8. Write $B=D$ or $E$, $A=B[T]_{(\mathfrak m_B,T)}$, $H=A^h$, and $C=B[[T]]$. For each $N\ge1$,
$g^N$ is monic and reduces to $T^{nN}$. By [lem-per-distinguished-polynomial-quotient],
$B[T]/(g^N)\to C/g^NC$ is the canonical isomorphism. The target is nonzero local because
$g\in\mathfrak m_C$, and is henselian by [lem-weil-pbc-complete-pair-henselian] and
[lem-weil-pbc-quotient-henselian-pair]. The composite $B[T]\to C/g^NC\to C/\mathfrak m_C$ has
kernel $(\mathfrak m_B,T)$. Thus every element outside that prime maps to a unit in $C/g^NC$.
Localizing the displayed isomorphism gives $A/g^NA\cong C/g^NC$. In particular $A/g^NA$ is already
henselian local. For $B=E$, locality of $D\to E$ ensures that all lower coefficients of $g$ lie in
$\mathfrak m_E$, as required.
9. By [lem-trf-henselization-quotient-at-prime], $H/g^NH$ is the ordinary henselization of
$A/g^NA$. The latter is henselian by Step 8, so its henselization map is an isomorphism:
[def-weil-pbc-henselization-at-prime] applied to its identity gives a local retraction, and
uniqueness for maps to its henselization makes the other composite the identity. Consequently the
canonical map $H/g^NH\to C/g^NC$ is an isomorphism, since its composite with $A/g^NA\to H/g^NH$ is
the isomorphism of Step 8. Reduction from $N+1$ to $N$ commutes with these maps, since each sends
the class of $h\in H$ to the class of its fixed image in $C$.
10. By [lem-sbc-complete-local-subideal], the complete Noetherian local ring $C$ is complete also
for $gC\subseteq\mathfrak m_C$. Taking inverse limits of the compatible isomorphisms of Step 9
therefore identifies $\varprojlim_N H/g^NH$ with $C$. The map from $H$ is the canonical map
already used, since every inverse-limit coordinate is its reduction modulo $g^N$. With
$(H,C)=(S,R)$ and $(S_V,R_V)$, this proves the two specified $g$-adic completion identifications.
Their maps are the faithfully flat maps of Step 3, so all clauses hold for the same canonical
maps.
-/
theorem finite_coefficient_henselian_cylinder
    (Λ : Type u) (V : Type v) [CommRing Λ] [CommRing V]
    [IsDomain Λ] [IsDomain V] [IsLocalRing Λ] [IsLocalRing V]
    [Algebra Λ V] [Module.Finite Λ V]
    (hcoeff : (IsField Λ ∧ IsField V) ∨
      (IsDiscreteValuationRing Λ ∧ IsDiscreteValuationRing V ∧
        IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ ∧
        IsAdicComplete (IsLocalRing.maximalIdeal V) V))
    (hinj : Function.Injective (algebraMap Λ V))
    (hloc : IsLocalHom (algebraMap Λ V)) (e : ℕ)
    (p : Ideal (Polynomial (MvPowerSeries (Fin e) Λ))) [p.IsPrime]
    (hp : p = (IsLocalRing.maximalIdeal (MvPowerSeries (Fin e) Λ)).comap
      (Polynomial.evalRingHom 0))
    (q : Ideal (Polynomial (MvPowerSeries (Fin e) V))) [q.IsPrime]
    (hq : q = (IsLocalRing.maximalIdeal (MvPowerSeries (Fin e) V)).comap
      (Polynomial.evalRingHom 0))
    (S : Type w) (S_V : Type z) [CommRing S] [CommRing S_V]
    [Algebra (Localization.AtPrime p) S] [HenselianLocalRing S]
    [Algebra (Localization.AtPrime q) S_V] [HenselianLocalRing S_V]
    (hS : Algebra.IsHenselizationAtPrime' (Polynomial (MvPowerSeries (Fin e) Λ)) p S)
    (hSV : Algebra.IsHenselizationAtPrime' (Polynomial (MvPowerSeries (Fin e) V)) q S_V) :
    IsNoetherianRing (MvPowerSeries (Fin e) Λ) ∧
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin e) Λ)) (MvPowerSeries (Fin e) Λ) ∧
    IsDomain (MvPowerSeries (Fin e) Λ) ∧
    IsNoetherianRing (MvPowerSeries (Fin e) V) ∧
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin e) V)) (MvPowerSeries (Fin e) V) ∧
    IsDomain (MvPowerSeries (Fin e) V) ∧
    IsExcellent S ∧ IsNoetherianRing S ∧ IsDomain S ∧
    IsExcellent S_V ∧ IsNoetherianRing S_V ∧ IsDomain S_V ∧
    ∃ (_ : Algebra S S_V) (_ : Algebra S (PowerSeries (MvPowerSeries (Fin e) Λ)))
      (_ : Algebra S_V (PowerSeries (MvPowerSeries (Fin e) V)))
      (_ : Algebra (PowerSeries (MvPowerSeries (Fin e) Λ))
        (PowerSeries (MvPowerSeries (Fin e) V))),
      Module.Finite S S_V ∧ IsLocalHom (algebraMap S S_V) ∧
      (algebraMap S S_V).comp (cylinderStructureMap p S) =
        (cylinderStructureMap q S_V).comp
          (Polynomial.mapRingHom (MvPowerSeries.map (algebraMap Λ V))) ∧
      (algebraMap S (PowerSeries (MvPowerSeries (Fin e) Λ))).comp (cylinderStructureMap p S) =
        Polynomial.coeToPowerSeries.ringHom ∧
      (algebraMap S_V (PowerSeries (MvPowerSeries (Fin e) V))).comp (cylinderStructureMap q S_V) =
        Polynomial.coeToPowerSeries.ringHom ∧
      algebraMap (PowerSeries (MvPowerSeries (Fin e) Λ)) (PowerSeries (MvPowerSeries (Fin e) V)) =
        PowerSeries.map (MvPowerSeries.map (algebraMap Λ V)) ∧
      IsLocalHom (algebraMap S (PowerSeries (MvPowerSeries (Fin e) Λ))) ∧
      IsLocalHom (algebraMap S_V (PowerSeries (MvPowerSeries (Fin e) V))) ∧
      (algebraMap S (PowerSeries (MvPowerSeries (Fin e) Λ))).FaithfullyFlat ∧
      (algebraMap S_V (PowerSeries (MvPowerSeries (Fin e) V))).FaithfullyFlat ∧
      Module.Finite (PowerSeries (MvPowerSeries (Fin e) Λ))
        (PowerSeries (MvPowerSeries (Fin e) V)) ∧
      ∃ (c : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃+*
          PowerSeries (MvPowerSeries (Fin e) Λ))
        (cV : AdicCompletion (IsLocalRing.maximalIdeal S_V) S_V ≃+*
          PowerSeries (MvPowerSeries (Fin e) V))
        (t : TensorProduct S (PowerSeries (MvPowerSeries (Fin e) Λ)) S_V ≃+* (PowerSeries
            (MvPowerSeries (Fin e) V))),
        (∀ x : S, c (algebraMap S _ x) = algebraMap S (PowerSeries (MvPowerSeries (Fin e) Λ)) x) ∧
        (∀ x : S_V,
          cV (algebraMap S_V _ x) = algebraMap S_V (PowerSeries (MvPowerSeries (Fin e) V)) x) ∧
        (∀ (a : PowerSeries (MvPowerSeries (Fin e) Λ)) (b : S_V),
          t (a ⊗ₜ[S] b) = algebraMap (PowerSeries (MvPowerSeries (Fin e) Λ))
            (PowerSeries (MvPowerSeries (Fin e) V)) a *
            algebraMap S_V (PowerSeries (MvPowerSeries (Fin e) V)) b) ∧
        ∀ (g : Polynomial (MvPowerSeries (Fin e) Λ)) (n : ℕ), 0 < n →
          g.Monic → g.natDegree = n →
          (∀ i : ℕ, i < n → g.coeff i ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin e) Λ)) →
          HenselianRing S (Ideal.span {cylinderStructureMap p S g}) ∧
          HenselianRing S_V
            (Ideal.span {cylinderStructureMap q S_V
              (g.map (MvPowerSeries.map (algebraMap Λ V)))}) ∧
          ∃ (cg : AdicCompletion (Ideal.span {cylinderStructureMap p S g}) S ≃+*
              PowerSeries (MvPowerSeries (Fin e) Λ))
            (cgV : AdicCompletion
              (Ideal.span {cylinderStructureMap q S_V
                (g.map (MvPowerSeries.map (algebraMap Λ V)))}) S_V ≃+*
                  PowerSeries (MvPowerSeries (Fin e) V)),
            (∀ x : S,
              cg (algebraMap S _ x) = algebraMap S (PowerSeries (MvPowerSeries (Fin e) Λ)) x) ∧
            (∀ x : S_V,
              cgV (algebraMap S_V _ x) =
                algebraMap S_V (PowerSeries (MvPowerSeries (Fin e) V)) x) := by
  sorry

end Algebra
