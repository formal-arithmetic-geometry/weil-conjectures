module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Ideal
import Sheaf.RingTheory.CompleteLocalExcellence
import Sheaf.RingTheory.CompleteDVRFiniteNormalization
import WeilConjectures.RingTheory.CohenRingsExist
import WeilConjectures.RingTheory.CohenRing
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import WeilConjectures.RingTheory.NagataOfCompleteLocal
import WeilConjectures.RingTheory.CohenRingModPowFormallySmooth
import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.RingTheory.JapaneseDomain
import Sheaf.RingTheory.ExcellentRing
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Galois Epp preparation with reduced special fibre

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IV,
4.2.3--4.2.5 and 4.3.3--4.3.7, pp. 58--61
(blueprint: lem-per-galois-epp-reduced-fibre-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsLocalRing

/-- A complete Noetherian normal local domain of mixed characteristic has a finite
Galois cover with an equivariant complete coefficient DVR and reduced special fibre.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IV,
4.2.3--4.2.5 and 4.3.3--4.3.7, pp. 58--61
(blueprint: lem-per-galois-epp-reduced-fibre-cover).

Proof (the accepted DAG proof, with its cited inputs):
1. Put $k=A/\mathfrak m$ and $k_*=\bigcap_{n\ge0}k^{p^n}$. This intersection is a field, and is
   perfect: the unique $p$th root of an element in all $k^{p^n}$ again lies in all $k^{p^n}$.
   Choose a Cohen ring $W_0$ with residue field $k_*$ by [lem-weil-pbc-cohen-rings-exist], and use
   [def-weil-pbc-cohen-ring] for completeness, the DVR property, and uniformizer $p$. Construct
   compatible maps $g_n:W_0/p^n\to A/\mathfrak m^n$ starting with the given inclusion $k_*\to k$.
   Given $g_n$, apply [lem-weil-pbc-cohen-ring-mod-pn-formally-smooth] with exponent $n+1$, target
   $A/\mathfrak m^{n+1}$ and square-zero ideal $\mathfrak m^n/\mathfrak m^{n+1}$ to lift the
   composite from $W_0/p^{n+1}$. Here $p^{n+1}=0$ in the target since $p\in\mathfrak m$.
   Completeness [def-weil-pbc-adically-complete-ring] gives a ring map $W_0\to A$ from these
   compatible maps. It is local because its residue map is injective. It is injective: every
   nonzero element of $W_0$ is $up^a$ by [lem-weil-pbc-dvr-unit-times-uniformizer-power], with $u$
   a unit, and $p^a\ne0$ in the characteristic-zero domain $A$.
2. Let $P_1,\ldots,P_r$ be the minimal primes over $pA$; they are finite by
   [lem-sc-finite-minimal-primes-over-ideal]. Each $P_i$ is a minimal support prime of the cyclic
   module $A/pA$, hence associated by [lem-weil-pbc-minimal-support-prime-associated], and has
   height one by [lem-weil-pbc-normal-domain-principal-quotient-associated-height]. The
   localization $T_i=A_{P_i}$ is Noetherian and normal by [lem-weil-pbc-localization-noetherian,
   lem-weil-pbc-localization-normal-domain], of dimension one, so is a DVR by
   [lem-sc-normal-dim1-dvr]. The map $W_0\to T_i$ is injective and local since its uniformizer $p$
   belongs to $P_i$. The ring $A$ is excellent by [lem-per-complete-local-excellence], and each
   $T_i$ is excellent by [lem-exc-finite-type-localization-excellent].
3. The residue field of $T_i$ is $\operatorname{Frac}(A/P_i)$. By
   [lem-weil-pbc-complete-local-quotient], $R_i=A/P_i$ is a complete Noetherian local domain of
   characteristic $p$ with residue field $k$. The map $k_*=W_0/pW_0\to R_i$ is injective because
   it is a unital map from a field to a nonzero ring. Its composite with $R_i\to k$ is the
   original inclusion. Since $k_{\mathrm{perf}}=k_*$, [lem-per-epp-perfect-core-complete-local]
   proves that every element of the maximal perfect subfield of $\operatorname{Frac}(A/P_i)$ is
   algebraic over $k_*$. Apply [lem-per-epp-finite-family-traits] to all the $T_i$ at once,
   obtaining a finite extension $W_0\hookrightarrow W_1$ of complete DVRs, with perfect residue
   field. Put $K_*=\operatorname{Frac}(W_0)$ and $K_1=\operatorname{Frac}(W_1)$. The extension
   $W_1$ is good for every $T_i$, in the explicit sense of [lem-per-epp-single-trait-base-change]:
   every normalized field factor of the base change has reduced special fibre.
4. The extension $K_1/K_*$ is finite. Indeed, localizing a finite $W_0$-module generating set for
   $W_1$ gives a finite-dimensional domain over $K_*$. Multiplication by any nonzero element is an
   injective endomorphism of this vector space, hence surjective; this localization is a field and
   therefore equals $K_1$. By [lem-weil-pbc-finite-extension-in-finite-normal-extension], embed
   $K_1$ in an extension $K$ finite and normal over $K_*$. It is separable: in characteristic zero
   an irreducible polynomial of positive degree has nonzero derivative of smaller degree, so it is
   relatively prime to its derivative. Thus $K/K_*$ is finite Galois.
5. Let $W$ be the integral closure of $W_0$ in $K$. By
   [lem-per-complete-dvr-finite-normalization], $W$ is a finite complete DVR over $W_0$, with
   fraction field $K$, and $W_0\to W$ is local. Moreover $W_1\subseteq W$: the elements of $W_1$
   satisfy monic equations over $W_0$ by [lem-weil-pbc-finite-algebra-is-integral]. The map
   $W_1\to W$ is local. If $\pi_1$ is a uniformizer of $W_1$, write $p=u\pi_1^a$ with $a>0$ by
   [lem-weil-pbc-dvr-unit-times-uniformizer-power]; since $p$ lies in the maximal ideal of $W$ and
   $u$ is a unit, so does $\pi_1$, whereas every element outside $(\pi_1)$ remains a unit. The
   residue field $k_0=W/\mathfrak m_W$ is finite over $k_*$: a finite $W_0$-module generating set
   descends to a spanning set. It is perfect by [lem-per-algebraic-extension-perfect]. For each
   $i$, apply clause (3) of [lem-per-epp-single-trait-base-change] to $W_1\to W$; all normalized
   field factors over $W$ still have reduced special fibre. Choose a uniformizer $\pi$ of $W$.
6. Let $F=\operatorname{Frac}(A)$. The algebra $F\otimes_{K_*}K$ is nonzero and finite dimensional
   over $F$: tensor a $K_*$-basis of $K$. Choose a maximal ideal and let $L$ be its quotient
   field. Then $L/F$ is finite and the unital map $K\to L$ is injective. Let $C\subset L$ be the
   integral closure of $A$ in $L$. It is a normal domain with fraction field $L$ by
   [lem-weil-pbc-integral-closure-finite-extension-normal]. It is finite over $A$:
   [lem-weil-pbc-complete-local-nagata] and [def-weil-pbc-nagata-ring,
   def-weil-pbc-japanese-domain] give precisely this for the finite extension $L/F$. The map $A\to
   C$ is injective, and $W\subset C$, because $W$ is finite over $W_0$ and hence integral by
   [lem-weil-pbc-finite-algebra-is-integral]; its monic equations over $W_0$ are also monic
   equations over $A$.
7. The images of $F$ and $K$ generate $L$ as a field: the surjection $F\otimes_{K_*}K\to L$
   expresses every element of $L$ as a finite sum of products from these two images. Apply
   [lem-per-galois-compositum-restriction] to these subfields of $L$. The extension $L/F$ is
   Galois, and each $F$-automorphism of $L$ preserves $K$. It is already finite by the preceding
   step. Hence [lem-weil-pbc-finite-galois-fixed-field] shows that $G=\operatorname{Aut}_F(L)$ is
   finite. This is the full group required in the statement, and restriction gives its action on
   $K$. We do not identify $G$ with all of $\operatorname{Aut}_{K_*}(K)$; it may be a proper
   subgroup.
8. By [lem-weil-pbc-finite-over-complete-local-product], the finite $A$-domain $C$ is Noetherian
   complete local, with unique maximal ideal $\mathfrak n$ over $\mathfrak m$. Thus
   $A\hookrightarrow C$ is local. The field $k'=C/\mathfrak n$ is finite over $k$: the images of
   any finite $A$-module generating set of $C$ span $k'$ over $k$. By
   [lem-weil-pbc-finite-algebra-is-integral] and
   [lem-weil-pbc-integral-injective-dimension-equal], $\dim C=d$. Also $W\hookrightarrow C$ is
   local: in $W$ the nonzero element $p$ is $u\pi^e$ by
   [lem-weil-pbc-dvr-unit-times-uniformizer-power]; its residue is zero, so $e>0$. Since
   $p\in\mathfrak n$ and $u$ stays a unit, $\pi\in\mathfrak n$. Every element outside $\pi W$ is a
   unit, giving the asserted inverse image of $\mathfrak n$. Reduction supplies the specified
   inclusion $k_0\hookrightarrow k'$.
9. For $g\in G$, applying $g$ to a monic equation over $A$ leaves its coefficients fixed, so
   $g(C)\subseteq C$; applying $g^{-1}$ gives equality. Likewise, restriction to $K$ fixes $K_*$,
   hence $W_0$, so monic equations over $W_0$ show $g(W)=W$. The restrictions are ring
   automorphisms and form compatible actions because they are restrictions of the same action on
   $L$. A ring automorphism preserves the unique maximal ideal of a local ring, so these
   automorphisms of $C$ and $W$ are local. The action fixes $A$ pointwise by the definition of
   $G$. Under $\operatorname{Frac}(C)=L$, it is exactly the full Galois action. The map $W\to C$
   is the inclusion already constructed, so it is equivariant.
10. Let $Q$ be a height-one prime of $C$ containing $\pi$ and put $P=Q\cap A$. It contains $p$
   because $p=u\pi^e$. Going down for the normal domain $A$ in its integral domain extension $C$
   [lem-weil-pbc-going-down-normal-integral] shows that $P$ cannot have a strict chain of length
   two below it: such a chain would lift to one below $Q$. Since $p\ne0$, $P$ has height one.
   Hence $P$ is minimal over $pA$ (a strictly smaller prime containing $p$ would give a chain of
   length two), and equals some $P_i$.
11. Fix this $P_i$ and localize $C$ at $A\setminus P_i$, obtaining $C_i$. By
   [lem-weil-pbc-integral-closure-commutes-localization], $C_i$ is the integral closure of
   $T_i=A_{P_i}$ in $L$ (localizing the field $L$ changes nothing). Let $D_i$ be the image of
   $T_i\otimes_{W_0}W$ in $L$. It is integral over $T_i$ by the finite-algebra criterion
   [lem-weil-pbc-finite-algebra-is-integral]: a finite $W_0$-module generating set of $W$ gives
   one for this image over $T_i$. If $x\in L$ is integral over $D_i$, the extension $D_i\subset
   D_i[x]$ is integral: the powers below the degree of a monic equation span $D_i[x]$, so
   [lem-weil-pbc-finite-algebra-is-integral] applies. Thus [lem-weil-pbc-integral-transitive] for
   $T_i\subset D_i\subset D_i[x]$ makes $x$ integral over $T_i$. Conversely a monic equation over
   $T_i$ is one over $D_i$. Thus $C_i$ is exactly the integral closure of $D_i$ in $L$. Since
   $\operatorname{Frac}(T_i)=F$, the field $L$ is a field factor of $F\otimes_{K_*}K$. The
   goodness of $W$ for $T_i$ proved in step 5, namely clause (3) of
   [lem-per-epp-single-trait-base-change], therefore says that $C_i/\pi C_i$ is reduced.
12. The ring $C_Q/\pi C_Q$ is reduced. Indeed, it is a localization of the reduced ring $C_i/\pi
   C_i$: the maps identify fractions $c/s$ and impose the same relation $\pi=0$. To check
   reducedness directly, if $(x/s)^n=0$, some inverted $t$ has $tx^n=0$, so
   $(tx)^n=t^{n-1}(tx^n)=0$; reducedness gives $tx=0$, hence $x/s=0$. This proves the generic
   reducedness assertion for every height-one $Q$ containing $\pi$.
13. Set $M=C/\pi C$. Every associated prime $Q$ of this cyclic $C$-module has height one by
   [lem-weil-pbc-normal-domain-principal-quotient-associated-height], because $C$ is a Noetherian
   normal domain and $\pi\ne0$. Such a prime contains $\pi$. If $z\in M$ is nilpotent, its image
   in $M_Q=C_Q/\pi C_Q$ is zero by the preceding step; the identification is
   [lem-weil-pbc-localization-at-prime-of-quotient]. Injectivity into the product of these module
   localizations [lem-weil-pbc-module-injects-localizations-associated-primes] forces $z=0$. Thus
   $C/\pi C$ is reduced. This is the argument of IV 4.2.4, expressed through the already available
   associated-prime form of Stacks 031T and 0311.
14. The complete Noetherian local domain $C$ is excellent by [lem-per-complete-local-excellence],
   hence catenary by [def-exc-excellent-ring]. Every prime $Q$ minimal over $\pi C$ is a minimal
   support prime of $C/\pi C$, so [lem-weil-pbc-minimal-support-prime-associated] and
   [lem-weil-pbc-normal-domain-principal-quotient-associated-height] give
   $\operatorname{ht}(Q)=1$. In the catenary local domain $C$ of dimension $d$, all saturated
   chains from $(0)$ to $\mathfrak n$ have length $d$. A saturated chain from $Q$ to $\mathfrak
   n$, preceded by $(0)\subsetneq Q$, is such a chain, so has length $d-1$ above $Q$. Chains in
   $C/Q$ are exactly chains above $Q$; therefore $\dim(C/Q)=d-1$ for every minimal $Q$ of $C/\pi
   C$. This proves equidimensionality of the required dimension. The construction of $C,W,\pi$ and
   the residue inclusions in the preceding steps supplies every remaining clause.
-/
theorem exists_galois_epp_reduced_fibre_cover
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsAdicComplete (maximalIdeal A) A] [CharZero A]
    (p d : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hd : 2 ≤ d) (hdim : ringKrullDim A = (d : WithBot ℕ∞)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : IsLocalRing C)
      (_ : IsNoetherianRing C) (_ : IsIntegrallyClosed C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra A C)
      (_ : IsLocalHom (algebraMap A C)),
      Function.Injective (algebraMap A C) ∧ Module.Finite A C ∧
      ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (maximalIdeal W) W) (_ : CharZero W)
        (_ : CharP (ResidueField W) p) (_ : Algebra W C)
        (_ : IsLocalHom (algebraMap W C)),
        Function.Injective (algebraMap W C) ∧ PerfectRing (ResidueField W) p ∧
        ∃ (_ : Algebra (FractionRing A) (FractionRing C)),
          (∀ a : A, algebraMap (FractionRing A) (FractionRing C)
            (algebraMap A (FractionRing A) a) =
              algebraMap C (FractionRing C) (algebraMap A C a)) ∧
          Module.Finite (FractionRing A) (FractionRing C) ∧
          IsGalois (FractionRing A) (FractionRing C) ∧
          ∃ (G : Type u) (_ : Group G) (_ : Finite G)
            (e : G ≃* (FractionRing C ≃ₐ[FractionRing A] FractionRing C))
            (ρC : G →* (C ≃+* C)) (ρW : G →* (W ≃+* W)),
            (∀ g : G, IsLocalHom (ρC g).toRingHom) ∧
            (∀ g : G, IsLocalHom (ρW g).toRingHom) ∧
            (∀ (g : G) (w : W),
              ρC g (algebraMap W C w) = algebraMap W C (ρW g w)) ∧
            (∀ (g : G) (a : A), ρC g (algebraMap A C a) = algebraMap A C a) ∧
            (∀ (g : G) (c : C),
              e g (algebraMap C (FractionRing C) c) =
                algebraMap C (FractionRing C) (ρC g c)) ∧
            ringKrullDim C = (d : WithBot ℕ∞) ∧
            RingHom.Finite (ResidueField.map (algebraMap A C)) ∧
            Function.Injective (ResidueField.map (algebraMap W C)) ∧
            ∃ π : W, maximalIdeal W = Ideal.span {π} ∧
              IsReduced (C ⧸ Ideal.span {algebraMap W C π}) ∧
              ringKrullDim (C ⧸ Ideal.span {algebraMap W C π}) =
                ((d - 1 : ℕ) : WithBot ℕ∞) ∧
              (∀ P : Ideal (C ⧸ Ideal.span {algebraMap W C π}),
                P ∈ (⊥ : Ideal (C ⧸ Ideal.span {algebraMap W C π})).minimalPrimes →
                ringKrullDim ((C ⧸ Ideal.span {algebraMap W C π}) ⧸ P) =
                  ((d - 1 : ℕ) : WithBot ℕ∞)) := by
  sorry

end IsLocalRing
