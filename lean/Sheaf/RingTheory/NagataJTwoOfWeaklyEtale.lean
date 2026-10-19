/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.RingTheory.IndPrincipalZariski
public import Sheaf.RingTheory.NagataRing
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.WeaklyEtaleField
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.CategoryTheory.MorphismProperty.Composition
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.RingTheory.JapaneseDomain
import Mathlib.RingTheory.Localization.Integral
import Sheaf.RingTheory.NormalOfFlatNormalFibers
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.RingTheory.RegularMapAscent
import Sheaf.RingTheory.JTwoResidueFieldCriterion
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso

/-!
# Nagata and J-2 ascent along weakly etale homomorphisms

Source: Silvio Greco, Two theorems on excellent rings, Nagoya Mathematical Journal 60
(1976), 139–149, Theorem 5.3(ii) and Remark 5.2, pp. 146–147; the Foreword on p. 139
assumes commutative Noetherian rings (blueprint: lem-exc-weakly-etale-nagata-j2).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

/-- Nagata and J-2 ascend together along a weakly etale map of Noetherian rings.
J-2 is expanded exactly as the open-regular-locus clause of `IsQuasiExcellent`.

Source: Greco, Two theorems on excellent rings, Theorem 5.3(ii), pp. 146–147, and
Remark 5.2; Stacks Project, Tags 032R and 07P7
(blueprint: lem-exc-weakly-etale-nagata-j2).

Proof (the ten steps of the node):
1. First establish the field-fibre calculation, for reuse below. Let $k\to F$ be any weakly etale
   algebra over a field. By [lem-weil-pbc-weak-etale-field], $F$ is reduced, every finitely
   generated $k$-subalgebra is finite etale, and its residue fields are separable algebraic over
   $k$. Apply [lem-weil-pbc-finite-algebra-is-integral] to the finite subalgebra $k[x]$, for each
   $x\in F$: every element of $F$ is integral over $k$. For any prime $P$ of $F$, the domain $F/P$
   is therefore algebraic over $k$. For $0\ne z\in F/P$, choose a monic relation of least degree.
   Its constant term is nonzero, since otherwise cancellation of $z$ gives a lower-degree
   relation. Solving this relation for $z^{-1}$ shows that $F/P$ is a field. Thus every prime of
   $F$ is maximal, and no two distinct primes are comparable; every prime is also minimal. Now
   [lem-weil-pbc-minimal-prime-reduced-localization-field] says that $F_P$ is a field for each
   $P$. In particular these local rings are normal domains by [def-weil-pbc-normal-ring], and
   regular local rings by [lem-weil-pbc-field-regular-ring]. If $F$ is Noetherian, it is
   consequently both normal and regular, with every prime maximal.
2. For any weakly etale map $U\to V$ of Noetherian rings and any $U$-algebra $U'$, the affine
   instance of [lem-weil-pbc-weakly-etale-composition-base-change], identified by
   [lem-weil-pbc-affine-chart-base-change-iso], makes $U'\to V\otimes_U U'$ weakly etale. In
   particular its fibre at $p\subset U$ is $F_p=V\otimes_U\kappa(p)=(U\setminus p)^{-1}(V/pV)$.
   This ring is Noetherian: $V/pV$ is a cyclic finite $V$-algebra, so
   [lem-weil-pbc-finite-algebra-noetherian] applies, and then
   [lem-weil-pbc-localization-noetherian] applies. Step 1 shows that every $F_p$ is normal,
   regular, and has all primes maximal. Its residue fields are separable algebraic over
   $\kappa(p)$. For $q\subset V$ over $p$, the fibre prime is the extension of $q/pV$; its residue
   field is $\operatorname{Frac}(V/q)=\kappa(q)$: localizing $V/q$ first at $U\setminus p$ and
   then at all its nonzero elements gives exactly the same fractions as localizing at all nonzero
   elements at once. Thus $\kappa(q)/\kappa(p)$ is algebraic, including when it is infinite.
3. Fix a prime $q\subset B$, put $p=f^{-1}(q)$, $k=\kappa(p)=\operatorname{Frac}(A/p)$ and
   $E=\kappa(q)=\operatorname{Frac}(B/q)$, and fix an arbitrary finite field extension $L/E$. Step
   2 gives that $E/k$ is algebraic. There is a finite subextension $L_0/k$ inside $L$ with
   $L=EL_0$: choose a finite $E$-basis $x_1,\ldots,x_r$ of $L$. Each $x_i$ satisfies a monic
   polynomial over $E$; the finitely many coefficients of these polynomials lie in a finite
   extension $k_1/k$ inside $E$, because adjoining finitely many algebraic elements is spanned
   successively by bounded powers. The ring $k_1[x_1,\ldots,x_r]$ is finite dimensional over $k_1$
   by the same bounded-power spanning argument and is a domain, hence a field: multiplication by a
   nonzero element is an injective endomorphism of a finite-dimensional vector space and is
   surjective. It is therefore a finite extension of $k$, and so is its subfield
   $L_0=k(x_1,\ldots,x_r)$. Finally $EL_0=L$ since $EL_0$ contains the chosen $E$-basis. No finite
   degree for $E/k$ is asserted.
4. Let $R\subset L_0$ be the integral closure of $A/p$ in $L_0$. Since $A$ is Nagata,
   [def-weil-pbc-nagata-ring] gives that $A/p$ is Japanese; [def-weil-pbc-japanese-domain] gives
   that $R$ is finite over $A/p$, hence over $A$. The precise normalization lemma
   [lem-weil-pbc-integral-closure-finite-extension-normal] gives that $R$ is a normal domain with
   fraction field $L_0$. By [lem-weil-pbc-finite-algebra-noetherian], $R$ is Noetherian. By
   [lem-weil-pbc-localization-normal-domain], each prime localization of $R$ is a normal domain,
   so $R$ is a normal ring as required by the normality ascent lemma.
5. Set $C=B\otimes_A R$. Step 2 gives that $R\to C$ is weakly etale. If $r_1,\ldots,r_s$ generate
   $R$ as an $A$-module, the elements $1\otimes r_j$ generate $C$ as a $B$-module, by expanding
   each pure tensor and then each sum of pure tensors. Thus $C$ is finite over the Noetherian ring
   $B$, and [lem-weil-pbc-finite-algebra-noetherian] makes $C$ Noetherian. Its fibre rings over
   $R$ are normal by step 2; the map $R\to C$ is flat by [def-weil-pbc-ind-etale-algebra]. All
   five hypotheses of [lem-weil-pbc-flat-normal-fibres-noetherian-normal] are now present: $R,C$
   Noetherian, flatness, normal fibres, and $R$ normal. Consequently $C$ is normal.
6. The maps $B\to B/q\subset E\subset L$ and $R\subset L_0\subset L$ agree on $A$ and give $h:C\to
   L$, $b\otimes r\mapsto\bar b r$. Write $Q=\ker h$ and $D=h(C)=C/Q\subset L$. Then $Q\cap R=0$
   and $Q\cap B=q$. The prime $Q$ is minimal: if $Q_0\subseteq Q$ is another prime of $C$, both
   avoid every nonzero element of $R$. Their extensions in $C\otimes_R L_0$ are primes, since the
   quotients embed in localizations of the domains $C/Q_i$. These extensions contract back to
   $Q_i$: if $sc\in Q_i$ with $0\ne s\in R$, primality gives $c\in Q_i$. But the generic fibre
   $C\otimes_R L_0$ has every prime maximal by step 2. The two extended primes, one contained in
   the other, must be equal, hence $Q_0=Q$. This proves minimality without claiming that $h$ is
   surjective onto $L$.
7. By [lem-weil-pbc-noetherian-finitely-many-minimal-primes], $C$ has finitely many minimal
   primes. It is reduced, since every prime localization of the normal ring $C$ is a domain and
   the maps to those localizations are jointly injective by
   [lem-weil-pbc-prime-localizations-jointly-injective]. Apply
   [lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions] to obtain
   $C\cong\prod_{i=1}^t C_i$ with each $C_i$ a normal domain. A prime in a finite product chooses
   one factor: of the orthogonal idempotents $e_i$ summing to $1$, exactly one is outside a prime;
   all other factors vanish in the quotient. Since $Q$ is minimal, its prime in the selected
   domain factor is $(0)$. Thus $D=C/Q$ is that normal domain factor. It is finite over $B/q$,
   generated by the images of $1\otimes r_j$. Its fraction field inside $L$ contains $E$ because
   it contains $B/q$, and contains $L_0$ because it contains $R$. It therefore equals $EL_0=L$.
8. The finite algebra $D$ is integral over $B/q$ by [lem-weil-pbc-finite-algebra-is-integral].
   Conversely any $x\in L$ integral over $B/q$ satisfies the same monic polynomial over the larger
   subring $D$, so lies in $D$, since $D$ is normal with fraction field $L$. Therefore $D$ is
   exactly the integral closure of $B/q$ in $L$, and it is finite over $B/q$. The prime $q$ and
   finite extension $L/E$ were arbitrary. By [def-weil-pbc-japanese-domain] every $B/q$ is
   Japanese. With the assumed Noetherianity of $B$, [def-weil-pbc-nagata-ring] gives that $B$ is
   Nagata. This part of the argument has not needed J-2.
9. Retain the construction for the arbitrary $q$ and $L/E$. The finite $A$-algebra $R$ is of
   finite type: its finite module generators also generate it as an algebra. Since $A$ is J-2,
   [def-exc-excellent-ring] makes $\operatorname{Reg}(R)$ open. It contains the zero prime,
   because $R_{(0)}=L_0$ is a regular field by [lem-weil-pbc-field-regular-ring]. By
   [lem-weil-pbc-spec-localization-away-basic-open], choose $0\ne a\in R$ with
   $D_R(a)\subseteq\operatorname{Reg}(R)$. For a prime $P$ of $R_a$ with contraction $p$, the
   mutually inverse maps $r/s\mapsto(r/1)/(s/1)$ and $(r/a^n)/(s/a^m)\mapsto ra^m/(sa^n)$ identify
   $(R_a)_P$ with $R_p$; their denominators are invertible since $a\notin p$ and $s\notin p$. Thus
   $R_a$ is regular. Its Noetherianity and that of $C_a$ follow from
   [lem-weil-pbc-localization-noetherian]. The map $R_a\to C_a$ is the base change of $R\to C$,
   hence weakly etale by step 2, flat by its definition, and has regular fibres by step 2. Apply
   [lem-weil-pbc-regular-map-ascent] to get that $C_a$ is regular. Under the product decomposition
   in step 7, write $C_a\cong D_a\times H$. For a prime $\mathfrak t$ of $D_a$, the corresponding
   prime of $C_a$ is $\mathfrak t\times H$. The idempotent $(1,0)$ is outside this prime and
   becomes $1$ in its localization, while $(0,1)$ becomes $0$. Projection therefore identifies
   $(C_a)_{\mathfrak t\times H}$ with $(D_a)_{\mathfrak t}$; its inverse sends $d/s$ to
   $(d,0)/(s,0)$, whose denominator is outside $\mathfrak t\times H$. Thus every prime local ring
   of $D_a$ is regular. Its Noetherianity follows from that of $C_a$, since it is a cyclic
   quotient algebra, by [lem-weil-pbc-finite-algebra-noetherian]. The image of $a$ in $D\subset L$
   is nonzero. For each prime $\mathfrak d$ of $D$ avoiding $a$, the fraction maps
   $d/s\mapsto(d/1)/(s/1)$ and $(d/a^n)/(s/a^m)\mapsto da^m/(sa^n)$ identify $D_{\mathfrak d}$
   with $(D_a)_{\mathfrak dD_a}$. Consequently $D_D(a)$ is a nonempty open subset of
   $\operatorname{Spec}D$ consisting of regular local rings; it contains $(0)$.
10. In particular, for every prime $q\subset B$ and every finite purely inseparable extension
   $L/\kappa(q)$, steps 3–7 and 9 produce the $B$-subalgebra $D\subset L$, finite as a $B$-module,
   with fraction field exactly $L$ and a nonempty open subset of its spectrum consisting of
   regular local rings. (The construction works for all finite extensions, so it applies to
   these.) These are exactly the hypotheses, with $R=B$, of [lem-exc-j2-residue-field-criterion].
   Since $B$ is Noetherian by assumption, that lemma proves that $B$ is J-2. Combining with step 8
   gives both requested clauses. If $B$ is the zero ring there are no primes; the Japanese
   conditions and the criterion are vacuous, and every unital $B$-algebra is zero, so the same
   conclusion holds.
-/
theorem isNagataRing_and_jTwo_of_weaklyEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) (hf : f.WeaklyEtale)
    (hNagata : IsNagataRing A)
    (hJTwo : ∀ (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C],
      IsOpen {p : PrimeSpectrum C | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}) :
    IsNagataRing B ∧
      ∀ (C : Type v) [CommRing C] [Algebra B C] [Algebra.FiniteType B C],
        IsOpen {p : PrimeSpectrum C | IsRegularLocalRing (Localization.AtPrime p.asIdeal)} := by
  sorry

end RingHom
