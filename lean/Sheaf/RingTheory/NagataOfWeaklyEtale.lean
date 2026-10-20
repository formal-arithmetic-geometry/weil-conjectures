/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.RingTheory.IndPrincipalZariski
import WeilConjectures.RingTheory.JapaneseDomain
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.RingTheory.NormalOfFlatNormalFibers
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Sheaf.RingTheory.WeaklyEtaleField
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Sheaf.RingTheory.IndEtaleUniverseTransport

/-! # Nagata ascent along weakly etale ring maps

Source: Silvio Greco, Two theorems on excellent rings, Nagoya Math. J. 60 (1976),
Remark 5.7(ii), p. 148, and Remark 5.2, p. 146
(blueprint: lem-exc-nagata-weakly-etale-ascent).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A weakly etale ring map from a Nagata ring to a Noetherian ring has Nagata target.
Source: Greco, Two theorems on excellent rings, Remark 5.7(ii), p. 148; Remark 5.2
identifies absolute flatness with weak etaleness for Noetherian rings.
(blueprint: lem-exc-nagata-weakly-etale-ascent).

Proof plan (the eight steps of the DAG node):
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
   $P$. In particular these local rings are normal domains by [def-weil-pbc-normal-ring], because
   the fraction field of a field is that field itself. Thus $F$ is a normal ring, with every prime
   maximal, including when $F$ is the zero ring (there are then no primes).

2. For any weakly etale map $U\to V$ of Noetherian rings and any $U$-algebra $U'$, the
   ring-to-scheme equivalence in [def-weil-pbc-ind-etale-algebra] and the base-change clause of
   [lem-weil-pbc-weakly-etale-composition-base-change], identified on affine spectra by
   [lem-weil-pbc-affine-chart-base-change-iso], makes $U'\to V\otimes_U U'$ weakly etale. In
   particular its fibre at $p\subset U$ is $F_p=V\otimes_U\kappa(p)=(U\setminus p)^{-1}(V/pV)$.
   This ring is Noetherian: $V/pV$ is a cyclic finite $V$-algebra, so
   [lem-weil-pbc-finite-algebra-noetherian] applies, and then
   [lem-weil-pbc-localization-noetherian] applies. Step 1 shows that every $F_p$ is normal and has
   all primes maximal. Its residue fields are separable algebraic over $\kappa(p)$. For $q\subset
   V$ over $p$, the fibre prime is the extension of $q/pV$; its residue field is
   $\operatorname{Frac}(V/q)=\kappa(q)$: localizing $V/q$ first at $U\setminus p$ and then at all
   its nonzero elements gives exactly the same fractions as localizing at all nonzero elements at
   once. Thus $\kappa(q)/\kappa(p)$ is algebraic, including when it is infinite.

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
   and $Q\cap B=q$. The prime $Q$ is minimal: the generic fibre is weakly etale over $L_0$ by step
   2; applying [lem-weil-pbc-weak-etale-field] and the algebraic-domain inverse calculation of
   step 1 shows that all its primes are maximal, so the following extension-contraction argument
   applies. If $Q_0\subseteq Q$ is another prime of $C$, both avoid every nonzero element of $R$.
   Their extensions in $C\otimes_R L_0$ are primes, since the quotients embed in localizations of
   the domains $C/Q_i$. These extensions contract back to $Q_i$: if $sc\in Q_i$ with $0\ne s\in
   R$, primality gives $c\in Q_i$. But the generic fibre $C\otimes_R L_0$ has every prime maximal
   by step 2. The two extended primes, one contained in the other, must be equal, hence $Q_0=Q$.
   This proves minimality without claiming that $h$ is surjective onto $L$.

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
   Nagata. This part of the argument has not needed J-2. If $B$ is the zero ring there is no prime
   $q$, so the Japanese conditions are vacuous and its assumed Noetherianity still gives the
   conclusion.
-/
theorem isNagataRing_of_weaklyEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsNoetherianRing B]
    (f : A →+* B) (hf : @Algebra.WeaklyEtale A B _ _ f.toAlgebra)
    (hA : IsNagataRing A) : IsNagataRing B := by
  sorry

end RingHom
