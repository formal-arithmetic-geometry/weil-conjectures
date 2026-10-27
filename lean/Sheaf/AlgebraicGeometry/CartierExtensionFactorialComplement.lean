/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.GroupTheory.MonoidLocalization.Away

/-!
# Extending effective Cartier divisors across factorial local rings

Source: Stacks Project, Divisors, Tag 0BD8 (lemma-closure-effective-cartier-divisor)
(blueprint: lem-sfb-cartier-extension-factorial-complement).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- An effective Cartier divisor on an open subscheme extends across a complement
with factorial local rings. The equality of pulled-back ideals is equality of closed
subschemes, including multiplicities. No density, separatedness, or integrality
hypothesis on the ambient scheme is required.

Source: Stacks Project, Divisors, Tag 0BD8 (lemma-closure-effective-cartier-divisor)
(blueprint: lem-sfb-cartier-extension-factorial-complement).

Proof (the accepted stage-1 split):

1. The open immersion $V\hookrightarrow X$ is quasi-compact by
   [lem-sfb-noetherian-open-immersion-qc]. For an affine open $B\subset X$, $D\cap B$ is closed in
   the quasi-compact space $V\cap B$, so it is quasi-compact; hence $h:D\to X$ is quasi-compact.
   It is a monomorphism (a composite of the two subscheme inclusions), so its diagonal is an
   isomorphism and it is quasi-separated as well. Form its scheme-theoretic image $C\subset X$
   using [lemma-nagata-scheme-image-ideal-qc]. By [lemma-nagata-scheme-image-restrict-open] its
   restriction to $V$ is the scheme-theoretic image of the closed immersion $D\hookrightarrow V$,
   which is $D$ by [lemma-nagata-scheme-image-of-closed-immersion]. Thus $C\cap V=D$ as closed
   subschemes.

2. Fix $x\in X\setminus V$ and put $A=\mathcal O_{X,x}$. Choose an affine open
   $\operatorname{Spec}B$ containing $x$. Its coordinate ring is Noetherian by
   [pqf-lem-affine-open-locnoeth], and $A=B_{\mathfrak p}$ by
   [lem-weil-pbc-affine-open-stalk-localization], so $A$ is Noetherian by
   [lem-weil-pbc-localization-noetherian]. It is a UFD by the hypothesis. The canonical morphism
   $c:\operatorname{Spec}A\to X$ is flat and identifies the closed-point local ring with $\mathcal
   O_{X,x}$, by [lem-weil-pbc-spec-local-ring-canonical-morphism]. Therefore
   [lem-sfb-scheme-image-flat-base-change] identifies $C_A=C\times_X\operatorname{Spec}A$ with the
   scheme-theoretic image of $E=D\times_X\operatorname{Spec}A$. Set $W=c^{-1}V$. The local
   equations of $D$ remain nonzerodivisors after pullback: every stalk map of $c$ is an
   isomorphism by the same canonical-morphism lemma. Thus $E$ is an effective Cartier divisor on
   $W$.

3. The single affine chart makes $\operatorname{Spec}A$ locally Noetherian. It is quasi-compact: a
   cover can be refined to basic opens $D(b)$, the $b$ generate the unit ideal (otherwise a
   maximal ideal misses the cover), and a finite expression for $1$ yields a finite subcover. Thus
   it is Noetherian, and its open $W$ is Noetherian by
   [lem-weil-pbc-noetherian-open-subscheme-noetherian]. Its local rings are prime localizations of
   $A$ by [lem-weil-pbc-affine-open-stalk-localization], hence UFDs by
   [lem-sfb-ufd-prime-localizations]. Apply [lem-sfb-factorial-cartier-prime-decomposition] to
   obtain $\mathcal I_E=\prod_i\mathcal I_{E_i}^{a_i}$ with integral Cartier components having
   generic points $\xi_i$ and $\dim\mathcal O_{W,\xi_i}=1$.

4. Let $\mathfrak p_i\subset A$ correspond to $\xi_i$. Since $W$ is open, its local ring there is
   $A_{\mathfrak p_i}$; the dimension-one conclusion says that $\mathfrak p_i$ has height one. By
   [lem-trf-ufd-height-one], $\mathfrak p_i=(f_i)$. Choose the $f_i$ pairwise nonassociated; each
   is a nonzero prime element because $A$ is a domain and $(f_i)$ is a nonzero prime ideal. The
   reduced closed subscheme $V(f_i)\cap W$ is precisely $E_i$: both are the reduced closure in $W$
   of $\xi_i$. Indeed on every affine chart meeting that closure the defining radical prime is the
   prime corresponding to that generic point. Hence the given equality of ideal products says that
   $E$ is cut out on $W$ by $F=\prod_i f_i^{a_i}$.

5. Write $J\subset A$ for the ideal of $C_A$. By [lem-weil-pbc-scheme-image-qc-kernel],
   $J=\ker(A\to\Gamma(E,\mathcal O_E))$. The equation in the preceding step gives $(F)\subset J$.
   Conversely, take $b\in J$. For each $i$ choose a basic open $D(h_i)\subset W$ containing
   $\xi_i$, so $h_i\notin(f_i)$. Its restriction satisfies
   $b/1\in(F)A_{h_i}\subset(f_i^{a_i})A_{h_i}$. The fraction equality rule gives $h_i^n
   b\in(f_i^{a_i})$ for some $n$. Since the prime $f_i$ does not divide $h_i$, unique
   factorization implies $f_i^{a_i}\mid b$. The $f_i$ are pairwise nonassociated, so unique
   factorization gives $F\mid b$. Thus $J=(F)$. If the decomposition is empty, $E$ is empty,
   $F=1$, and the same kernel is $A$.

6. The product $F$ is nonzero in the domain $A$ (including the empty product $1$), so
   multiplication by $F$ is injective. At the closed point of $\operatorname{Spec}A$, its ideal
   $J=(F)$ is already the stalk ideal. The canonical-morphism identification in step 2 therefore
   proves that $\mathcal I_{C,x}$ is generated by a nonzerodivisor. For $x\in V$ this follows from
   $C\cap V=D$; at points outside $C$ the generator is $1$. Every stalk of $\mathcal I_C$ is now
   covered. Apply [lem-sfb-stalk-nonzerodivisor-cartier-spreading] to the closed subscheme $C$ of
   the locally Noetherian $X$. It is an effective Cartier divisor, and the previously proved
   equality $C\cap V=D$ gives the required $D^{\mathrm{ext}}=C$.
-/
theorem exists_isInvertible_extension_of_factorial_complement
    {X : Scheme.{u}} [IsLocallyNoetherian X] (V : X.Opens)
    (D : V.toScheme.IdealSheafData) (hD : D.IsInvertible)
    (hfactorial : ∀ x : X, x ∉ V →
      IsDomain (X.presheaf.stalk x) ∧ UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ Dext : X.IdealSheafData, Dext.IsInvertible ∧ Dext.comap V.ι = D := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
