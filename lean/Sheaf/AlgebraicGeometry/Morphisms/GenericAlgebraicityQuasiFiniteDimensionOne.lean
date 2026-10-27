/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.Algebraic.Defs
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Sheaf.RingTheory.AffineDimensionInequality
import Sheaf.AlgebraicGeometry.ClosedPointField
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-!
# Generic algebraicity and quasi-finiteness in local dimension at most one

Source: Stacks Project, Varieties, Tag 0AB6, `lemma-quasi-finite-in-codim-1`, condition (1)
(blueprint: lem-sfb-generically-finite-quasifinite-over-dimension-one).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A locally finite type morphism with algebraic residue extensions at all component
 generic points is quasi-finite at every point over a target point whose local ring is
 Noetherian of Krull dimension at most one.

Source: Stacks Project, Varieties, Tag 0AB6, `lemma-quasi-finite-in-codim-1`, condition (1)
(blueprint: lem-sfb-generically-finite-quasifinite-over-dimension-one).
The algebra structure in the generic hypothesis is induced by the canonical residue-field
map, and the conclusion uses the finite-type-inclusive Stacks notion of quasi-finiteness.

Proof (the ten steps of the DAG, following Tag 0AB6):
1. Fix $z\in Z$ over $s$. Choose an affine neighbourhood $V=\operatorname{Spec}R$ of $s$, with
corresponding prime $\mathfrak p$, and an affine open $U=\operatorname{Spec}A$ containing $z$ and
contained in $g^{-1}(V)$. By [lem-weil-pbc-lft-affine-pairs], $A$ is a finite type $R$-algebra. By
[lem-weil-pbc-affine-open-stalk-localization], $B=R_{\mathfrak p}\cong\mathcal O_{S,s}$. Thus $B$
is Noetherian and local, with maximal ideal $\mathfrak m=\mathfrak pB$ and $\dim B\le1$. Write
$k=B/\mathfrak m=\kappa(s)$ and $M=R\setminus\mathfrak p$. Uses: lem-weil-pbc-lft-affine-pairs,
lem-weil-pbc-affine-open-stalk-localization, def-weil-pbc-localization-at-prime.

2. Put $C=A\otimes_R B$. By [lem-weil-pbc-fibre-product-affine-spectra], $\operatorname{Spec}C$ is
the base change of $U\to V$ to $\operatorname{Spec}B$. By [lem-weil-pbc-localization-base-change],
$A\to C$ is localization at the image of $M$. If $a_1,\ldots,a_n$ generate $A$ over $R$, then
$a_i\otimes1$ generate $C$ over $B$: every pure tensor is a $B$-multiple of a polynomial in these
elements, and every tensor is a finite sum of pure tensors. Thus $C$ is of finite type over $B$ in
[def-weil-pbc-finite-type-algebra]. Uses: lem-weil-pbc-fibre-product-affine-spectra,
lem-weil-pbc-localization-base-change, def-weil-pbc-finite-type-algebra.

3. A minimal prime $Q$ of $A$ gives a generic point $\eta_Q$ of the irreducible component
$V(Q)\subset U$ by [lem-weil-pbc-spec-irreducible-components-minimal-primes]. Its closure in $Z$
is an irreducible component of $Z$: if that closure is contained in an irreducible closed subset
$H\subset Z$, then $H\cap U$ is an irreducible closed subset of $U$ containing $V(Q)$, hence
equals $V(Q)$ by maximality; the nonempty open $H\cap U$ is dense in $H$, so $H=\overline{V(Q)}$.
This is precisely the maximality in [def-weil-irreducible-components]. Since
$\overline{\{\eta_Q\}}=\overline{V(Q)}$, $\eta_Q$ is the generic point of this component as in
[def-sc-generic-point]. The assumed generic algebraicity therefore says $\kappa(Q)/\kappa(Q\cap
R)$ is algebraic. Here the residue fields are the same in the open subschemes and their ambient
schemes by [lem-weil-pbc-affine-open-stalk-localization]. Uses:
lem-weil-pbc-spec-irreducible-components-minimal-primes, def-weil-irreducible-components,
def-sc-generic-point, lem-weil-pbc-affine-open-stalk-localization.

4. Let $Q'$ be any minimal prime of $C$ and $Q_0=Q'\cap A$. By
[lem-sc-irreducible-components-cover] and
[lem-weil-pbc-spec-irreducible-components-minimal-primes], $Q_0$ contains a minimal prime $Q$ of
$A$. Since $Q_0$ avoids the image of $M$, so does $Q$. By (1) of
[lem-weil-pbc-localization-prime-residue-field-iso], $QC$ is a prime contained in $Q'$; minimality
gives $QC=Q'$ and then $Q=Q_0$. Put $q_0=Q\cap R$ and $q=Q'\cap B$. The same prime correspondence
for $R\to B$ gives $q=q_0B$, with $q_0\subseteq\mathfrak p$. Clause (3) of that node identifies
$\kappa(Q)\cong\kappa(Q')$ and $\kappa(q_0)\cong\kappa(q)$ compatibly with their structure maps.
Hence Step 3 implies that $\kappa(Q')/\kappa(q)$ is algebraic. This verifies the generic
hypothesis after localization without assuming $Z$ or $S$ globally Noetherian. Uses:
lem-sc-irreducible-components-cover, lem-weil-pbc-spec-irreducible-components-minimal-primes,
lem-weil-pbc-localization-prime-residue-field-iso.

5. Let $P\subset C$ be any prime above $\mathfrak m$. Choose a minimal prime $Q'\subseteq P$,
again using [lem-sc-irreducible-components-cover] and
[lem-weil-pbc-spec-irreducible-components-minimal-primes]. Set $q=Q'\cap B$, $E=B/q$, $D=C/Q'$,
and $r=P/Q'\subset D$. Then $E\hookrightarrow D$ is an inclusion of domains, $D$ is a finite type
$E$-algebra (use the images of the generators of $C$), and $E$ is Noetherian by
[lem-weil-pbc-finite-type-algebra-noetherian], applied to the quotient $B\to B/q$, generated by
zero extra elements. The prime $r$ contracts to $\mathfrak m/q$ in $E$. Step 4 says
$\operatorname{Frac}(D)=\kappa(Q')$ is algebraic over $\operatorname{Frac}(E)=\kappa(q)$, so
$\operatorname{trdeg}_E D=0$ by [def-kun-transcendence-degree]. Also
$\kappa(r)=\operatorname{Frac}(C/P)=\kappa(P)$ and $\kappa(\mathfrak m/q)=k$. Under
[lem-weil-pbc-spec-quotient-homeomorphism-zero-locus], chains of primes of $E$ lift to chains of
primes of $B$ containing $q$; hence their lengths are at most one by
[def-weil-pbc-krull-dimension-ring]. Uses: lem-sc-irreducible-components-cover,
lem-weil-pbc-spec-irreducible-components-minimal-primes,
lem-weil-pbc-finite-type-algebra-noetherian, def-kun-transcendence-degree,
lem-weil-pbc-spec-quotient-homeomorphism-zero-locus, def-weil-pbc-krull-dimension-ring.

6. If $q=\mathfrak m$, then $E=k$ and $\operatorname{ht}_E(\mathfrak m/q)=0$. Apply
[lem-trf-affine-dimension-inequality] to $E\hookrightarrow D$, $\mathfrak m/q$ and $r$, with all
its hypotheses checked in Step 5. It gives
$\operatorname{ht}_D(r)\le0-\operatorname{trdeg}_k\kappa(P)$. Both height and transcendence degree
are nonnegative, so $\operatorname{trdeg}_k\kappa(P)=0$. This is the vertical-component case,
including the case $\dim B=0$. Uses: lem-trf-affine-dimension-inequality.

7. If $q\ne\mathfrak m$, then $q\subsetneq\mathfrak m$. The strict chain $(0)\subsetneq\mathfrak
m/q$ in $E$ and the upper bound on chain lengths in Step 5 give $\operatorname{ht}_E(\mathfrak
m/q)=1$. Moreover $r\ne(0)$, since otherwise $P=Q'$ would have contraction both $\mathfrak m$ and
$q$. As $D$ is a domain, $(0)\subsetneq r$ gives $\operatorname{ht}_D(r)\ge1$. Apply
[lem-trf-affine-dimension-inequality] to the same inclusion and primes as in Step 6. It yields
$1\le\operatorname{ht}_D(r)\le1-\operatorname{trdeg}_k\kappa(P)$, and hence
$\operatorname{trdeg}_k\kappa(P)=0$. Thus Steps 6 and 7 cover every component through every
closed-fibre point. Uses: lem-trf-affine-dimension-inequality.

8. The closed fibre of $\operatorname{Spec}C\to\operatorname{Spec}B$ is $Y=\operatorname{Spec}F$
with $F=C/\mathfrak mC$: tensoring $C$ with $k=B/\mathfrak m$ sends $c\otimes\bar b$ to
$bc\bmod\mathfrak mC$, with inverse $\bar c\mapsto c\otimes1$. By
[lem-weil-pbc-spec-quotient-homeomorphism-zero-locus], its primes correspond to primes $P$ of $C$
over $\mathfrak m$, and its residue field at $P/\mathfrak mC$ is $\operatorname{Frac}(C/P)$. The
images of the finite algebra generators of $C$ generate $F$ over $k$, so $Y$ is of finite type
over the field $k$ by [def-weil-finite-type-morphism]. Steps 6 and 7 show that every point of $Y$
has residue transcendence degree zero over $k$. Apply part (a) of [lem-kun-closed-point-field]:
every point of $Y$ is closed. Uses: lem-weil-pbc-spec-quotient-homeomorphism-zero-locus,
def-weil-finite-type-morphism, lem-kun-closed-point-field.

9. Since all primes of $F$ are maximal, there is no strict inclusion between distinct primes. By
[def-weil-pbc-krull-dimension-ring], $\dim F\le0$, equivalently $\dim Y\le0$. Apply
[lem-weil-pbc-finite-type-dim-zero-artinian] to the finite type $k$-scheme $Y$: its underlying
space is finite and discrete. This also includes $F=0$, when the fibre is empty. Uses:
def-weil-pbc-krull-dimension-ring, lem-weil-pbc-finite-type-dim-zero-artinian.

10. The fibre $U_s$ is $\operatorname{Spec}(A\otimes_R k)$ by
[lem-weil-pbc-fibre-product-affine-spectra]. The $B$-algebra $C=A\otimes_R B$ therefore has
$C\otimes_B k\cong A\otimes_R k$, explicitly $(a\otimes b)\otimes c\mapsto a\otimes bc$, with
inverse $a\otimes c\mapsto(a\otimes1)\otimes c$. Thus $U_s\cong Y$, and the set of points of $U$
mapping to $s$ is finite by the fibre homeomorphism in [def-pc-scheme-fibre]. Apply
[pqf-lem-locqf-fibre-discrete] to $U\to V$. It is locally of finite type by
[lem-weil-pbc-lft-affine-pairs], used in both directions: an affine open $U'\subseteq U$ and an
affine open $V'\subseteq V$ with $g(U')\subseteq V'$ are affine opens of $Z$ and $S$, so $\mathcal
O_S(V')\to\mathcal O_Z(U')$ is of finite type because $g$ is locally of finite type. It is
quasi-finite at $z$. The affine neighbourhoods witnessing this for $U\to V$ are also affine open
neighbourhoods in $Z$ and $S$, so they witness quasi-finiteness of $g$ at $z$ by
[pqf-def-quasifinite]. Since $z$ was arbitrary over $s$, this proves the item. Uses:
lem-weil-pbc-fibre-product-affine-spectra, def-pc-scheme-fibre, pqf-lem-locqf-fibre-discrete,
lem-weil-pbc-lft-affine-pairs, pqf-def-quasifinite.
-/
theorem quasiFiniteAtPoint_of_generic_algebraic_of_local_dim_le_one
    {Z S : Scheme.{u}} (g : Z ⟶ S) [LocallyOfFiniteType g] (s : S)
    [IsNoetherianRing (S.presheaf.stalk s)]
    (hdim : ringKrullDim (S.presheaf.stalk s) ≤ 1)
    (hgeneric : ∀ (T : Set Z), T ∈ irreducibleComponents Z →
      ∀ (η : Z), IsGenericPoint η T →
        @Algebra.IsAlgebraic (S.residueField (g η)) (Z.residueField η) _ _
          (g.residueFieldMap η).hom.toAlgebra) :
    ∀ z : Z, g z = s → Scheme.Hom.IsQuasiFiniteAtPoint g z := by
  sorry

end AlgebraicGeometry
