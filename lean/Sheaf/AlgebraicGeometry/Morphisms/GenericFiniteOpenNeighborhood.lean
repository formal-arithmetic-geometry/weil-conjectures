/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.GroupTheory.MonoidLocalization.Away
import Sheaf.AlgebraicGeometry.FiniteDiscreteFiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.RingTheory.MinimalPrimeFiniteTypeFiniteAway

/-!
# Finiteness over an open containing all component generic points

Source: Stacks Project, Morphisms of Schemes, Tag 02NW, lemma-generically-finite,
equivalence (1) and (4), applied to every component generic point.
(blueprint: lem-weil-pbc-generic-finite-morphism-open-neighborhood)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A quasi-compact, quasi-separated, locally finite type morphism to a Noetherian scheme
with finite set-theoretic fibres at component generic points is finite over a dense open
containing all component generic points.

Source: Stacks Project, Tag 02NW, lemma-generically-finite, (1) implies (4), followed by
union over component generic points.
(blueprint: lem-weil-pbc-generic-finite-morphism-open-neighborhood)

Proof (the node's six steps):
1. Fix a generic point $\eta$ of a component of $Y$ and choose an affine neighbourhood
$V_0=\operatorname{Spec}R$. Put $X_0=f^{-1}(V_0)$ and $f_0:X_0\to V_0$. The open-fibre-product
identification and quasi-compact base change make $f_0$ quasi-compact; also $X_0$ is quasi-compact
by the definition. To check $X_0$ quasi-separated directly, take affine opens $A,B\subseteq X_0$.
The open-fibre-product lemma identifies $A\times_{V_0}B$ with an open of $X\times_YX$, and the
affine tensor-product lemma makes it affine, hence quasi-compact. Its preimage under the
quasi-compact diagonal of $f$ is $A\cap B$, hence quasi-compact. The affine-cover criterion now
proves $X_0$ quasi-separated. The intersection of the component of $\eta$ with $V_0$ is a
component of $V_0$: any irreducible subset containing it has closure in $Y$ containing the
original component, hence equals that component. Thus $\eta$ is still generic in $V_0$.

Dependencies: def-pc-scheme, def-weil-finite-type-morphism, def-weil-quasi-separated-morphism,
lem-weil-pbc-open-fibre-product, lem-pc-quasi-compact-base-change,
lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-quasi-separated-affine-cover-criterion.

2. Write $f^{-1}(\{\eta\})=\{\xi_1,\ldots,\xi_n\}$. The finite-fibre lemma gives a discrete scheme
fibre, and the fibre homeomorphism gives no nontrivial specializations among the $\xi_i$. For any
generalization $x$ of $\xi_i$ in $X_0$, $f(x)$ is a generalization of $\eta$. There is no proper
generalization of the generic point of a component: the closure of any such generalization is
irreducible and contains that maximal component, so equals it, and uniqueness of its generic point
forces equality. Hence $f(x)=\eta$ and discreteness forces $x=\xi_i$. Each $\xi_i$ lies in an
irreducible component of $X_0$; its generic point exists by sobriety, is a generalization of
$\xi_i$, and therefore equals $\xi_i$. Distinct $\xi_i$ belong to distinct components.

Dependencies: pqf-lem-locqf-fibre-discrete, def-pc-scheme-fibre, lem-weil-pbc-scheme-sober,
lem-sc-irreducible-components-cover, def-sc-generic-point, def-weil-irreducible-components.

3. If $n>0$, apply the affine-neighbourhood theorem to $X_0$, the finitely many components just
obtained, and $x=\xi_1$. This gives an affine open $U=\operatorname{Spec}S\subseteq X_0$
containing the entire fibre over $\eta$. If $n=0$, use the empty affine open
$U=\operatorname{Spec}(0)$. In both cases $U$ is affine and contains every point over $\eta$.

Dependencies: lem-chow-affine-through-generic-points, def-weil-affine-spectrum.

4. The affine-pairs finite-type criterion applied to $U\subseteq X$, $V_0\subseteq Y$ makes the
induced map $\varphi:R\to S$ of finite type. The prime $\mathfrak p$ of $\eta$ is minimal by the
spectrum/component correspondence: $\overline{\{\mathfrak p\}}=V(\mathfrak p)$, so a strictly
smaller prime would contradict maximality of that component. The primes of $S$ contracting to
$\mathfrak p$ are precisely the points of $U$ mapping to $\eta$, hence form a finite set. Apply
the algebraic localization lemma to obtain $g\notin\mathfrak p$ with $R_g\to S_{\varphi(g)}$
finite. Put $V_1=D(g)\subseteq V_0$ and $U_1=U\cap f^{-1}(V_1)=D(\varphi(g))$. The basic-open
pullback identity and principal-localization open immersion identify these with the affine schemes
$\operatorname{Spec}R_g$ and $\operatorname{Spec}S_{\varphi(g)}$. Their induced ring map sends
$a/g^k$ to $\varphi(a)/\varphi(g)^k$: it agrees with $\varphi$ on $R$ and preserves inverses of
the now invertible $g$. Thus it is exactly the finite localized map just obtained. The
affine-cover criterion for finite morphisms, applied to the one-member cover of $V_1$, shows
$U_1\to V_1$ finite.

Dependencies: lem-weil-pbc-lft-affine-pairs,
lem-weil-pbc-spec-irreducible-components-minimal-primes, def-weil-affine-spectrum,
lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away, lem-weil-pbc-basic-open-pullback,
lem-weil-pbc-principal-localization-open-immersion, def-weil-ring-localization-away,
lem-weil-pbc-finite-local-on-target.

5. The closed subset $Z=X_0\setminus U$ has $\eta\notin f_0(Z)$ because $U$ contains the full
fibre. By the closed-subset construction choose a closed immersion $i:T\to X_0$ with image $Z$,
and put $j=f_0\circ i:T\to V_0$. This composite is quasi-compact: over any affine open $A\subseteq
V_0$, its inverse image is homeomorphic to the closed subset $Z\cap f_0^{-1}(A)$ of the
quasi-compact space $f_0^{-1}(A)$, hence is quasi-compact. If $\eta\in\overline{j(T)}$, the
closure-specialization theorem gives $t\in T$ with $j(t)$ specializing to $\eta$. As proved in
step 2, the component generic point $\eta$ has no proper generalization, so $j(t)=\eta$,
contradicting $\eta\notin f_0(Z)$. Consequently $W=V_0\setminus\overline{j(T)}$ is open, contains
$\eta$, and $f_0^{-1}(W)\cap Z=\varnothing$. Choose a principal open $V_\eta=D(h)$ of $V_0$ with
$\eta\in V_\eta\subseteq W\cap V_1$. Then $f^{-1}(V_\eta)\subseteq U$, so it equals $U_1\cap
f^{-1}(V_\eta)$ as an open subscheme. It is therefore the restriction of the finite morphism
$U_1\to V_1$ to $V_\eta$, hence finite by target restriction.

Dependencies: lem-weil-pbc-closed-subset-closed-subscheme, def-weil-closed-immersion,
def-weil-finite-type-morphism, lem-sc-picard-closure-specialization,
lem-weil-pbc-spec-localization-away-basic-open, lem-weil-pbc-finite-local-on-target.

6. Perform the preceding construction for every generic point $\eta$ and set $V=\bigcup_\eta
V_\eta$. Each $V_\eta$ is an affine open of $Y$, hence of $V$, and these opens cover $V$. The
finite-local-on-target lemma shows $f^{-1}(V)\to V$ finite. The union contains every component
generic point. For any $y\in Y$, choose an irreducible component containing $y$ and its generic
point $\eta$. Since $\eta\in V$ and $y\in\overline{\{\eta\}}$, one has $y\in\overline V$, so $V$
is dense. If $Y$ is empty, take $V=\varnothing$; the same cover criterion is vacuous and its
preimage is empty. No intersection of the different $V_\eta$ is taken, since such an intersection
could lose other generic points.

Dependencies: lem-weil-pbc-finite-local-on-target, lem-sc-irreducible-components-cover,
lem-weil-pbc-scheme-sober, def-sc-generic-point.
-/
theorem Scheme.Hom.exists_dense_open_isFinite_of_finite_generic_fibers
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] [CompactSpace Y]
    (hfinite : ∀ (Z : Set Y), Z ∈ irreducibleComponents Y →
      ∀ (η : Y), IsGenericPoint η Z → (f ⁻¹' {η}).Finite) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧
      (∀ (Z : Set Y), Z ∈ irreducibleComponents Y →
        ∀ (η : Y), IsGenericPoint η Z → η ∈ V) ∧
      IsFinite (f ∣_ V) := by
  sorry

end AlgebraicGeometry
