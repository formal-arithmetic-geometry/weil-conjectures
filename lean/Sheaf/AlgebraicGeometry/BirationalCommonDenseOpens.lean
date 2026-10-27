/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Common dense opens for a birational morphism

Source: Stacks Project, Morphisms, Tag 0BAC, lemma-birational-birational, alternative (2),
with birationality as in Tag 01RO (blueprint: lem-sfb-birational-common-dense-opens).
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A locally finitely presented morphism bijecting component generic points and inducing
isomorphisms on their local rings restricts to an isomorphism between dense open subschemes.

Source: Stacks Project, Morphisms, Tag 0BAC, lemma-birational-birational, alternative (2),
and Tag 01RO, definition-birational (blueprint: lem-sfb-birational-common-dense-opens).

Proof:
1. If there are no irreducible components, both schemes are empty and we take $U=Y$, $V=X$.
   Otherwise enumerate the component generic points as $\eta_1,\ldots,\eta_r$ in $Y$ and
   $\xi_i=f(\eta_i)$ in $X$, using the assumed bijection. By sobriety their closures are exactly
   the respective components $Y_i$ and $X_i$. Set $Y_i^\circ=Y\setminus\bigcup_{j\ne i}Y_j$ and
   $X_i^\circ=X\setminus\bigcup_{j\ne i}X_j$. These are open because the component families are
   finite. Each contains its own generic point: membership of $\eta_i$ in another closed component
   would force $Y_i\subseteq Y_j$, contrary to maximality; the same argument applies to $X$. They
   are pairwise disjoint and contained in their respective components. Every nonempty open subset
   of $Y_i^\circ$ contains $\eta_i$: its complement in $Y_i$ is closed and would contain the
   closure of $\eta_i$ if it contained $\eta_i$. Thus $\eta_i$ remains generic on every
   neighbourhood inside $Y_i^\circ$, and likewise for $\xi_i$.
2. For each $i$, choose an affine open $V_i^0=\operatorname{Spec}B\subseteq X_i^\circ$ containing
   $\xi_i$. Choose an affine open $U_i^0=\operatorname{Spec}A\subseteq Y_i^\circ\cap
   f^{-1}(V_i^0)$ containing $\eta_i$; the latter open contains $\eta_i$ since $f(\eta_i)=\xi_i$.
   The affine-chart square identifies this restriction of $f$ with $\operatorname{Spec}\varphi$
   for its induced ring map $\varphi:B\to A$. Both affine spectra have a generic point for the
   whole space by Step 1, hence are irreducible: two nonempty opens both contain that point. The
   component/minimal-prime description of spectra therefore gives unique minimal primes $\mathfrak
   q$ of $B$ and $\mathfrak p$ of $A$, representing $\xi_i$ and $\eta_i$. Carry out Steps 3--6 for
   each $i$ with these rings.
3. The map on affine points gives $\varphi^{-1}(\mathfrak p)=\mathfrak q$. The affine stalk-map
   formula identifies the stipulated generic local-ring isomorphism with the induced map
   $B_{\mathfrak q}\to A_{\mathfrak p}$. Apply [lem-sfb-birational-generic-localization]: its
   unique-minimal-prime and contraction hypotheses were established in Step 2 and the first
   sentence here. Consequently the canonical map $B_{\mathfrak q}\to A_{\mathfrak
   q}=\varphi(B\setminus\mathfrak q)^{-1}A$ is an isomorphism. Here and below $A_g$ means
   localization of $A$ at $\varphi(g)$.
4. The affine-chart finite-presentation theorem applied directly to $f,U_i^0,V_i^0$ gives $A\cong
   B[t_1,\ldots,t_n]/(h_1,\ldots,h_m)$; let $x_j$ be the images of the variables. Surjectivity of
   $B_{\mathfrak q}\to A_{\mathfrak q}$ writes $x_j/1=\varphi(b_j)/\varphi(s_j)$ for some
   $s_j\notin\mathfrak q$. The equality criterion for fractions supplies
   $s_j^\prime\notin\mathfrak q$ with $\varphi(s_j^\prime)(\varphi(b_j)-\varphi(s_j)x_j)=0$ in
   $A$. Put $g=\prod_j s_js_j^\prime\notin\mathfrak q$ (empty product $1$). Every factor becomes a
   unit in $B_g$ and $A_g$, so $x_j=\varphi(b_j)/\varphi(s_j)$ in $A_g$. The map $B_g\to A_g$ is
   surjective: $A_g$ is generated as a ring by the images of $B$, the $x_j$, and
   $\varphi(g)^{-1}$, all now in its image.
5. Localizing the displayed presentation gives $A_g\cong B_g[t_1,\ldots,t_n]/(h_1,\ldots,h_m)$: a
   map from either ring into any $B_g$-algebra amounts to choosing $n$ elements satisfying the
   same relations. Thus $A_g$ is finitely presented over $B_g$. Apply [lem-weil-pbc-finite-
   presentation-surjection-kernel-fg] with coefficient ring $B_g$, target $A_g$, and zero
   polynomial variables, to obtain finitely many generators $c_1,\ldots,c_a$ of $J=\ker(B_g\to
   A_g)$. Write $c_j=b_j/g^{e_j}$. Its image in $A_{\mathfrak q}$ is zero, and injectivity in Step
   3 implies $b_j/1=0$ in $B_{\mathfrak q}$. The fraction equality criterion gives
   $u_j\notin\mathfrak q$ with $u_jb_j=0$ in $B$. Put $h=g\prod_j u_j\notin\mathfrak q$. The map
   $B_h\to A_h$ remains surjective by the same generators as in Step 4. It is injective as well:
   if $b/h^e$ maps to zero, then $\varphi(h)^k\varphi(b)=0$ in $A$ for some $k$. Hence $h^kb/1\in
   J$ inside $B_g$. All $c_j$ vanish in $B_h$, so $h^kb/1=0$ there; since $h$ is a unit,
   $b/h^e=0$. We have an isomorphism $B_h\xrightarrow{\sim}A_h$.
6. Let $V_i=D(h)\subseteq V_i^0$ and $U_i=D(\varphi(h))\subseteq U_i^0$. Principal-localization
   open immersions identify these with $\operatorname{Spec}B_h$ and $\operatorname{Spec}A_h$. The
   fraction map $B_h\to A_h$ extends $\varphi$ and commutes with localization maps; applying the
   contravariant functor $\operatorname{Spec}$ gives the corresponding commutative square. Thus
   $f|_{U_i}:U_i\to V_i$ is precisely $\operatorname{Spec}(B_h\to A_h)$. Functoriality applied to
   the inverse ring isomorphism from Step 5 makes this restriction an isomorphism. The opens
   contain $\xi_i$ and $\eta_i$, respectively, since $h\notin\mathfrak q$ and
   $\varphi^{-1}(\mathfrak p)=\mathfrak q$. Each $U_i$ remains inside $Y_i^\circ$ and each $V_i$
   inside $X_i^\circ$.
7. Set $U=\bigcup_iU_i$ and $V=\bigcup_iV_i$. The pairwise disjoint open pieces identify the
   restricted map $f|_U$ with the piecewise isomorphisms $U_i\to V_i$. Explicitly its inverse
   sends a point of $V_i$ by the inverse of this isomorphism. It is continuous since the $V_i$
   form an open partition. On any open $W\subseteq V$, the sheaf axiom for the disjoint cover
   $W=\coprod_i(W\cap V_i)$ identifies sections with the product of the section rings on the
   pieces (the overlaps are empty); the inverse sheaf maps on the pieces give inverse ring maps on
   these products, compatible with restrictions. These define the inverse morphism of locally
   ringed spaces, since its maps on local rings are the local inverses. Hence $f|_U:U\to V$ is an
   isomorphism of open subschemes. Finally $U$ contains every $\eta_i$, so its closure contains
   every $Y_i=\overline{\{\eta_i\}}$, and hence all of $Y$; similarly $V$ is dense in $X$. The
   desired source open is the union of the selected $U_i$, which need not exhaust $f^{-1}(V)$.
-/
theorem exists_common_dense_opens_isIso_of_birational
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFinitePresentation f]
    (hX : (irreducibleComponents X).Finite) (hY : (irreducibleComponents Y).Finite)
    (hgeneric : Set.BijOn f (genericPoints Y) (genericPoints X))
    (hstalk : ∀ η : Y, η ∈ genericPoints Y → IsIso (f.stalkMap η)) :
    ∃ (U : Y.Opens) (V : X.Opens), Dense (U : Set Y) ∧ Dense (V : Set X) ∧
      ∃ hUV : U ≤ f ⁻¹ᵁ V, IsIso (f.resLE V U hUV) := by
  sorry

end AlgebraicGeometry
