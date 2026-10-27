/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Blowup.Gluing
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfCoherentFreeStalks
import WeilConjectures.Blowup.InvertibleCenter
import Mathlib.RingTheory.Flat.Localization
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Affine.Defs
import Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation
import WeilConjectures.Blowup.Affine.Principalization
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.Principalization
import WeilConjectures.AlgebraicGeometry.AffineConormalSections
import Sheaf.AlgebraicGeometry.ProjectiveLineRegularDimensionOne
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Exceptional fibres and conormal bundles of regular surface point blowups

Source: Stacks Project, resolve.tex, Tag 0AGQ (lemma-blowup), (1) and (3),
globalized by flat localization; divisors.tex, Tag 0807 for the dimension-one case
(blueprint: lem-sfb-point-blowup-exceptional-conormal).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The exceptional fibre of a regular surface point blowup has local dimension one
or two at its centre. In the first case the blowup is an isomorphism. In the second
case the fibre is an effective Cartier projective line, with conormal bundle O(1).
The centre is the actual kernel of Spec κ(p) → X, and the fibre and both projections
are Mathlib's scheme-theoretic fibre constructions.

Source: Stacks Project, resolve.tex, Tag 0AGQ, (1) and (3), and divisors.tex, Tag 0807
(blueprint: lem-sfb-point-blowup-exceptional-conormal).

Proof plan:
1. Choose an affine neighbourhood $V=\operatorname{Spec}R$ of $p$, with corresponding maximal
ideal $\mathfrak n$. By [lem-weil-pbc-affine-open-stalk-localization], $A=\mathcal
O_{X,p}=R_{\mathfrak n}$. Integrality makes $R$ a domain. Prime chains in $R_{\mathfrak n}$ give
chains of irreducible closed subsets of $X$ by taking their closures, so $d\le\dim X=2$. If
$d=0$, the prime $(0)$ in the domain $R$ equals $\mathfrak n$, hence $p$ is the generic point of
$V$ and of $X$. Its being closed would force the integral scheme $X$ to have just one point,
contradicting dimension $2$. Thus $d\in\{1,2\}$. Write $\mathcal J$ for the ideal of the reduced
closed point; its stalk at $p$ is the maximal ideal of $A$, and its stalk at every other point
is the whole local ring.

2. On each member of an affine covering with Noetherian coordinate rings, the ideal defining
$\mathcal J$ is finitely generated, by [def-weil-pbc-noetherian-ring]. Its associated ideal
sheaf is quasi-coherent by [def-sbc-closed-immersion-ideal-sheaf], and consequently coherent by
[pqf-lem-coherent-ft-locnoeth]. In particular $\mathcal J$ is a finite-type quasi-coherent
ideal, as required by the blowup principalization theorem below.

3. If $d=1$, regularity means that $\mathfrak m_A=(x)$ for one element $x$. The domain $A$ has
dimension one, so $x\ne0$, and multiplication by $x$ identifies $A$ with $\mathcal J_p$. At
every other point $\mathcal J$ has stalk equal to the local ring. Hence every stalk of this
coherent ideal is free of rank one. Apply [lem-sc-coherent-free-stalks-locally-free]; its local
free ranks are one, as seen on these stalks. Thus $\mathcal J$ is invertible, and
[cor-nagata-blowup-cartier-iso] makes $b$ an isomorphism. Its scheme-theoretic fibre over $p$ is
therefore $\operatorname{Spec}k$, by the fibre-product definition of a fibre.

4. Assume now $d=2$. Use the affine neighbourhood $V=\operatorname{Spec}R$ above and
$T=R\setminus\mathfrak n$. The map $g:\operatorname{Spec}A\to V\to X$ is flat. Indeed, a prime
of $A=R_{\mathfrak n}$ corresponds to a prime $\mathfrak q\subseteq\mathfrak n$ of $R$; its
stalk map is $R_{\mathfrak q}\to (R_{\mathfrak n})_{\mathfrak qR_{\mathfrak n}}$, an isomorphism
by the fraction descriptions in [lem-weil-pbc-affine-open-stalk-localization]: its inverse sends
$(a/s)/(b/u)$ to $au/(sb)$, where $s,u\notin\mathfrak n$ and $b\notin\mathfrak q$, so
$sb\notin\mathfrak q$. Thus these stalk maps are flat by [lem-weil-pbc-localization-flat], as
required by [def-weil-flat-morphism]. The ideal $\mathcal J$ extends to $\mathfrak m_A$. Apply
the comparison constructed in [def-nagata-blowup-flat-base-change-map] and its isomorphism
assertion [thm-nagata-blowup-flat-base-change]. This identifies $Y=\operatorname{Bl}_{\mathfrak
m_A}\operatorname{Spec}A$ with $\operatorname{Spec}A\times_X X'$. Denote its projection by
$h:Y\to X'$. Taking the further fibre over $\operatorname{Spec}k$ identifies
$F=Y\times_{\operatorname{Spec}A}\operatorname{Spec}k$ canonically with $E$, with the same
$k$-structure. On every affine open $\operatorname{Spec}C$ of $b^{-1}(V)$, the corresponding
open of $Y$ is $\operatorname{Spec}(T^{-1}C)$.

5. Choose generators $x,y$ of $\mathfrak m_A$, using regularity and $d=2$. Both $(x,y)$ and
$(y,x)$ are regular sequences by [lem-weil-pbc-regular-local-generators-regular-sequence]. First
identify $Y$ with the affine blowup $\operatorname{Bl}_{\mathfrak
m_A}(\operatorname{Spec}A)=\operatorname{Proj}\mathcal R_A(\mathfrak m_A)$: for the one-member
affine cover $\{\operatorname{Spec}A\}$ the glue datum of [def-nagata-global-blowup-glue-data]
consists of the single local model $\mathsf
B_{\operatorname{Spec}A}=\operatorname{Bl}_{\mathfrak m_A}(\operatorname{Spec}A)$ of
[def-nagata-global-blowup-local-model], and [prop-nagata-global-blowup-cover-independent]
identifies the global blowup over $\operatorname{Spec}A$ with it. By
[prop-nagata-affine-blowup-chart-cover] the $x$- and $y$-charts then cover $Y$;
[prop-nagata-affine-blowup-chart] identifies their maps [def-nagata-affine-blowup-chart-map]
with the standard opens $D_+(xu)$ and $D_+(yu)$ of the Rees Proj, where $u$ is its degree-one
bookkeeping variable. Their rings, by [lem-trf-blowup-chart-regular-sequence-presentation], are
$$C_x=A[t]/(xt-y),\qquad C_y=A[s]/(ys-x),$$ where $t=y/x$ and $s=x/y$. By
[lemma-nagata-chart-extended-ideal-principal], the ideal $\mathfrak m_A\mathcal O_Y$ is $(x)$
and $(y)$ on these charts. Consequently the fibre charts are $C_x/(x)=k[t]$ and $C_y/(y)=k[s]$.
On the intersection, $t$ is invertible and $s=t^{-1}$: the intersection is the standard open
where the other degree-one generator of the Rees algebra is invertible relative to the chosen
generator, equivalently $D(t)$ on the $x$-chart. Thus these fibre charts glue precisely to the
two charts of [def-sc-p1-standard]. They give a $k$-isomorphism $r:E=F\xrightarrow{\sim}\mathbf
P^1_k$.

6. By [thm-nagata-blowup-principalizes-center], $\mathcal I=\mathcal J\mathcal O_{X'}$ is an
invertible ideal defining an effective Cartier divisor. This divisor is exactly the
scheme-theoretic fibre $E$, since the reduced closed point has ideal $\mathcal J$: on an affine
open $\operatorname{Spec}C$ of $b^{-1}(V)$ the fibre is $\operatorname{Spec}(C\otimes_R
R/\mathfrak n)=\operatorname{Spec}(C/\mathfrak nC)$, with $\mathfrak
nC=\Gamma(\operatorname{Spec}C,\mathcal J\mathcal O_{X'})$ and $R/\mathfrak n=R_{\mathfrak
n}/\mathfrak nR_{\mathfrak n}=k$ as $\mathfrak n$ is maximal, while over $X\setminus\{p\}$ the
fibre is empty and $\mathcal J\mathcal O_{X'}$ is the unit ideal. We also need its conormal on
the localized model $Y$. The conormal map of [lem-weil-pbc-closed-immersion-conormal-functorial]
for $h$ identifies the original conormal on $E$ with that on $F$. Indeed, on an affine open with
ideal $I\subset C$, [lem-weil-pbc-affine-conormal-sections] writes this map as
$$I/I^2\longrightarrow (T^{-1}I)/(T^{-1}I)^2,\qquad a\bmod I^2\longmapsto a/1\bmod
(T^{-1}I)^2.$$ Here $(T^{-1}I)^2=T^{-1}(I^2)$: a product $(a/t)(b/u)$ has numerator $ab\in I^2$,
and a fraction $ab/t$ equals $(a/t)(b/1)$, with finite sums giving both inclusions. After
restriction to $E$, every element of $T$ is already a unit (its nonzero residue in $k$ is
invertible). Thus its inverse sends $a/t$ to $t^{-1}a$ in $I/I^2$. This is well-defined:
equality of localized representatives means that an element of $T$ kills their cross-multiplied
difference modulo $I^2$, and multiplication by that element is invertible on the $C/I$-module
$I/I^2$. The two composites are identities. The formulas commute with restriction of fractions,
so agree on overlaps and identify the conormal sheaves on all of $E$.

7. On $\operatorname{Spec}C_x$ the element $x$ is a nonzerodivisor: $C_x=A[\mathfrak
m_A/x]\subset A_x$ by [def-nagata-blowup-chart-ring], and $A$ is a domain. Likewise $y$ is a
nonzerodivisor on the other chart. Hence the conormal modules given by
[lem-weil-pbc-affine-conormal-sections] are $(x)/(x^2)\cong k[t]$ with basis $[x]$, and
$(y)/(y^2)\cong k[s]$ with basis $[y]$. Explicitly $\bar a\mapsto ax\bmod x^2$ is bijective
because $x$ is a nonzerodivisor, and similarly for $y$. On the overlap $[y]=t[x]$, since $y=tx$
already in the ambient chart. In [def-sc-p1-standard], the frames $g_0,g_1$ of $\mathcal O(1)$
satisfy $g_1=tg_0$. Sending $r^*g_0$ to $[x]$ and $r^*g_1$ to $[y]$ therefore glues to an
isomorphism $r^*\mathcal O(1)\cong\mathcal C_{E/X'}$. The two displayed free rank-one modules
also verify invertibility directly.

8. Finally [lem-sc-p1-regular-dimension-one] gives Noetherianity, regularity and dimension one
for $\mathbf P^1_k$, and [lemma-nagata-projective-space-base-change-proper] gives its properness
over $k$, taking the two-element index set and base $\operatorname{Spec}k$. It is integral: its
two standard affine charts have domain rings $k[t]$ and $k[s]$, are reduced, and have common
nonempty dense open $\operatorname{Spec}k[t,t^{-1}]$. Each chart is irreducible, and the density
of their common open makes their union irreducible; the union is also reduced and nonempty. The
equivalence in [def-pc-integral-scheme] proves integrality. All these properties pass along the
$k$-isomorphism $r$ to $E$, completing the $d=2$ case. -/
theorem point_blowup_exceptional_conormal
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hX : IsRegularScheme X) (hdim : topologicalKrullDim X = 2)
    (p : X) (hp : IsClosed ({p} : Set X)) :
    (ringKrullDim (X.presheaf.stalk p) = 1 ∨
      ringKrullDim (X.presheaf.stalk p) = 2) ∧
    IsClosedImmersion ((X.fromSpecResidueField p).ker.blowupMap.fiberι p) ∧
    (ringKrullDim (X.presheaf.stalk p) = 1 →
      IsIso (X.fromSpecResidueField p).ker.blowupMap ∧
      Nonempty ((X.fromSpecResidueField p).ker.blowupMap.fiber p ≅
        Spec (X.residueField p))) ∧
    (ringKrullDim (X.presheaf.stalk p) = 2 →
      IsIntegral ((X.fromSpecResidueField p).ker.blowupMap.fiber p) ∧
      IsRegularScheme ((X.fromSpecResidueField p).ker.blowupMap.fiber p) ∧
      IsNoetherian ((X.fromSpecResidueField p).ker.blowupMap.fiber p) ∧
      topologicalKrullDim ((X.fromSpecResidueField p).ker.blowupMap.fiber p) = 1 ∧
      IsProper ((X.fromSpecResidueField p).ker.blowupMap.fiberToSpecResidueField p) ∧
      ((X.fromSpecResidueField p).ker.blowupMap.fiberι p).ker.IsInvertible ∧
      Modules.IsInvertible
        ((Modules.tensorPullback ((X.fromSpecResidueField p).ker.blowupMap.fiberι p)).obj
          ((X.fromSpecResidueField p).ker.blowupMap.fiberι p).ker.toModules) ∧
      ∃ r : (X.fromSpecResidueField p).ker.blowupMap.fiber p ≅
          ProjectiveLine (Spec (X.residueField p)),
        r.hom ≫ (ProjectiveLine (Spec (X.residueField p)) ↘ Spec (X.residueField p)) =
          (X.fromSpecResidueField p).ker.blowupMap.fiberToSpecResidueField p ∧
        Nonempty
          ((Modules.tensorPullback ((X.fromSpecResidueField p).ker.blowupMap.fiberι p)).obj
              ((X.fromSpecResidueField p).ker.blowupMap.fiberι p).ker.toModules ≅
            (Modules.tensorPullback r.hom).obj
              (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (X.residueField p)) 1))) := by
  sorry

end AlgebraicGeometry.Scheme
