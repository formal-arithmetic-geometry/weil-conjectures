/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Sheaf.RingTheory.StrictHenselizationCompletionNoetherian
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Conservative
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Sheaf.AlgebraicGeometry.LogRegularCompletedChart
import Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction
import Sheaf.AlgebraicGeometry.LogRegularSharpChart
import Sheaf.RingTheory.LogRegularSaturationNormality
import Sheaf.TraceFormula.CompleteToricMonomialFactors

/-!
# Normality and divisorial description of a log regular structure

Source: Illusie--Laszlo--Orgogozo, Exposé VI, §1.4 and Exposé VIII, §§3.4.1, 3.5
(blueprint: lem-trf-log-regular-divisorial-structure).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A locally Noetherian fs log regular scheme is normal, and its log structure is
divisorial on the dense open locus where the characteristic is trivial.
Source: ILO, Exposé VI, §1.4 and Exposé VIII, §§3.4.1, 3.5
(blueprint: lem-trf-log-regular-divisorial-structure).

Proof plan (the seven steps of the DAG node):

1. Fix a geometric point $\bar y$ over $y$, set $A_0=\mathcal O_{Y,y}$ and $A=\mathcal
O^{\mathrm{sh}}_{Y,\bar y}$, and choose a sharp chart $P=\overline N_{\bar y}\to N$ on an affine
pointed etale neighbourhood $W$ by the sharp-chart lemma. In particular $P$ is finitely generated,
integral, saturated and sharp. The chart definition gives $N_{\bar y}=P\oplus A^\times$. Replacing
that sharp chart and its affine neighbourhood $W$ if necessary, as permitted by the completed-
chart lemma (from now on $W$ and $a:P\to A$ denote the replacement), it identifies $\widehat A$,
respecting these monomials, with the complete monoid model $B_k(P,n)$ if $A$ contains a field, and
with $B_C(P,n)/(\theta)$ otherwise. By normality of these saturated models, $\widehat A$ is a
normal domain. This is only the fs case: no saturation of a non-saturated log scheme is
introduced.
Uses: lem-trf-log-regular-sharp-chart, def-trf-fs-log-blowup, lem-trf-log-regular-completed-chart,
lem-trf-log-regular-saturation-normality.

2. By the affine strict-local comparison lemma, applied to an affine open $\operatorname{Spec}D\ni
y$ (so $D_{\mathfrak p}=A_0$) and the separable closure $K$ of $\kappa(y)$ in $\Omega$, $A$ is
isomorphic as an $A_0$-algebra to an algebraic strict henselization $A_0^{\mathrm{sh}}$ relative
to $K$, by a local isomorphism. Its index pairs $(S,\chi:S\to K)$ are the pointed etale triples
$(S,\ker\chi,\text{induced }\kappa(\ker\chi)\to K)$ over the closed point, with the same
morphisms, so $A_0^{\mathrm{sh}}$ is the triples colimit of the two lemmas below. Hence $A_0\to A$
and $A\to\widehat A$ ($\widehat A$ the completion at the maximal ideal $\mathfrak m_{A_0}A$) are
faithfully flat, by the strict-henselization and completed-strict-henselization lemmas (their
Noetherian hypothesis holds because $Y$ is locally Noetherian). Descend normal-domainness along
each map, as follows. For a faithfully flat $E\to F$ with $F$ a normal domain, ideal contraction
for the zero ideal makes $E\to F$ injective, so $E$ is a domain. If $a/b\in\operatorname{Frac}E$
is integral over $E$, its image is integral over $F$ by the same monic equation, hence lies in
$F$. Thus $a\in bF\cap E=bE$ by ideal contraction, so $a/b\in E$. Apply this argument first to
$A\to\widehat A$ and then to $A_0\to A$. All local rings of $Y$ are therefore normal domains.
Uses: lem-exc-affine-strict-local-ring-comparison, lem-sc-strict-henselization-faithfully-flat,
lem-sc-strict-henselization-completion-noetherian, lem-weil-pbc-faithfully-flat-ideal-contraction.

3. On the chart $W$, choose generators $p_1,\ldots,p_r$ of $P$ and put $s=\prod_i a(p_i)$, with
empty product $1$. The associated-log chart formula says that the characteristic is zero exactly
where all these generators are units. Hence $V\times_Y W=D(s)$, an open subset of $W$. Etale maps
are open, so their images show that $V$ is open in $Y$. Apply monoidal-ideal contraction at $\bar
y$ to the empty monoid ideal: no $a(p)$ is zero in $A$, and therefore $s\neq0$ in the domain $A$
of step 2. Thus $D(s)\subset\operatorname{Spec}A$ is nonempty. Every open neighbourhood of the
closed point of $\operatorname{Spec}A$ is the whole spectrum; the preimage of every neighbourhood
of $y$ contains that closed point, and hence meets $D(s)$. Its image lies in $V$. Since $y$ was
arbitrary, $V$ is dense. Every section of $N$ restricts to a unit on $V$, by the chart formula or
the definition of the triviality locus.
Uses: def-trf-fs-log-blowup, lem-weil-pbc-etale-morphism-open-map, lem-trf-log-regular-monoidal-
ideal-contraction.

4. The structural map is injective on the geometric stalk at $\bar y$. Indeed, if $u a(p)=v a(q)$
with $u,v\in A^\times$, then $(a(p))=(a(q))$. Contraction of the monoid ideals $p+P$ and $q+P$
gives $p+P=q+P$. Thus $p=q+r$ and $q=p+t$ for $r,t\in P$; integrality gives $r+t=0$, and sharpness
gives $r=t=0$, so $p=q$. Since $a(p)\neq0$ in the domain $A$, cancellation gives $u=v$. Together
with $N_{\bar y}=P\oplus A^\times$, this proves injectivity.
Uses: lem-trf-log-regular-monoidal-ideal-contraction.

5. Let a germ of $\mathcal O_Y\cap j_*\mathcal O_V^\times$ at $\bar y$ be represented by a regular
function $f$ on a pointed etale neighbourhood, invertible on its intersection with $V$. Refine
with the chart neighbourhood of step 1. Pullback of the inverse to $\operatorname{Spec}A[1/s]$
shows that $f$ is a unit in $A[1/s]$. Write an inverse as $g/s^m$. The localization equality gives
$s^l(fg-s^m)=0$ for some $l\geq0$; since $A$ is a domain and $s\neq0$, $fg=s^m=a(m\sum_i p_i)$.
Pass to the completed monoid model of step 1. The complete-toric monomial-factor lemma, applied to
this equation, gives $f=\widehat u\,a(p)$ in $\widehat A$ for some $p\in P$ and $\widehat
u\in\widehat A^\times$. The same argument covers $s=1$.
Uses: lem-trf-complete-toric-monomial-factors.

6. We have $(f)\widehat A=(a(p))\widehat A$. By faithfully flat ideal contraction along
$A\to\widehat A$, both inclusions descend: $f=a(p)u$ and $a(p)=fv$ for some $u,v\in A$.
Substitution gives $a(p)=a(p)uv$. Since $a(p)\neq0$ and $A$ is a domain, $uv=1$; hence $u\in
A^\times$. Consequently the germ $f$ is the image of $(p,u)\in P\oplus A^\times=N_{\bar y}$. This
proves surjectivity onto the intersection at each geometric point; step 4 gives injectivity. The
structural map factors through the intersection by step 3. Geometric-stalk detection of
isomorphisms of etale sheaves of sets now identifies $N$ with $\mathcal O_Y\cap j_*\mathcal
O_V^\times$, compatibly with multiplication and the structural maps.
Uses: lem-weil-pbc-faithfully-flat-ideal-contraction, lem-weil-pbc-sets-etale-iso-on-geometric-
stalks.

7. Let $\operatorname{Spec}C\subseteq Y$ be an integral affine open. For each maximal ideal
$\mathfrak m$ of $C$, the local ring $C_{\mathfrak m}=\mathcal O_{Y,y_{\mathfrak m}}$ is a normal
domain by step 2. The local-normality criterion therefore makes $C$ a normal domain, equivalently
integrally closed in its fraction field.
Uses: lem-weil-pbc-normal-domain-of-local-normal.
-/
theorem logRegular_divisorialStructure
    (X : FineSaturatedLogScheme.{u}) (hX : X.IsLogRegular) :
    (∃ U : X.scheme.Opens,
      Dense (U : Set X.scheme) ∧
        X.logStructure.trivialityLocus = (U : Set X.scheme) ∧
        Presheaf.IsSheaf X.scheme.smallEtaleTopology
          (divisorialLogPresheaf U.ι) ∧
        ∃ (e : X.logStructure.monoidSheaf.obj ≅ divisorialLogPresheaf U.ι),
          e.hom ≫ divisorialStructuralMap U.ι = X.logStructure.alpha ∧
          ∀ (W : X.scheme.Etale) (s : X.logStructure.monoidSheaf.obj.obj (op W)),
            IsUnit ((pullback.fst W.hom U.ι).appTop (X.logStructure.alpha.app (op W) s))) ∧
      (∀ y : X.scheme,
        IsDomain (X.scheme.presheaf.stalk y) ∧
          IsIntegrallyClosed (X.scheme.presheaf.stalk y)) ∧
      (∀ (U : X.scheme.Opens), IsAffineOpen U → IsIntegral U.toScheme →
        IsIntegrallyClosed (Γ(X.scheme, U))) := by
  sorry

end AlgebraicGeometry
