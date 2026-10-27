/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ZariskiLogStructure
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.TraceFormula.FgCommutativeMonoidFinitePresentation
import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks
import Sheaf.AlgebraicGeometry.FineLogStalkChartSpreading
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Affine Zariski fs charts compatible with étale association

Source: ILO, Exposé VIII 3.3.4(ii), printed p. 107; fs refinement using VI 1.6,
VIII 3.3.13, printed pp. 70, 108--109 (blueprint: lem-trf-zariski-fs-monoid-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A prescribed Zariski log structure with fs étale association has an affine
Zariski fs chart at every point; the same section homomorphism is an étale chart.

Source: ILO VIII 3.3.4(ii), VI 1.6, VIII 3.3.13
(blueprint: lem-trf-zariski-fs-monoid-chart).

Proof (the eight steps of the DAG node):
1. Fix $x\in X$, a geometric point $\bar x$ over it, and an fs etale chart $Q$ near $\bar x$. Put
$A=\mathcal O_{X,x}$, $B=\mathcal O_{X,\bar x}$ and $L=(M_{\mathrm{Zar}})_x$. The Zariski-stalk
unit-extension lemma says that $L$ is integral, has units $A^\times$, and identifies its
sharpening $P=L/A^\times$ with $(Q-E)/E^{\mathrm{gp}}$, where $E$ is the face mapping to units in
$B$. Face sharpening therefore makes $P$ sharp fine saturated and $P^{\mathrm{gp}}$ finite free.
Apply the integral-monoid splitting lemma to $L$: it gives $j:P\to L$ and an isomorphism $P\oplus
A^\times\to L$, $(p,u)\mapsto j(p)u$. No nonzero $p\in P$ has $\alpha j(p)\in B^\times$: the local
map $A\to B$ reflects units, so $\alpha j(p)\in A^\times$, hence
$j(p)\in\alpha^{-1}(A^\times)=A^\times$ by the unit axiom of $M_{\mathrm{Zar}}$, and
$p=q(j(p))=0$, where $q:L\to P$ is the quotient map with $qj=\mathrm{id}$ from the splitting
lemma. So the face $(\alpha j)^{-1}(A^\times)$, and likewise its preimage of $B^\times$, is
$\{0\}$, and the chart pushouts over it are the products $P\oplus A^\times$ and $P\oplus
B^\times$. The unit-extension formula $L\oplus_{A^\times}B^\times\simeq M_{\bar x}$ with $L\simeq
P\oplus A^\times$ then identifies $P\oplus B^\times\to M_{\bar x}$, $(p,b)\mapsto j(p)b$, with an
isomorphism too. Thus the composite $j_{\mathrm{Et}}:P\to M_{\bar x}$ is a chart of that stalk,
and $j$ is a chart of the Zariski stalk. Uses: def-trf-fs-log-blowup,
lem-trf-zariski-log-stalk-unit-extension, lem-trf-fs-face-sharpening,
lem-trf-integral-monoid-free-sharpening-splitting.

2. Choose finitely many generators $p_1,\ldots,p_d$ of $P$. The finite-presentation lemma supplies
finitely many defining pairs of relations for these generators. Represent each germ $j(p_i)$ by a
section of $M_{\mathrm{Zar}}$ on a common Zariski neighborhood $U_0$ of $x$. Each relation holds
at $x$, so its two section representatives agree on a smaller neighborhood. Intersect these
finitely many neighborhoods. The resulting tuple satisfies every defining relation and hence
determines a homomorphism $h:P\to M_{\mathrm{Zar}}(U_0)$ with germ exactly $j$. This uses only the
definition of equality of germs after the cited finite-presentation result; empty generator or
relation lists require no shrinking. Uses: lem-trf-fg-commutative-monoid-finite-presentation.

3. On $U_0$ put $\beta=\alpha h$. Apply the Zariski prelog-logification comparison to the constant
monoid sheaf associated to $P$ and to $\beta$. Denote its associated Zariski log structure by
$N_Z$ and its associated etale log structure by $N$. The universal properties give compatible maps
$f_Z:N_Z\to M_{\mathrm{Zar}}|_{U_0}$ and $f:N\to M|_{U_0}$, induced by $h$ and fixing units. The
comparison identifies the etale extension of $f_Z$ with $f$. The etale associated-log stalk
formula identifies $f_{\bar x}$ with the isomorphism $P\oplus B^\times\to M_{\bar x}$ in step 1,
respecting the specified generators and structural map. Uses:
lem-trf-zariski-prelog-logification-comparison, lem-trf-associated-log-universal-stalks.

4. Apply fine-log stalk-chart spreading to the given map $j_{\mathrm{Et}}:P\to M_{\bar x}$. Its
pushout hypothesis was verified in step 1. It gives an affine pointed etale neighborhood $(W,\bar
w)\to(U_0,\bar x)$ and a chart $k:P\to M(W)$ whose germ is $j_{\mathrm{Et}}$. The homomorphism
obtained from $h$ on $W$ has the same germ. The equality clause of finite-monoid stalk-data
spreading gives a further affine pointed etale refinement on which these homomorphisms agree.
Replace $W$ by this refinement; restrictions of a chart are charts by associated-log restriction
compatibility. Thus the restriction of $f$ to $W$ is an isomorphism induced by exactly $h$, not by
an unrelated chart with the same abstract monoid. Uses: lem-trf-fine-log-stalk-chart-spreading,
lem-trf-finite-monoid-stalk-data-spreading, lem-trf-associated-log-universal-stalks.

5. Let $V$ be the image of this $W\to U_0$. It contains $x$ and is Zariski open by openness of
etale morphisms. The map $W\to V$ is a surjective etale covering. For any geometric point $\bar y$
of $V$, the geometric-point lifting lemma gives a lift to $W$. The restriction-stalk
identification in finite-monoid stalk-data spreading identifies the map $f_{\bar y}$ with the
stalk of $f|_W$, which is an isomorphism by step 4. The geometric-stalk criterion for etale
sheaves now makes $f|_V$ an isomorphism. In particular $N|_V$ is fs, using the charts of the
isomorphic $M|_V$. Uses: lem-weil-pbc-etale-morphism-open-map,
lem-weil-pbc-etale-cover-geometric-point-lift, lem-trf-finite-monoid-stalk-data-spreading,
lem-weil-pbc-sets-etale-iso-on-geometric-stalks, def-trf-fs-log-blowup.

6. Fix $y\in V$ and a geometric point $\bar y$ over it. Write $C=\mathcal O_{V,y}$, $D=\mathcal
O_{V,\bar y}$, $R_1=(N_Z)_y$, $R_2=(M_{\mathrm{Zar}})_y$ and $a=(f_Z)_y$. Apply Zariski-stalk unit
extension to both Zariski log structures, whose associated etale log structures are fs by step 5.
It says that $R_i$ are integral with units $C^\times$, and canonically identifies their
characteristic quotients with those of $R_i\oplus_{C^\times}D^\times$. These identifications
respect section maps and units. Since $f_{\bar y}$ is an isomorphism, the induced map $\overline
a:R_1/C^\times\to R_2/C^\times$ is bijective. Thus we have a bijection on characteristic monoids
for the actual Zariski map, not merely an abstract identification of them. Uses:
lem-trf-zariski-log-stalk-unit-extension.

7. The map $a$ in step 6 is bijective by cancellation. For $b\in R_2$, lift its characteristic
using $\overline a$ to a representative $r\in R_1$. Then $b=a(r)u$ for some $u\in C^\times$, so
$b=a(ru)$. If $a(r)=a(s)$, injectivity of $\overline a$ gives $r=su$ for a unit $u\in C^\times$.
Cancellation in the integral monoid $R_2$ yields $u=1$, since $a$ fixes units; hence $r=s$.
Therefore all Zariski stalk maps of $f_Z|_V$ are bijective. On any open, a target section has
local lifts by stalk surjectivity; injectivity of stalks makes any two local lifts equal after
shrinking at each point of an overlap. The sheaf uniqueness and gluing axioms give a unique global
lift. Thus $f_Z|_V$ is an isomorphism compatible with the structural maps. Uses: .

8. Choose an affine neighborhood $T$ of $x$ in $X$. In $T=\operatorname{Spec}R$, basic opens form
a basis: since $x\in V\cap T$, the complement is a closed set $V(I)$, and some $g\in I$ is outside
the prime of $x$. Then $U=D_T(g)=\operatorname{Spec}R_g$ contains $x$ and is contained in $V$.
Restrict $h$ to $U$. Restriction compatibility for logification preserves the isomorphisms
$N_Z|_U\simeq M_{\mathrm{Zar}}|_U$ and $N|_U\simeq M|_U$ from steps 5 and 7. Consequently $P$ is
the required fs chart on both sites and its structural map is exactly $\alpha h$. Uses:
def-pc-scheme, lem-trf-zariski-prelog-logification-comparison.
-/
theorem FineSaturatedLogScheme.exists_affine_zariski_fs_chart
    (X : FineSaturatedLogScheme.{u}) (Z : ZariskiLogStructure X.scheme)
    (e : Z.toZariskiPrelogStructure.EtaleMap X.logStructure) (he : e.IsAssociation)
    (x : X.scheme) :
    ∃ U : X.scheme.Opens, x ∈ U ∧ IsAffine U.toScheme ∧
      ∃ (P : Type u) (_ : CommMonoid P) (h : P →* Z.monoidSheaf.obj.obj (op U)),
        IsFineSaturatedMonoid P ∧ Z.IsChart U h ∧
          X.logStructure.IsChart (Scheme.Etale.mk U.ι) ((e.sectionMap U).comp h) := by
  sorry

end AlgebraicGeometry
