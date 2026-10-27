module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.SupportedPerfectApproximation
import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.AlgebraicGeometry.AffineSupportedPerfectApproximation
import WeilConjectures.AlgebraicGeometry.SupportedOpenPushforward
import WeilConjectures.Algebra.Homology.DerivedOpenShriekAdjunction
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkMaps
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.AffinePerfectSupportExtension
import WeilConjectures.AlgebraicGeometry.AffinePerfectMapLift
import WeilConjectures.AlgebraicGeometry.DerivedOpenGluing
import WeilConjectures.AlgebraicGeometry.PerfectThickClosure
import WeilConjectures.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Supported perfect approximation across an affine open

Source: Stacks Project, Derived Categories of Schemes, Tag 08ER, lemma-induction-step
(blueprint: lem-sfb-supported-perfect-approximation-open-step).

The approximation property is the shared definition from Tags 08EM and 08EN.
No quasi-separatedness assumption is imposed on the scheme or on the first open.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Uniform supported perfect approximation extends from a quasi-compact open `U` to
`Y = U ∪ V` when `V` is affine and `U ∩ V` is quasi-compact.
Source: Stacks Project, Derived Categories of Schemes, Tag 08ER, lemma-induction-step
(blueprint: lem-sfb-supported-perfect-approximation-open-step).

Proof (the corrected stage-1 argument, retaining the statement of Tag 08ER):
1. Fix a closed $T\subseteq Y$ with retrocompact complement. The complement of $T\cap U$ in $U$ is
   retrocompact: every affine open of $U$ is also an affine open of $Y$. Choose a witness $r_U$
   for $\mathsf A(U)$ at $T\cap U$, and enlarge it to be nonnegative. Enlarging a witness
   preserves its property: $a$-pseudo-coherence implies $b$-pseudo-coherence for $b\ge a$ by the
   same local approximation, and the support condition becomes stronger when its lower endpoint
   decreases. Put $T'=T\setminus U$, closed in $Y$ and contained in $V$. The correct complement
   formula is $V\setminus T'=(V\setminus T)\cup(U\cap V)$. Both opens on the right are quasi-
   compact, the first by retrocompactness and the second by hypothesis; their union is quasi-
   compact. Choose a finite affine cover of this complement with $s\ge0$ members. Set $r=r_U+s$, a
   number depending only on $Y,T$ and the fixed cover. Dependencies: def-sfb-supported-perfect-
   approximation-property, def-sfb-m-pseudo-coherent-complex, lem-pqf-finite-affine-cover-qc-open.
2. Fix $m$ and an admissible $E$: it is $(m-r)$-pseudo-coherent, lies in
   $D_{\mathrm{QCoh}}(\mathcal O_Y)$, and is supported on $T$ in degrees $\ge m-r$. On each open
   in its pseudo-coherence cover, cohomology vanishes above the maximum of $m-r$ and the upper
   bound of the strictly perfect approximation. Quasi-compactness of $U$ gives a finite subcover
   of $U$ and hence an integer $h$ with $H^i(E)|_U=0$ for $i>h$. Prove the approximation
   conclusion, simultaneously for all such $E$, by induction on $\max(0,h-(m-s)+1)$. This uses an
   upper bound, not a largest nonzero degree, so also covers $E|_U=0$. Exact restriction commutes
   with cohomology and preserves the local defining approximations. Dependencies: def-sfb-m-
   pseudo-coherent-complex, def-pc-perfect-complex, def-pc-derived-open-restriction-maps.
3. In the base case $h<m-s$, $H^i(E)|_U=0$ for $i\ge m-s$. Since $r\ge s$, the support condition
   outside $T$ also holds in these degrees. Thus $H^i(E)$ is supported on $T'$ for $i\ge m-s$. The
   restriction $E|_V$ is $m$-pseudo-coherent by monotonicity, because $r\ge0$. Apply the affine
   approximation theorem to $V,T',m,s$: its required support range $i\ge m-s+1$ follows from the
   stronger bound just obtained. This gives a perfect $B$ supported on $T'$ and $b:B\to E|_V$
   inducing isomorphisms above $m$ and a surjection at $m$. Dependencies: lem-sfb-affine-
   supported-perfect-approximation, def-sfb-m-pseudo-coherent-complex.
4. Let $j:V\hookrightarrow Y$. The supported-open pushforward theorem says that $Rj_*B$ is perfect
   and $j_!B\cong Rj_*B$. Let $P=j_!B$ and let $v:P\to E$ correspond to $b$ under the derived
   extension-by-zero adjunction. Exactness of extension by zero gives $H^i(P)=j_!H^i(B)$. Its
   stalks are those of $H^i(B)$ on $V$ and zero outside $V$, so $P$ is supported on $T'\subseteq
   T$. On $V$, the map $v$ is $b$ under the adjunction unit; this unit is an isomorphism, as
   follows from the inside-stalk unit formula (the restriction back to $V$ is the identity).
   Outside $V$, both $H^i(P)$ and $H^i(E)$ vanish for $i\ge m$, because $T'\subset V$ and $m\ge
   m-s$. Consequently $v$ has the required cohomology isomorphisms and surjection everywhere. The
   stalk criterion detects the isomorphisms; exact stalks identify the cokernel of the degree-$m$
   map as zero, hence that map is surjective. Dependencies: lem-pc-supported-open-pushforward,
   lem-sc-derived-open-shriek-derived-adjunction, lem-sc-derived-open-restriction-adjunction-
   exact, lem-sc-module-extension-by-zero-stalk-maps, lem-weil-pbc-module-stalk-exact, lem-weil-
   pbc-module-iso-on-stalks.
5. Suppose $h\ge m-s$. Then $h-r_U\ge m-r$, so $E|_U$ is $(h-r_U)$-pseudo-coherent and supported
   on $T\cap U$ in degrees $\ge h-r_U$. Apply $\mathsf A(U)$ at approximation degree $h$,
   obtaining $p:A\to E|_U$ with $A$ perfect supported on $T\cap U$, an isomorphism in degrees
   $>h$, and a surjection in degree $h$. In particular $H^i(A)=0$ for $i>h$. Put $W=U\cap V$. The
   affine supported extension theorem on $V$, with closed support $T\cap V$, supplies a perfect
   supported $Q$ and an isomorphism $c:Q|_W\cong(A\oplus A[1])|_W$. Its hypotheses hold because
   $W$ is quasi-compact and $V\setminus T$ is quasi-compact. Apply the affine perfect-map lifting
   theorem to the composite $Q|_W\xrightarrow{c}(A\oplus
   A[1])|_W\xrightarrow{\mathrm{pr}_1}A|_W\xrightarrow{p}E|_W$. Replace $Q$ by the supplied
   perfect $Q_1$, still supported on $T\cap V$, and replace $c$ by $c\circ\beta|_W$. The resulting
   map $b:Q_1\to E|_V$ satisfies $b|_W=p|_W\circ\mathrm{pr}_1\circ c$. Dependencies: def-sfb-
   supported-perfect-approximation-property, def-sfb-m-pseudo-coherent-complex, lem-sc-affine-
   perfect-support-extension, lem-sc-affine-perfect-map-lift.
6. Glue $A\oplus A[1]$ on $U$ and $Q_1$ on $V$ using $c^{-1}$ and the compatible maps
   $p\circ\mathrm{pr}_1,b$. The derived open gluing theorem gives $a:R\to E$ whose restriction to
   $U$ is $p\circ\mathrm{pr}_1$ and whose restriction to $V$ is $b$. Finite sums and shifts
   preserve perfectness, so the two restrictions are perfect. Their strictly perfect local covers
   together cover $Y$, proving $R$ perfect by definition. Their vanishing stalks prove support on
   $T$. On $U$, $H^i(R)=H^i(A)\oplus H^{i+1}(A)$, which vanishes for $i>h$, and $H^h(a)$ is
   surjective. Perfect objects are pseudo-coherent by the perfect-to-pseudo-coherent theorem, and
   pseudo-coherent scheme objects have quasi-coherent cohomology. In particular $R\in
   D_{\mathrm{QCoh}}(\mathcal O_Y)$. Dependencies: lem-sc-derived-open-gluing, lem-pc-perfect-
   thick-closure, def-pc-perfect-complex, lem-pc-perfect-pseudo-coherent-locally-finite-tor, lem-
   sc-pseudo-coherent-qcoh.
7. Complete $a$ to a distinguished triangle $R\to E\to E_1\to R[1]$. A perfect object is locally
   strictly perfect, so its local identity approximation makes $R$ $(m-r+1)$-pseudo-coherent.
   Apply part (1) of the ringed-site pseudo-coherence triangle theorem on the small Zariski ringed
   site, whose local strictly perfect definition is exactly the scheme definition: $E_1$ is
   $(m-r)$-pseudo-coherent. The quasi-coherent derived property is closed under shifts and
   triangle middle terms; apply it with support equal to $Y$ to the rotated triangle $E\to E_1\to
   R[1]$. Hence $E_1\in D_{\mathrm{QCoh}}$. The cohomology long exact sequence on $U$ gives
   $H^i(E_1)|_U=0$ for $i\ge h$, using the surjection at $h$ and the vanishing above $h$ of
   $R|_U,E|_U$. At a stalk outside $T$, all cohomology stalks of $R$ vanish, so the same sequence
   identifies $H^i(E_1)_y$ with $H^i(E)_y$. Thus $E_1$ satisfies the same support bound. The
   induction hypothesis at upper bound $h-1$ now gives an approximation $v_1:P_1\to E_1$ at degree
   $m$, with $P_1$ perfect supported on $T$. Dependencies: def-weil-triangulated-category, def-pc-
   perfect-complex, lem-sfb-ringed-site-m-pseudocoherent-triangle, lem-pc-supported-qcoh-
   triangulated, lem-sf-derived-homology-long-exact, lem-weil-pbc-module-stalk-exact.
8. Let $d:E_1\to R[1]$ be the connecting morphism. Complete $d\circ v_1$ and rotate to obtain a
   distinguished triangle $R\to P\to P_1\xrightarrow{d\circ v_1}R[1]$. Apply TR3 to the rotated
   triangles starting with $P_1\to R[1]$ and $E_1\to R[1]$, using $v_1$ and the identity of
   $R[1]$, and shift the third map back. This yields $v:P\to E$ and a morphism from the upper
   triangle to $R\to E\to E_1\to R[1]$ whose outer components are $1_R,v_1$. Two-out-of-three
   gives that $P$ is perfect. At a point outside $T$, the upper triangle's exact cohomology
   sequence has zero outer stalks in every degree, proving all stalks of $H^i(P)$ there are zero.
   Dependencies: def-weil-triangulated-category, lem-pc-perfect-thick-closure, lem-sf-derived-
   homology-long-exact, lem-weil-pbc-module-stalk-exact.
9. Check the comparison on stalks at any fixed point, using the long exact sequences of this
   triangle morphism. For $i\ge m$, map $z\in H^i(E)$ to $z_1\in H^i(E_1)$ and lift $z_1$ to
   $x_1\in H^i(P_1)$ through $H^i(v_1)$. Its boundary in $H^{i+1}(R)$ is zero by commutativity, so
   lift $x_1$ to $x\in H^i(P)$. The difference $z-H^i(v)x$ comes from $H^i(R)$; adjust $x$ by that
   class. This proves surjectivity. If $i>m$ and $H^i(v)x=0$, injectivity of $H^i(v_1)$ says $x$
   comes from $a\in H^i(R)$. Since $a$ maps to zero in $H^i(E)$, it is the boundary of some $b\in
   H^{i-1}(E_1)$. Surjectivity of $H^{i-1}(v_1)$, valid since $i-1\ge m$, lifts $b$ to
   $H^{i-1}(P_1)$. The upper exact sequence makes the image of $a$ in $H^i(P)$ zero, so $x=0$.
   Thus the stalk maps are bijective above $m$ and surjective at $m$. Stalk detection gives the
   sheaf isomorphisms; exact stalks show the degree-$m$ cokernel has all stalks zero, hence is
   zero. This proves that $v$ is an approximation and completes the induction. Since the fixed
   $r=r_U+s$ works for every $m,E$, $\mathsf A(Y)$ holds. Dependencies: lem-sf-derived-homology-
   long-exact, lem-weil-pbc-module-stalk-exact, lem-weil-pbc-module-iso-on-stalks, def-sfb-
   supported-perfect-approximation-property. -/
theorem hasSupportedPerfectApproximation_of_open_cover
    (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (U V : Y.Opens)
    [∀ W : U.toScheme.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [∀ W : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over W))]
    (hcover : U ⊔ V = ⊤) (hU : IsCompact (U : Set Y)) (hV : IsAffineOpen V)
    (hUV : IsCompact ((U ⊓ V : Y.Opens) : Set Y))
    (hA : HasSupportedPerfectApproximation.{u, w} U.toScheme) :
    HasSupportedPerfectApproximation.{u, w} Y := by
  sorry

end AlgebraicGeometry.Scheme
