module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.SpaceSupportedPerfectApproximation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.PerfectThickClosure
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AffineSupportedPerfectApproximation
import Sheaf.AlgebraicGeometry.ElementaryEtaleShriekExact
import WeilConjectures.AlgebraicGeometry.AffinePerfectSupportExtension
import WeilConjectures.AlgebraicGeometry.AffinePerfectMapLift
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Supported perfect approximation across a distinguished square

Source: Stacks Project, Derived Categories of Spaces, Tag 08HN (lemma-induction-step)
(blueprint: lem-sfb-space-supported-approximation-square-step).

The open subspace is presented by an algebraic space `U` and its presheaf isomorphism `e`.
The closed complement uses the existing reduced closed-subspace interface. The affine
chart is an actual scheme over the base, and the distinguished condition is imposed on
its canonical sheaf pullback projection. Absolute quasi-separatedness uses the existing
affine-test definition, with no separation hypothesis on the base scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The uniform supported perfect approximation property passes from the quasi-compact
open member of an elementary distinguished square to its qcqs ambient space.
Source: Stacks Project, Tag 08HN (lemma-induction-step)
(blueprint: lem-sfb-space-supported-approximation-square-step).

Proof (the corrected twelve-step argument recorded in the DAG):
1. Use $D_{\mathrm{QCoh}}$, perfectness, support, and $b$-pseudo-coherence in the sense of the
   defining node. Etale restrictions are exact slice restrictions and preserve
   $D_{\mathrm{QCoh}}$. For a scheme chart $Y$, the exact faithful functor $\epsilon_Y^*$
   identifies the Zariski and small-etale quasi-coherent derived categories, commutes with
   restriction to opens, and preserves and reflects $b$-pseudo-coherence and perfectness.
   Consequently support and the required cohomology isomorphisms and epimorphisms also transfer:
   on every open in the complement use exactness and faithfulness to preserve and detect zero
   kernels, cokernels and cohomology. These comparisons will be used on the schemes $V$ and
   $O=U\times_WV$; no representability of $U$ is asserted.
2. Here are the closure verifications used below. A perfect object has quasi-coherent cohomology:
   on its strictly perfect local models, terms are images of idempotents of finite free modules,
   hence quasi-coherent; kernel, image and cokernel closure then gives quasi-coherent cohomology,
   and the etale chart criterion descends it. If two objects of a triangle have quasi-coherent
   cohomology, its long exact sequence expresses the third cohomology as an extension of a kernel
   by a cokernel, so extension closure keeps it quasi-coherent. Perfect objects are closed under
   shifts, finite sums and triangles: restrict to scheme charts, use step 1 to pass to Zariski,
   apply the scheme thick-closure theorem, then detect perfectness back on the charts. Finally a
   perfect object is $b$-pseudo-coherent for every $b$, since the local identity map from a
   strictly perfect model is an approximation in every degree.
3. Fix a closed $T\subseteq|W|$ with $W\setminus T\to W$ quasi-compact. Its base change to $U$ is
   quasi-compact, so choose a witness $r_U$ for $\mathsf A(U)$ and $T\cap|U|$. Enlarge it to be
   nonnegative: a $b$-pseudo-coherent approximation also works at any degree $c\ge b$, and the
   support condition in degrees $\ge b$ implies that in degrees $\ge c$. Put $T'=T\setminus|U|$.
   This is closed in $W$, is contained in the reduced complement $Z$, and $V\times_WT'\to T'$ is
   an isomorphism after giving $T'$ its reduced closed subspace structure. Put $C=V\setminus
   j^{-1}(T')$. The correct equality is $C=(V\setminus j^{-1}T)\cup O$. The first open is quasi-
   compact by the given definition of the quasi-compact immersion $W\setminus T\to W$, evaluated
   on the affine chart $V$; the second is quasi-compact by hypothesis. Thus $C$ has a finite
   affine open cover, of size $s\ge0$. Set $r=r_U+s$. All these choices depend on $W,T,U,V$, not
   on $m,E$.
4. Fix $m$ and $E\in D_{\mathrm{QCoh}}(\mathcal O_W)$ satisfying the hypotheses for this $r$, and
   put $b=m-r$. There is an integer upper bound $h$ with $H^i(E)|_U=0$ for $i>h$. Indeed, each
   local strictly perfect approximation at degree $b$ gives such a bound on its domain; the etale
   images of these domains are open and cover $|U|$, so quasi-compactness gives finitely many
   bounds, whose maximum together with $b$ works. If $U$ is empty the assertion is vacuous. Prove
   the desired approximation for every such $E$ by induction on $\max(0,h-(m-s)+1)$. The base is
   $h<m-s$; in the step $h\ge m-s$, the new object will have upper bound $h-1$. This formulation
   also includes $E|_U=0$, for which one may choose $h=m-s-1$.
5. Suppose $h<m-s$. Then $H^i(E)|_U=0$ for $i\ge m-s$, and since $b\le m-s$, the high cohomology
   is supported on $T'$ in this range. On the affine scheme $V$, step 1 writes
   $E|_V\cong\epsilon_V^*E_0$, with $E_0\in D_{\mathrm{QCoh}}(\mathcal O_{V,\mathrm{Zar}})$,
   $m$-pseudo-coherent by monotonicity from $b\le m$, and supported on $j^{-1}T'$ for $i\ge m-s$.
   The complement of that support has the $s$-affine cover of step 3. The affine approximation
   theorem therefore applies (it only requires support for $i\ge m-s+1$) and gives $B_0\to E_0$.
   Pulling back gives a perfect $B$ supported on $j^{-1}T'$ and $\beta:B\to E|_V$ with
   isomorphisms above $m$ and an epimorphism in degree $m$.
6. Since $B|_O=0$, supported etale excision identifies $P=j_!B$ with $Rj_*B$, with $P|_V\cong B$
   and $P|_U=0$. These restrictions form a cover of $W$: $U$ covers its open and $j$ is an
   isomorphism over its complement. Thus the local strictly perfect models show $P$ is perfect.
   The adjunction in the excision node turns $\beta$ into $v:P\to E$, whose restriction to $V$ is
   $\beta$ under the unit isomorphism. Exactness of $j_!$ and the sum-of-lifts stalk formula show
   $H^i(P)$ is supported on $T'$, hence on $T$. On $U$, both $P$ and $H^i(E)$ for $i\ge m$ vanish,
   because $s\ge0$ and $h<m-s$. On $V$, the cohomology maps are those of $\beta$. Consequently $v$
   has the desired isomorphisms and epimorphism: geometric stalks preserve finite limits and
   colimits and detect mono-, epi- and isomorphisms. This completes the base case, including
   $s=0$.
7. Now suppose $h\ge m-s$. Then $h-r_U\ge m-s-r_U=b$. Restriction of the local approximations to
   the slice defining $U$, followed by monotonicity, makes $E|_U$ $(h-r_U)$-pseudo-coherent and
   supported on $T\cap|U|$ in degrees $\ge h-r_U$. Apply $\mathsf A(U)$ at degree $h$, obtaining
   $p:A\to E|_U$, with $A$ perfect supported on $T\cap|U|$, isomorphisms above $h$, and an
   epimorphism at $h$. In particular $H^i(A)=0$ for $i>h$. We use approximation at $h$, not at the
   fixed output degree $m$.
8. The overlap $O\subset V$ is a quasi-compact open scheme. Also $V\setminus j^{-1}T$ is quasi-
   compact by the defining test on the affine chart $V$. Transfer $A|_O$ to the Zariski quasi-
   coherent derived category via step 1 (perfect objects are quasi-coherent by step 2). Apply
   supported affine stabilization to obtain a perfect $Q$ on $V$, supported on $j^{-1}T$, with
   $c:Q|_O\xrightarrow{\sim}(A\oplus A[1])|_O$. Apply affine perfect-map lifting to
   $p|_O\circ\mathrm{pr}_1\circ c:Q|_O\to E|_O$, after the same comparison. Replace $Q$ by the
   supplied perfect $Q_1$, with $\beta_1:Q_1\to Q$ an isomorphism on $O$ and $\gamma:Q_1\to E|_V$
   satisfying $\gamma|_O=p|_O\circ\mathrm{pr}_1\circ c\circ\beta_1|_O$. The node explicitly
   preserves support, since $Q_1=Q\otimes^{\mathbf L}I$. Transfer back to the small-etale site;
   exact faithful comparison and its restriction isomorphism preserve this equation and every
   support and perfectness condition.
9. Use derived distinguished-square gluing with $A\oplus A[1]$ on $U$, $Q_1$ on $V$, the overlap
   isomorphism $(c\circ\beta_1|_O)^{-1}$ and compatible maps $p\circ\mathrm{pr}_1,\gamma$. It
   gives $a:R\to E$ with these restrictions. Perfectness and support on $T$ hold on this etale
   cover, hence globally by the local definition and stalk detection. Step 2 puts $R$ in
   $D_{\mathrm{QCoh}}$. On $U$, $H^i(R)=H^i(A)\oplus H^{i+1}(A)$ vanishes for $i>h$, and $H^h(a)$
   is surjective. All shifts here use $H^i(A[1])=H^{i+1}(A)$, as in the specified derived
   category.
10. Complete $a$ to a triangle $R\to E\to E_1\to R[1]$. The perfect object $R$ is $(b+1)$-pseudo-
   coherent by its local identity approximations. Part (1) of the ringed-site triangle theorem
   therefore makes $E_1$ $b$-pseudo-coherent. Step 2 gives $E_1\in D_{\mathrm{QCoh}}$. The exact
   cohomology sequence on $U$ gives $H^i(E_1)|_U=0$ for $i\ge h$: use the epimorphism in degree
   $h$ and vanishing of $R|_U,E|_U$ above $h$. Outside $T$, every cohomology of $R$ is zero, so
   this sequence identifies $H^i(E_1)$ there with $H^i(E)$; the same support bound in degrees $\ge
   b$ persists. Thus the induction hypothesis applies with upper bound $h-1$, yielding $v_1:P_1\to
   E_1$ with $P_1$ perfect supported on $T$, isomorphisms above $m$ and an epimorphism at $m$. The
   nonnegative induction parameter strictly decreased.
11. Let $d:E_1\to R[1]$ be the boundary. Complete $d\circ v_1$ and rotate to get a triangle $R\to
   P\to P_1\xrightarrow{d\circ v_1}R[1]$. Apply TR3 to its rotation starting with $P_1\to R[1]$
   and the corresponding rotation starting with $E_1\to R[1]$, with maps $v_1$ and $1_{R[1]}$.
   Shift back to obtain $v:P\to E$ and a morphism of the displayed triangles, with components
   $1_R,v,v_1,1_{R[1]}$. Step 2 gives perfectness of $P$. Restricting the upper triangle outside
   $T$, its outer terms have zero cohomology; exactness then gives zero cohomology of $P$ there.
   Thus $P$ is supported on $T$.
12. Here is the endpoint diagram chase on a geometric stalk. For $i\ge m$, send $z\in H^i(E)$ to
   $z_1\in H^i(E_1)$ and lift $z_1$ through the surjection $H^i(v_1)$ to $x_1\in H^i(P_1)$. Its
   boundary in $H^{i+1}(R)$ is zero by the commuting diagram, so it lifts to $x\in H^i(P)$. The
   difference $z-H^i(v)x$ comes from $H^i(R)$; adjusting $x$ by that class proves surjectivity.
   For $i>m$, if $H^i(v)x=0$, injectivity of $H^i(v_1)$ says $x$ comes from $a\in H^i(R)$. This
   $a$ maps to zero in $H^i(E)$, so it is the boundary of $b_1\in H^{i-1}(E_1)$. Since $i-1\ge m$,
   lift $b_1$ through $H^{i-1}(v_1)$; exactness of the upper row then gives $x=0$. Geometric
   stalks preserve finite limits and colimits, so these are exact stalk sequences, and they detect
   the sheaf isomorphisms above $m$ and the epimorphism at $m$. Hence $v$ is the required
   approximation. The fixed $r=r_U+s$ works for all $m,E$, proving $\mathsf A(W)$.
-/
theorem hasSupportedPerfectApproximation_of_distinguishedSquare
    {S : Scheme.{u}} (W U : AlgebraicSpace S)
    [HasDerivedCategory.{w} W.SmallModules] [HasDerivedCategory.{w} U.SmallModules]
    (hWqc : CompactSpace (Point W.obj.obj)) (hWqs : IsAbsolutelyQuasiSeparated W)
    (A : OpenSubspace W) (e : U.obj.obj ≅ A.val.toFunctor)
    (hUqc : CompactSpace (Point U.obj.obj))
    (V : Over S) (hV : IsAffine V.left) (j : yoneda.obj V ⟶ W.obj.obj)
    (hj : IsEtale j) (C : ClosedSubspace W)
    (hCred : IsReduced (C.val : AlgebraicSpace S))
    (hC : pointImage C.val.arrow.hom.hom = (pointImage A.val.ι)ᶜ)
    (hZ : IsIso (Limits.pullback.snd j C.val.arrow.hom.hom))
    (hUV : IsCompact (schemePointMap j ⁻¹' pointImage A.val.ι))
    (hU : HasSupportedPerfectApproximation U) :
    HasSupportedPerfectApproximation W := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
