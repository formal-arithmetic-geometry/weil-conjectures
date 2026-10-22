/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Sheaf.Topology.WLocalComponents
import Sheaf.Topology.ProfiniteCohomologyVanishing
import Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit
import Sheaf.AlgebraicGeometry.FilteredColimitElementEventuallyZero
import WeilConjectures.Topology.ModuleMayerVietoris
import WeilConjectures.Topology.RestrictInjectiveResolution
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-! # Cohomological dimension of a spectral space

Source: Stacks Project, Cohomology of Sheaves, Tag 0A3G, part (1),
`proposition-cohomological-dimension-spectral`.
(blueprint: lem-sfb-spectral-space-cohomology-dimension)

The dimension is bounded above, rather than required to equal the bound. In particular,
the empty space is allowed, with Krull dimension minus infinity. No Noetherian assumption
is needed. Cohomology uses the recorded abelian-sheaf cohomology at the top open.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

/-- Abelian sheaf cohomology on a spectral space vanishes above any finite upper
bound on its topological Krull dimension, including for the empty space.

Source: Stacks Project, Cohomology of Sheaves, Tag 0A3G, part (1),
`proposition-cohomological-dimension-spectral`.
(blueprint: lem-sfb-spectral-space-cohomology-dimension)

Proof (simultaneous induction on vanishing and surjectivity in the top degree):
1. We may apply the cited ringed-space lemmas to abelian sheaves as follows. On any space $Y$ give
   every abelian sheaf its canonical module structure over the constant integer sheaf
   $\underline{\mathbf Z}_Y$ [def-weil-pbc-constant-sheaf, def-weil-sheaf-of-modules-category]: an
   integer acts by repeated addition, and a locally constant integer section acts by gluing these
   operations on opens where it is constant. Conversely any such module structure is forced by the
   action of $1$. Every additive sheaf map respects this action. Thus forgetting this structure
   and supplying it back are inverse on objects and maps, commute with sections and open
   restriction, and preserve injectivity because their lifting problems are identical. Computing
   the two cohomologies on the same injective resolution identifies the ringed-space cohomology
   [def-sc-ringed-space-module-cohomology] with the abelian-sheaf cohomology
   [def-sc-topological-abelian-cohomology], including the restriction maps. In the remaining
   steps, ringed-space citations always use this integer structure.
2. For the empty space all sheaf sections, hence all terms of a global-sections resolution, are
   zero. This proves the stated empty case in every degree. For nonempty spaces we prove
   simultaneously by induction on $n\geq0$: (A$_n$) for every spectral $X$ with $\dim X\leq n$ and
   every abelian sheaf $F$, $H^q(X,F)=0$ for $q>n$; and (B$_n$) for the same $X,F$ and every
   quasi-compact open $U\subseteq X$, restriction $H^n(X,F)\to H^n(U,F|_U)$ is surjective. Both
   assertions are also retained for the empty space. This is an induction on an upper bound, so it
   applies directly to the given $d$; there is no assumption that $\dim X=d$.
3. For $n=0$ and $X$ nonempty, there are no nontrivial specializations. Indeed, if $x$ specializes
   to $y\ne x$, the irreducible closed sets $\overline{\{y\}}\subsetneq\overline{\{x\}}$ give a
   chain of length one, contradicting $\dim X\leq0$; strictness follows from sobriety, hence the
   $T_0$ property. Thus $\overline{\{x\}}=\{x\}$ for every $x$: the set $X^c$ of closed points is
   all of $X$, in particular closed, and its subspace topology is that of $X$. Clause 1 of
   [det-pe-wlocal-components], applied with $T=X$, says that $X^c=X$ is profinite: compact,
   Hausdorff and totally disconnected. Then [lem-cbc-profinite-topological-cohomology-vanishing]
   gives (A$_0$). Every quasi-compact open $U$ is a compact subset of the Hausdorff space $X$,
   hence closed, so $U$ is clopen. A section of $F$ on $U$ extends by the zero section on
   $X\setminus U$, using the sheaf gluing axiom for the disjoint open covering
   $X=U\sqcup(X\setminus U)$. This proves (B$_0$).
4. Let $n\geq1$, assume (A$_{n-1}$) and (B$_{n-1}$) for all spectral spaces of dimension at most
   $n-1$, and fix $X,F$ with $\dim X\leq n$. To prove (B$_n$), let $U\subseteq X$ be quasi-compact
   open and $\xi\in H^n(U,F|_U)$. Set $Z=X\setminus U$, $W=\{x:\overline{\{x\}}\cap
   Z\ne\varnothing\}$ and $S=W\setminus Z$. The hypotheses of
   [lem-sfb-punctured-spectral-neighborhood-dimension] hold: $Z$ is closed and its open complement
   is exactly the quasi-compact $U$. Thus $S$ is spectral of dimension at most $n-1$. Applying
   (A$_{n-1}$) to $F|_S$ in degree $n$ yields $H^n(S,F|_S)=0$. The case $S=\varnothing$ uses the
   empty case already proved.
5. Apply [lem-weil-pbc-punctured-neighborhood-cohomology-colimit] to this closed $Z$ and its
   quasi-compact open complement. Its indexing category consists of the quasi-compact open
   neighborhoods $N$ of $Z$, with reverse inclusion; it is small (a set of subsets of $X$),
   nonempty (contains $X$), and directed (intersections are quasi-compact). The class $\xi$ is at
   the stage $N=X$, since $X\setminus Z=U$. Its image in the colimit is zero by the preceding step
   and the comparison isomorphism to $H^n(S,F|_S)$. The filtered-colimit zero criterion
   [lem-sc-filtered-colimit-map-zero] gives a quasi-compact open neighborhood $V$ of $Z$ at which
   this class vanishes: $\xi|_{V\setminus Z}=0$. Here $V\setminus Z=V\cap U$.
6. Since $Z\subseteq V$, the opens $U,V$ cover $X$. The pair $(\xi,0)\in H^n(U,F|_U)\oplus
   H^n(V,F|_V)$ restricts to zero under the difference map to $H^n(U\cap V,F|_{U\cap V})$, by the
   preceding step. The exact Mayer–Vietoris sequence [lem-sc-mayer-vietoris-ringed-space], applied
   with the integer coefficients of step 1, therefore supplies $\widetilde\xi\in H^n(X,F)$
   restricting to $(\xi,0)$. In particular it restricts to $\xi$ on $U$. This proves (B$_n$)
   before it is used to prove (A$_n$).
7. Choose an injective resolution $0\to F\to I^0\to I^1\to\cdots$ in abelian sheaves, using
   [lem-weil-pbc-site-sheaves-enough-injectives] on the site of opens and the resolution
   definition [def-sp-injective-resolutions], and set $G=\ker(I^n\to
   I^{n+1})=\operatorname{im}(I^{n-1}\to I^n)$. The latter equality uses exactness of the
   resolution and $n\geq1$. Kernels of sheaves are computed on sections, so for every open
   $A\subseteq X$ the degree-$n$ cycles are $G(A)$. Restricting the injective resolution to $A$
   remains an injective resolution by [lem-sc-ringed-space-restrict-injective-resolution] and step
   1. Consequently the definition of degree-$n$ cohomology gives the exact row $I^{n-1}(A)\to
   G(A)\to H^n(A,F|_A)\to0$. These rows for $A=X,U$ form a commuting restriction diagram, because
   all their maps are induced by the same differential and restriction maps.
8. For a quasi-compact open $U\subseteq X$ and $g\in G(U)$, let $c$ be its image in $H^n(U,F|_U)$.
   By (B$_n$), lift $c$ to $\widetilde c\in H^n(X,F)$ and then, by exactness of the top row, to
   $h\in G(X)$. The difference $g-h|_U$ maps to zero in $H^n(U,F|_U)$, hence equals the
   differential of some $b\in I^{n-1}(U)$. The injective-sheaf restriction theorem
   [lem-weil-pbc-injective-sheaf-mono-restriction], on the small site of opens of $X$, lifts $b$
   to $\widetilde b\in I^{n-1}(X)$; the inclusion $U\hookrightarrow X$ is a monomorphism. Then
   $h+d\widetilde b$ restricts to $g$. Thus $G(X)\to G(U)$ is surjective for every quasi-compact
   open $U$. If $U\subseteq V$ are both quasi-compact open, this also makes $G(V)\to G(U)$
   surjective: first lift to $X$, then restrict to $V$.
9. The quasi-compact opens of $X$ form a basis stable under binary intersections by spectrality.
   The surjectivities just proved therefore satisfy every hypothesis of
   [lem-sfb-quasi-compact-restriction-acyclicity], so $G$ is acyclic for global sections (take
   $V=X$, which is quasi-compact). The exact augmented complex $0\to F\to I^0\to\cdots\to
   I^{n-1}\to G\to0$ is a resolution in degrees $0,\ldots,n$; its earlier terms are injective and
   hence acyclic by part 1 of [lemma-weil-pbc-leray-acyclicity]. Apply part 2 of that lemma to
   global sections on abelian sheaves, whose source category has enough injectives by
   [lem-weil-pbc-site-sheaves-enough-injectives]; the target abelian groups have enough injectives
   by [lem-weil-pbc-ring-modules-enough-injectives] with $R=\mathbf Z$, since the integer action
   is uniquely determined by the additive group. It identifies $H^q(X,F)$ with the degree-$q$
   cohomology of $I^0(X)\to\cdots\to I^{n-1}(X)\to G(X)$. This complex has zero terms above degree
   $n$, hence zero cohomology there. This proves (A$_n$), closes the simultaneous induction, and
   taking $n=d$ proves the item.
-/
theorem subsingleton_H'_top_of_spectralSpace_of_dimension_le
    (T : Type u) [TopologicalSpace T] [SpectralSpace T]
    (d : ℕ) (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (q : ℕ) (hq : d < q) :
    Subsingleton
      (@CategoryTheory.Sheaf.H'.{u, u, u}
        (Opens T) inferInstance (Opens.grothendieckTopology T) inferInstance
        (@hasExt_of_enoughInjectives _ _ _ inferInstance
          (@IsGrothendieckAbelian.enoughInjectives _ _ _
            (CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
              (Opens.grothendieckTopology T) AddCommGrpCat.{u}))) F q ⊤) := by
  sorry

end TopCat.Sheaf
