/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import WeilConjectures.AlgebraicGeometry.DenseCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace

/-! # Component dimension at a generic point in an etale chart

Source: Stacks Project, Decent Spaces, Tags 0A4J and 03K6; Algebra, Tag 00OT;
Varieties, Tag 0A21; Descent, Tag 04N4
(blueprint: lem-sfb-space-component-generic-chart-dimension).

The dimension at a point is the infimum of dimensions of open neighbourhoods, using
`topologicalKrullDimAt`. A component has its induced topology. Quasi-compactness of the
space, local finite type on etale scheme charts, and quasi-compactness of every scheme
test of the diagonal are stated separately. No scheme atlas is chosen in the statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Each component has a unique generic point and finite nonnegative dimension, equal to
the topological local dimension at every point of every etale scheme chart over that
generic point. The chart need not be surjective or quasi-compact.

Source: Stacks Project, Tags 0A4J, 03K6, 00OT, 0A21 and 04N4
(blueprint: lem-sfb-space-component-generic-chart-dimension).

Proof (the node's seven steps):
1. Choose an affine surjective etale atlas $p:W\to Y$ by [lem-sfb-qc-space-affine-etale-atlas].
   The finite-type hypothesis on charts makes $W$ locally of finite type over $k$. Since $W$ is
   affine it is quasi-compact by [lem-weil-pbc-affine-scheme-qcqs], hence finite type. Write
   $W=\operatorname{Spec}A$; [lem-pc-affine-finite-type-algebra] makes $A$ finitely generated over
   $k$, and [lem-wf-affine-noetherian-components] makes $|W|$ Noetherian. The map $|p|$ is
   continuous and surjective by [lem-a1-space-point-open-calculus]. Thus $|Y|$ is Noetherian: pull
   back any descending chain of closed subsets to $W$, let it stabilize there, and use
   surjectivity to infer stabilization of the original chain.
2. By [lem-sc-noetherian-finite-irreducible-components], write the finitely many components of
   $|Y|$ as $C=C_1,C_2,\ldots,C_r$. Sobriety from [lem-sfb-quasiseparated-space-sober] gives the
   unique point $\eta$ with closure $C$. It lies in no other component: if $\eta\in C_i$, then
   $C=\overline{\{\eta\}}\subseteq C_i$, so maximality forces $C_i=C$. Consequently
   $O=|Y|\setminus\bigcup_{i>1}C_i$ is an open neighbourhood of $\eta$ contained in $C$. All
   subsequent neighbourhoods will be taken inside this open.
3. Let $i:Z\hookrightarrow Y$ be the reduced closed subspace supported on $C$, supplied by [lem-
   sfb-space-reduced-closed-support]. Its pullback $T=Z\times_YW\to W$ is a closed immersion, with
   point image $p^{-1}(C)$, and $T\to Z$ is a surjective etale atlas by [lem-trf-space-fibre-
   products-etale-covers]. By the affine quotient characterization in [def-weil-closed-immersion],
   $T=\operatorname{Spec}(A/I)$ for an ideal $I$. The images of a finite set of $k$-algebra
   generators of $A$ generate $A/I$, so $T$ is finite type over $k$, and the chart criterion makes
   $Z$ locally of finite type. Also $|Z|=C$ is quasi-compact: it is closed in the quasi-compact
   space $|Y|$ (adjoin its open complement to a cover). Since $i$ is a monomorphism, its diagonal
   over $k$ is the base change of the diagonal of $Y$ along $Z\times_kZ\to Y\times_kY$. Quasi-
   compactness on scheme tests survives this base change by [lem-sfb-space-quasicompact-affine-
   tests]. Thus $Z$ is finite type and quasi-separated over $k$. The same diagonal argument proves
   that every open subspace of $Y$ is quasi-separated.
4. Fix $w\in W$ above $\eta$. Let $N$ be any open neighbourhood of $w$ in $W$ contained in
   $p^{-1}(O)$. By [lem-a1-space-etale-open-image], its image is an open subspace $J\subseteq Y$
   and $N\to J$ is surjective etale. The nonempty open $|J|\subseteq C$ is dense in the
   irreducible space $C$. Put $Z_J=Z\times_YJ$ and $T_J=T\times_ZZ_J$. The closed-support pullback
   clause of [lem-sfb-space-reduced-closed-support] identifies $|Z_J|$ homeomorphically with
   $|J|$. The inverse image $T_J$ is an open dense subset of $T$: every nonempty open $B\subseteq
   T$ has nonempty open image in $Z$ by [lem-a1-space-point-open-calculus], which meets the dense
   open $Z_J$, so $B\cap T_J\ne\varnothing$. Apply [lem-weil-pbc-dense-open-dimension-comparison]
   to the finite-type scheme $T$ and its dense open $T_J$ to obtain $\dim T=\dim T_J$. The maps
   $T\to Z$, $T_J\to Z_J$ and $N\to J$ are surjective etale atlases, the middle one by [lem-trf-
   space-fibre-products-etale-covers]. All three targets are quasi-separated by step 3. Thus [lem-
   sfb-quasiseparated-space-atlas-dimension] and [lem-weil-pbc-homeomorphism-krull-dimension] give
   $\dim N=\dim|J|=\dim|Z_J|=\dim T_J=\dim T=\dim|Z|=\dim C$. This is a sequence of direct
   applications and a one-line density check. It never asserts that $N\to Y$ factors through the
   reduced subspace $Z$.
5. The neighbourhoods $N$ just considered form a neighbourhood basis at $w$: intersect any
   neighbourhood with the open set $p^{-1}(O)$, which contains $w$. By [lem-weil-pbc-dimension-at-
   point-open-subspace], compute the local dimension inside this open subspace. Every open
   neighbourhood there has dimension $\dim C$ by step 4, so its infimum is $\dim C$ by [def-kun-
   topological-dimension-at-point]. Hence $\dim_wW=\dim C$ for every $w$ above $\eta$.
6. Now let $a:U\to Y$ and $u$ be as in the statement. The fibre product $V=U\times_YW$ is a
   scheme, and its projections to $U$ and $W$ are etale by representability and etale base change
   [def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers]. Surjectivity on pairs of
   field-valued point classes [lem-a1-space-point-open-calculus] supplies $v\in V$ mapping to $u$
   and to some $w\in W$ above $\eta$. Apply [lem-sfb-etale-topological-dimension-at-point] to both
   scheme projections. It gives $\dim_uU=\dim_vV=\dim_wW=\dim C$. Neither $U$ nor $a$ needs to be
   quasi-compact or surjective.
7. The atlas $T\to Z$ of step 3 and [lem-sfb-quasiseparated-space-atlas-dimension] identify $\dim
   C=\dim|Z|=\dim T$. The scheme $T$ is finite type over $k$, so [lem-kun-dimension-finite-type]
   makes this dimension finite. It is nonnegative since $C$ is nonempty and the atlas is
   surjective, so $T$ is nonempty and any point has a nonempty irreducible closure, a chain of
   length zero in the definition of Krull dimension [def-kun-topological-krull-dimension]. This
   proves the asserted membership in $\mathbf Z_{\geq0}$ as well as the equality. If $Y$ is empty,
   it has no irreducible components and the statement is vacuous.
-/
theorem component_generic_chart_dimension {k : Type u} [Field k]
    (Y : AlgebraicSpace (Spec (CommRingCat.of k)))
    (hqc : CompactSpace (Point Y.obj.obj))
    (hft : ∀ (U : Over (Spec (CommRingCat.of k))) (a : yoneda.obj U ⟶ Y.obj.obj),
      IsEtale a → LocallyOfFiniteType U.hom)
    (hdiag : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj)))
    (C : Set (Point Y.obj.obj)) (hC : C ∈ irreducibleComponents (Point Y.obj.obj)) :
    (∃! η : Point Y.obj.obj, closure ({η} : Set (Point Y.obj.obj)) = C) ∧
      (∃ n : ℕ, topologicalKrullDim C = (n : WithBot ℕ∞)) ∧
      ∀ (η : Point Y.obj.obj), closure ({η} : Set (Point Y.obj.obj)) = C →
        ∀ (U : Over (Spec (CommRingCat.of k))) (a : yoneda.obj U ⟶ Y.obj.obj),
          IsEtale a → ∀ (x : U.left), schemePointMap a x = η →
            topologicalKrullDimAt x = topologicalKrullDim C := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
