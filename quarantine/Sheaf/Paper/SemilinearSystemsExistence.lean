/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearDerivedCalculus
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-! # Existence of the ordinary semilinear system calculus

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 079P, 06YS, 06YY,
07A4 and 08J7--08JB (blueprint: lem-coef-semilinear-system-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.SemilinearSections

variable {C₀ : Type c} [Category.{v} C₀] (J₀ : GrothendieckTopology C₀)
  [EssentiallySmall.{max c v r} C₀]
  (B₀ : ℕ → Sheaf J₀ CommRingCat.{max c v r})
  (τ₀ : ∀ n : ℕ, B₀ (n + 1) ⟶ B₀ n)

/-- The ordinary system calculus and its cartesian internal-Hom transition law.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 079P, 06YS, 06YY,
07A4 and 08J7--08JB (blueprint: lem-coef-semilinear-system-existence).
Proof: construct the ringed sequence site, its Grothendieck derived category,
component evaluations, K-flat tensor and K-injective Hom models. The transition
law is obtained by transposing the component evaluation map through the
cartesian reduction isomorphisms and the tensor-Hom adjunction; the tensor
associators give its cocycle. -/
structure SemilinearSystemData where
  systems : Data.{c, v, r} J₀ B₀ τ₀
  homTransition : systems.HomReductionFormula J₀ B₀ τ₀

/-- Ordinary semilinear system calculus and cartesian internal Hom.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 079P, 06YS, 06YY,
07A4 and 08J7--08JB (blueprint: lem-coef-semilinear-system-existence).
Proof:
1. Present the sequence topos by the small site $\mathcal C\times\mathbf N_{\geq1}$: an arrow
$(U,n)\to(W,m)$ consists of $U\to W$ and $n\leq m$, and generating covers have fixed index and are
covers of $\mathcal C$. Pulling back such a cover along an index-changing arrow still gives a
fixed-index cover, so this is a site. Its sheaf condition says exactly that each level is a sheaf;
the other restrictions give inverse-sequence transitions. The ring sheaf $(U,n)\mapsto B_n(U)$ is
therefore $B_\bullet$, and its module sheaves are exactly $\mathscr S(B)$. Kernels and cokernels
are computed at each level using kernels and sheafified cokernels of module sheaves; the
scalar-linear transitions descend to these constructions. Hence cohomology of a complex of systems
is componentwise.

2. Apply [lem-pur-ringed-site-grothendieck-abelian] and [prop-pur-kinjective-resolutions-exist] to
that small ringed site. This gives Grothendieck abelianness and unbounded K-injective resolutions
in $\mathscr S(B)$. Exact evaluation descends termwise by
[lem-weil-pbc-exact-functor-derived-factorization]. A morphism in the derived category is
invertible exactly when its cone is acyclic; its evaluated cones are the cones of its evaluations.
Componentwise cohomology therefore proves joint detection of isomorphisms. This uses only
localization of complexes of systems, not a category of diagrams in triangulated categories.

3. On underlying sequence topoi, evaluation $e_n$ is inverse image of a geometric morphism: its
right adjoint sends a sheaf $F$ to the sequence with value $F$ for $q\geq n$ and terminal sheaf
for $q<n$. The adjunction follows by extending the component at $n$ along the given transitions;
evaluation preserves finite limits. The structural ring map is $e_nB_\bullet=B_n$. Thus
[lem-weil-pbc-ringed-topos-kflat-pullback] says evaluation carries flat-term K-flat complexes on
the sequence site to flat-term K-flat complexes over $B_n$. Apply [lem-pc-kflat-resolution] on
that site and [lem-weil-pbc-site-derived-tensor-descent]: evaluating the resulting total tensor
complexes computes $e_n(M\otimes^L_{B_\bullet}N)=M_n\otimes^L_{B_n}N_n$. The comparisons on
morphisms are induced by actual tensor chain maps and inversion of quasi-isomorphisms.

4. For a $B_n$-module $F$, define $(E_nF)_q=F\otimes_{B_n}B_q$ for $q\leq n$ and zero for $q>n$,
with quotient-induced transitions. A map $h:F\to M_n$ extends uniquely to $E_nF\to M$: its
component at $q\leq n$ is $x\otimes a\mapsto a\,\tau_{nq}(h(x))$, and above $n$ the source is
zero. Balancing and the transition cocycle verify this formula; evaluating at $n$ recovers $h$.
This proves the natural adjunction $E_n\dashv e_n$ by the module tensor/restriction adjunction.
These formulas also commute with the Hom-complex differential $d(h)=d_Mh-(-1)^{|h|}hd_F$, giving
the adjunction on homotopy categories.

5. The additive functor $QE_n$ preserves shifts and cone matrices. Every complex over $B_n$ has a
flat-term K-flat resolution [lem-pc-kflat-resolution]. A quasi-isomorphism between such complexes
remains a quasi-isomorphism after each tensor $-\otimes_{B_n}B_q$ by
[lem-pur-derived-change-of-rings](1), and hence after $E_n$ by componentwise cohomology. The
resolving-class criterion [lem-pur-left-derived-from-kflat-class] gives an everywhere-defined
$L_n=LE_n$, computed by $E_nP$ on those representatives. By
[lem-weil-pbc-exact-functor-derived-functor], exact evaluation is its own everywhere-defined right
derived functor, so [lem-pc-derived-adjoint-functors] gives $L_n\dashv e_n$. In particular
$e_qL_nP=P\otimes^L_{B_n}B_q$ for $q\leq n$ and is zero otherwise. No coefficient-flatness
hypothesis entered this argument.

6. For $m\geq n$, put $T_{m,n}=-\otimes^L_{B_m}B_n$. There is a natural map
$\sigma_{mn}:L_nT_{m,n}\to L_m$: on a flat-term K-flat $P$ over $B_m$, its components are the
tensor rebracketing identity $P\otimes_{B_m}B_q$ for $q\leq n$ and the zero-source map for $q>n$.
K-flat pullback ensures the iterated tensors compute the displayed functors. Resolving-class
tensor descent makes this a transformation of functors on the derived categories. Both composites
for three indices have precisely the same components as chain maps on the same representative, so
they are equal after localization. The derived adjunction sends precomposition with $\sigma_{mn}$
to $h\mapsto t_{m,n}T_{m,n}(h)$: this is the tensor-adjoint formula $x\otimes a\mapsto
a\tau_{mn}h(x)$. It follows that the $t_{m,n}$ are natural and satisfy their cocycle.
Invertibility of adjacent reductions implies invertibility of all reductions by this cocycle and
preservation of isomorphisms by tensor; this proves the stated normalization criterion.

7. On any of the small ringed sites in use, define $H(M,N)$ by the K-injective construction
[def-pur-derived-internal-hom]; its independence is [lem-pur-rhom-well-defined]. The internal-Hom
identity of [lem-weil-pbc-ringed-internal-hom-exact-restriction] and the global-sections
identification of [lem-pur-rhom-global-sections] give $$\operatorname{Hom}(P,H(M,N))\cong
H^0R\Gamma H(P,H(M,N))\cong H^0R\Gamma H(P\otimes^LM,N)\cong\operatorname{Hom}(P\otimes^LM,N).$$
These bijections are natural. Hence they define the tensor-Hom adjunction and its evaluation on
the sequence site as well as on each level. This supplies the system internal Hom without trying
to assemble unrelated fiber objects.

8. Let $M$ be cartesian. There is a canonical system map $$L_n(P\otimes^L_{B_n}M_n)\cong
L_nP\otimes^L_{B_\bullet}L_nM_n\longrightarrow L_nP\otimes^L_{B_\bullet}M,$$ where the last arrow
uses the counit $L_ne_nM\to M$. For the first isomorphism take flat-term K-flat representatives
over $B_n$. Their $E_n$ extensions are K-flat with flat terms: below $n$ this is K-flat pullback,
above $n$ zero; componentwise exactness and tensor then test K-flatness of these particular
systems. The ordinary tensor rebracketing gives the isomorphism on these strict models and
descends by tensor descent. At $q\leq n$ the second arrow is $T_{n,q}P\otimes^L t^M_{n,q}$, which
is invertible by cartesianness, and above $n$ it is $0\to0$. Joint detection therefore makes the
displayed projection map an isomorphism of derived systems. This is a constructed map, not an
inference of equality from evaluations.

9. For every $P\in D(B_n)$, apply the adjunctions and the preceding projection isomorphism to
obtain
$$\operatorname{Hom}(P,e_nH_B(M,N))\cong\operatorname{Hom}(L_nP,H_B(M,N))\cong\operatorname{Hom}(L
_nP\otimes^LM,N)\cong\operatorname{Hom}(L_n(P\otimes^LM_n),N)\cong\operatorname{Hom}(P\otimes^LM_n
,N_n)\cong\operatorname{Hom}(P,H_{B_n}(M_n,N_n)).$$
Yoneda gives the claimed natural internal-Hom comparison. Its definition by these transposes
carries system evaluation to the fiber evaluation. Transpose the reduction transition of the
system evaluation map. Since $t^M_{m,n}$ is invertible, the resulting equation uniquely determines
the reduction of $H_B(M,N)$: it is exactly the transpose of the formula displayed in the
statement. The cocycle holds as an equation of system maps because evaluation and its adjunction
were constructed on the sequence site; alternatively its two transposes are the same
twice-reassociated evaluation followed by the transition of $N$, by the tensor associators. The
inverse cartesian comparison is essential here. -/
theorem semilinearSystemData : Nonempty (SemilinearSystemData.{c, v, r} J₀ B₀ τ₀) := by
  sorry

end WeilConjectures.SemilinearSections
