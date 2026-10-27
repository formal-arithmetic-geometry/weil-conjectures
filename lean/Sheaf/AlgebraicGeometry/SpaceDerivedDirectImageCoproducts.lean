/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import Sheaf.AlgebraicGeometry.AlgebraicSpaceHigherDirectImageQuasiCoherent
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.BoundedBelowCoproductFiltration
import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension

/-! # Quasi-coherent derived direct image and ambient coproducts

Source: Stacks Project, spaces-perfect.tex, Tags 08FA(1), 08FB and 08F3
(blueprint: lem-sfb-space-derived-pushforward-coproducts).

The derived functor is the canonical K-injective direct image on the equivalent small
ringed models. Coproducts are taken in the ambient derived categories. The comparison
is fixed by its composites with every coprojection, including for the empty family.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Quasi-compact quasi-separated direct image preserves quasi-coherent cohomology
and its canonical ambient coproduct comparison is invertible.
Source: Stacks Project, spaces-perfect.tex, Tag 08FA(1),
lemma-quasi-coherence-direct-image; Tag 08FB, lemma-quasi-coherence-pushforward-direct-sums;
Tag 08F3, lemma-quasi-coherence-direct-sums
(blueprint: lem-sfb-space-derived-pushforward-coproducts).

The comparison `sigmaComparison` is the unique map whose composite with the i-th
coprojection is `Rf_*` of the i-th coprojection. The small ringed model retains the
original coefficient universe; `w` is the localization morphism universe. No absolute
quasi-compactness or quasi-separatedness is assumed of X or Y.

Proof:
1. Use the small site skeletons fixed by the size convention. The module categories on the small
   etale sites are Grothendieck abelian. Their ambient derived coproducts are represented by
   termwise sums. Exactness of sums implies $H^q(\bigoplus_iE_i)=\bigoplus_iH^q(E_i)$ and that
   good truncations commute with these sums: compute their kernels and cokernels termwise.
   Quasi-coherent modules are closed under sums, kernels and cokernels. Consequently the ambient
   sum of the $E_i$ has quasi-coherent cohomology, as do their good truncations.
   Uses: lem-pur-ringed-site-grothendieck-abelian, lem-kun-grothendieck-derived-coproducts, src-
   weil-derived-homology-preserves-coproducts, lem-sfb-space-qcoh-kernels-colimits, def-sbc-
   standard-tstructure-derived-category, def-weil-size-convention.
2. Restrict to affine etale scheme charts $a:V\to Y$, putting $X_V=X\times_YV$ and $g:X_V\to V$.
   The chart calculus identifies $a^*Rf_*K$ with $Rg_*(K|_{X_V})$, and quasi-coherent cohomology
   is detected on these charts. Restriction to a slice commutes with sums: the sheafified
   termwise sum restricts to the sheafified sum on that slice, since its coverings are exactly
   the coverings over the slice object. It is exact, so it also commutes with good truncations
   and cohomology. These identifications take each coprojection to its restricted coprojection,
   hence identify the restricted canonical comparison with the comparison for $g$. The
   hypotheses on $g$ follow directly from the scheme-test definitions: every affine test over
   $V$ is one over $Y$, and the diagonal is a base change of the diagonal of $f$. We may thus
   prove both claims with $Y$ affine. Isomorphisms of sheaves are detected on a covering by the
   sheaf gluing axiom.
   Uses: lem-sfb-space-derived-etale-chart-calculus, def-trf-space-etale-module-functors.
3. The canonical module direct image is left exact: its adjunction identifies maps into the
   image of a kernel with maps into that kernel, so it preserves kernels and the zero object; it
   is additive by its module-valued limit formula. For bounded below $K$ with quasi-coherent
   cohomology, apply the truncation spectral sequence $E_2^{p,q}=R^pf_*H^q(K)\Rightarrow
   H^{p+q}(Rf_*K)$. Its $E_2$ terms are quasi-coherent by the higher-image theorem. Every next
   page is a kernel modulo an image of maps between such modules, so remains quasi-coherent. In
   each fixed total degree, the spectral sequence stabilizes and the abutment has a finite
   filtration. Each graded piece is therefore quasi-coherent; induction through that finite
   filtration, starting at zero and using extension closure, proves that every $H^r(Rf_*K)$ is
   quasi-coherent.
   Uses: thm-sp-truncation-e2, lem-sfb-space-higher-direct-image-quasi-coherent, lem-sfb-space-
   qcoh-kernels-colimits, lem-sfb-space-qcoh-extension-closed, lem-pur-ringed-site-grothendieck-
   abelian, def-trf-space-etale-module-functors.
4. On this affine target choose one $N\geq1$ from the uniform upper-bound lemma. Fix
   $r\in\mathbf Z$ and put $l=r-N$. For $A=\tau_{\leq l-1}K$ the bound gives $H^m(Rf_*A)=0$ for
   $m\geq l-1+N=r-1$, in particular for $m=r,r+1$. Apply $Rf_*$ to the truncation triangle $A\to
   K\to\tau_{\geq l}K\to A[1]$. Its long exact cohomology sequence gives the natural isomorphism
   $H^r(Rf_*K)\cong H^r(Rf_*\tau_{\geq l}K)$. The right side is quasi-coherent by the bounded
   below case. This proves preservation for arbitrary $K$; the chart reduction then proves it on
   the original target.
   Uses: lem-sfb-space-derived-pushforward-upper-bound, def-sbc-standard-tstructure-derived-
   category, lem-pc-right-derived-functor-triangulated, lem-sf-derived-homology-long-exact.
5. For every $p\geq0$, $R^pf_*$ preserves arbitrary sums of module sheaves. Indeed, the sum is
   the filtered colimit of its finite subsums, indexed by finite subsets of the indexing set
   (including the empty subset). The filtered-colimit lemma identifies its higher image with the
   colimit of the higher images of those finite subsums. Additivity of $R^pf_*$ identifies the
   latter with the finite subsums of $\bigoplus_iR^pf_*M_i$: applying the additive derived
   functor and then cohomology preserves finite biproducts. All identifications agree with the
   injections, so the resulting isomorphism is the canonical comparison.
   Uses: lem-sfb-space-higher-module-image-filtered-colimits, lem-pc-right-derived-functor-
   triangulated, lem-weil-pbc-module-sheaves-colimits-forgetful.
6. For a family $K_i$ of objects with quasi-coherent cohomology and a common lower cohomological
   bound $a$, put $K=\bigoplus_iK_i$ with its coprojections $u_i:K_i\to K$; by step 1,
   $H^q(K)=0$ for $q<a$. The module categories are Grothendieck abelian and $f_*$ is left exact
   and additive (step 3). By part 2 of the truncation spectral-sequence theorem applied to
   $M[0]$, $H^p(Rf_*(M[0]))\cong R^pf_*M$ naturally in the module $M$. Fix $p\geq0$ and
   $r\in\mathbf Z$. Under these identifications the canonical map
   $\bigoplus_iH^p(Rf_*(H^r(K_i)[0]))\to H^p(Rf_*(H^r(K)[0]))$ induced by the $H^r(u_i)$ is the
   composite of $\bigoplus_iR^pf_*H^r(K_i)\to R^pf_*(\bigoplus_iH^r(K_i))$, an isomorphism by
   step 5, with $R^pf_*$ of the canonical map $\bigoplus_iH^r(K_i)\to H^r(K)$, an isomorphism
   because $H^r$ preserves coproducts. So every hypothesis of the bounded-below coproduct
   filtration lemma holds for $F=f_*$, the maps $u_i$ and the bound $a$. For each degree $q$ it
   gives finite filtrations of $\bigoplus_iH^q(Rf_*K_i)$ and $H^q(Rf_*K)$ and a filtered
   morphism between them whose underlying map is the canonical comparison $\sum_iH^q(Rf_*u_i)$,
   with every graded map an isomorphism. The finite-filtration induction lemma shows that this
   comparison is an isomorphism, in every degree $q$, including $q<a$ and the empty family.
   Uses: lem-pc-bounded-below-coproduct-filtration, lem-sp-finite-filtration-induction, thm-sp-
   truncation-e2, lem-pur-ringed-site-grothendieck-abelian, src-weil-derived-homology-preserves-
   coproducts.
7. For the original unbounded family and a fixed degree $r$, take the single cutoff $l=r-N$ from
   step 4, with $N$ independent of the family. That step gives natural degree-$r$ isomorphisms
   for every $E_i$ and for $E=\bigoplus_iE_i$. Since $\tau_{\geq l}E=\bigoplus_i\tau_{\geq
   l}E_i$, step 6 gives the degree-$r$ comparison for the truncated family. Naturality with
   respect to each injection makes the square of truncated and untruncated degree-$r$
   comparisons commute. Its two vertical arrows and bottom arrow are isomorphisms; hence so is
   its top arrow. By cohomology of ambient sums this top arrow is $H^r$ of the requested
   comparison. This holds for every $r$. A derived morphism inducing isomorphisms in all degrees
   is invertible: represent it by a roof with left arrow a quasi-isomorphism; the right arrow is
   then a quasi-isomorphism too, and both arrows are inverted by localization. This also covers
   the empty family. Finally restrict to the affine charts of step 2 to conclude globally.
   Uses: src-weil-derived-homology-preserves-coproducts, def-weil-abstract-derived-category.
-/
theorem derivedDirectImage_quasiCoherent_coproducts
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hqc : IsQuasiCompactPresheafMap f.hom.hom)
    (hqs : IsQuasiCompactPresheafMap (diagonalPresheafMap f.hom.hom))
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules] :
    (∀ K : X.DerivedModules, X.derivedQCohProperty K →
      Y.derivedQCohProperty ((derivedDirectImage f).obj K)) ∧
    (∀ (I : Type u) (E : I → X.DerivedQCoh),
      IsIso (sigmaComparison (derivedDirectImage f) (fun i ↦ (E i).obj))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
