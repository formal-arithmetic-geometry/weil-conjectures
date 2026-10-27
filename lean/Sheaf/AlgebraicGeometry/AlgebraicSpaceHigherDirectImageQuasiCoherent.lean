/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-! # Quasi-coherence of higher direct images on algebraic spaces

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 0720,
lemma-higher-direct-image (blueprint: lem-sfb-space-higher-direct-image-quasi-coherent).

Higher direct image is computed in all modules, using the canonical direct image on
an equivalent small ringed model, and transported back to the original small étale site.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Higher direct images along a quasi-compact quasi-separated map preserve quasi-coherence.
Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 0720,
lemma-higher-direct-image (blueprint: lem-sfb-space-higher-direct-image-quasi-coherent).

The natural number i includes degree zero. Its cast to an integer selects the same
cohomological degree of the unbounded derived direct image of F placed in degree zero.
The small-module equivalence is the recorded restriction equivalence, so the conclusion
is quasi-coherence on the original small étale site, with its original structure sheaf.
For a module in degree zero, K-injective computation agrees with an ordinary injective
resolution. The localization universe w is arbitrary.

Proof (the accepted relative Čech route preceding Stacks Tag 0720):
1. It suffices to prove the assertion after every affine etale chart $V\to Y$. Indeed
   quasi-coherence is a local-presentation condition: the presentations on a covering of each
   affine chart compose to covering presentations on each object of $Y_{\mathrm{et}}$; arbitrary
   scheme charts have affine open covers. Restricting $F$ to $X_V=X\times_YV$ preserves its local
   presentations. The higher-image restriction isomorphism identifies the desired restriction with
   $R^if_{V,*}(F|_{X_V})$. Quasi-compactness is stable under base change by the cited affine-test
   lemma; the relative diagonal of $f_V$ is the base change of that of $f$, so the same stability
   proves quasi-separatedness. Hence replace $Y$ by $V$. Uses:
   def-trf-space-quasi-coherent-module, lem-sfb-space-higher-image-etale-restriction,
   lem-sfb-space-quasicompact-affine-tests.
2. Now $Y$ is affine, hence quasi-compact and quasi-separated. Quasi-compactness of $f$ gives
   quasi-compactness of $X$, and the source clause of the qcqs-product lemma gives
   quasi-separatedness of $X$. For this absolute formulation regard spaces over
   $\operatorname{Spec}\mathbf Z$ by the cited change-of-base identification. The cited
   atlas/topology equivalence identifies this quasi-compactness with quasi-compactness of the
   point space, as required by the atlas and permanence statements. Choose an affine surjective
   etale scheme chart $U\to X$. For $p\geq0$ put $U_p=U^{\times_X(p+1)}$. Inductively $U_p$ is a
   scheme: $U_0=U$, and $U_p\times_XU$ is the base change of the representable etale map $U\to X$
   to the scheme $U_p$. It is qcqs by induction and the qcqs-product clause. The permanence lemma
   therefore says $a_p:U_p\to Y$ is qcqs, and the affine-test equivalence identifies this with
   scheme quasi-compactness; its diagonal has the same scheme tests for quasi-separatedness. Uses:
   lem-weil-pbc-affine-scheme-qcqs, lem-sfb-space-qcqs-source-products,
   lem-sfb-space-change-base-to-integers, lem-sfb-qc-space-affine-etale-atlas,
   lem-trf-space-fibre-products-etale-covers, lem-sfb-space-qcqs-permanence,
   lem-sfb-space-quasicompact-affine-tests, lem-a1-space-etale-open-image.
3. Let $F_p=F|_{U_p}$. Each $u_p:U_p\to X$ is etale (successive base changes and compositions of
   the atlas), so restriction preserves the local free presentations defining quasi-coherence.
   Apply the relative Cech module spectral sequence to $f$ and this atlas. Its first page is
   $E_1^{p,q}=R^qa_{p,*}F_p$ and it converges to $R^{p+q}f_*F$ with the specified finite
   filtration. Every $a_p$ is a qcqs scheme morphism by step 2; the scheme small-etale
   higher-image comparison therefore makes every $E_1^{p,q}$ quasi-coherent. This uses
   structure-sheaf modules throughout. Uses: lem-trf-space-chartwise-etale-permanence,
   def-trf-space-quasi-coherent-module, lem-sfb-space-relative-cech-module-spectral-sequence,
   lem-sfb-scheme-etale-higher-image-comparison.
4. Every later page is quasi-coherent, by induction on the page: at each bidegree the next page is
   the cokernel of the map from the incoming image to the outgoing kernel. These images and
   kernels, and then that cokernel, are quasi-coherent by the cited closure statement. At fixed
   $(p,q)$ first-quadrant differentials vanish for sufficiently large page (an incoming
   differential requires $r\leq p$, an outgoing one requires $r\leq q+1$). Thus the stable term
   $E_\infty^{p,q}$ is quasi-coherent. No closure under arbitrary subobjects is used. Uses:
   lem-sfb-space-qcoh-kernels-colimits, lem-sfb-space-relative-cech-module-spectral-sequence.
5. For fixed $i\geq0$, convergence gives $F^0=R^if_*F$ and $F^{i+1}=0$ with
   $F^p/F^{p+1}=E_\infty^{p,i-p}$. The zero module is quasi-coherent (its zero presentation).
   Descending finite induction on $p=i,\ldots,0$ applies extension closure to $0\to F^{p+1}\to
   F^p\to E_\infty^{p,i-p}\to0$. It gives quasi-coherence of $F^0$. Step 1 then gives the
   assertion on the original $Y$, including $i=0$. Uses:
   lem-sfb-space-relative-cech-module-spectral-sequence, lem-sfb-space-qcoh-extension-closed.
-/
theorem isQuasicoherent_higherDirectImage_of_quasiCompact_quasiSeparated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hqc : IsQuasiCompactPresheafMap f.hom.hom)
    (hqs : IsQuasiCompactPresheafMap (diagonalPresheafMap f.hom.hom))
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    ((Y.smallModuleEquivalence.inverse).obj
      ((DerivedCategory.homologyFunctor Y.SmallModules (i : ℤ)).obj
        ((derivedDirectImage f).obj
          ((DerivedCategory.singleFunctor X.SmallModules 0).obj
            (X.smallModuleRestriction.obj F))))).IsQuasicoherent := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
