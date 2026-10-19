/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorDirectSums
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Tensoring derived global sections with a constant complex

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
lem-kun-0f12.md; Stacks Project, etale-cohomology.tex, Tag 0F12
(blueprint: lem-kun-0f12).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- On a quasi-compact quasi-separated scheme of finite torsion etale cohomological
dimension, the canonical constant-complex projection map is invertible for all unbounded
complexes over any torsion commutative coefficient ring. Torsion of a unital ring is
expressed by a positive integer annihilating its unit; it then annihilates every element.
Source: Stacks Tag 0F12 (blueprint: lem-kun-0f12).

Proof plan from the DAG:
1. Write $\mathcal A=\operatorname{Mod}(X_{\Et},\Lambda)$ and $\Gamma=\Gamma(X,-):\mathcal
A\to\operatorname{Mod}(\Lambda)$. The category $\mathcal A$ is Grothendieck abelian. Sections are
additive and preserve kernels, so $\Gamma$ is left exact. Put $d=\kuncd(X)<\infty$. A torsion
unital ring has some integer $n\ge1$ with $n1=0$, hence every $\Lambda$-module sheaf is a torsion
abelian sheaf. The coefficient-forgetting cohomology comparison therefore gives $R^q\Gamma(M)=0$
for all $M\in\mathcal A$ and $q>d$. For any set-indexed family $(M_i)$, its sum is the filtered
colimit of its finite subsums, in both module sheaves and underlying abelian sheaves. Finite sums
of injective resolutions are injective resolutions (extend a map into each coordinate separately),
and additivity gives $R^q\Gamma(\bigoplus_{i\in J}M_i)=\bigoplus_{i\in J}R^q\Gamma(M_i)$ for
finite $J$. Cohomology commutes with this filtered colimit on the qcqs scheme $X$, including
constant-ring module coefficients. Thus the canonical map $\bigoplus_iR^q\Gamma(M_i)\to
R^q\Gamma(\bigoplus_iM_i)$ is an isomorphism for every $q\ge0$. This proves the sheaf-level input
of Stacks 0F11 for the actual ring $\Lambda$, rather than assuming its stated $\mathbf Z/n$
conclusion also covers $\Lambda$.
Dependencies: lem-weil-pbc-module-sheaves-grothendieck-abelian,
def-weil-pbc-global-sections-functor, def-kun-cd, lem-weil-pbc-etale-module-cohomology-forget,
lem-weil-pbc-module-sheaves-colimits-forgetful, lem-weil-pbc-cohomology-filtered-colimit.

2. For an arbitrary family $(E_i)$ in $D(\mathcal A)$ choose K-injective representatives
$I_i^\bullet$ with injective terms. The termwise sum $J^\bullet=\bigoplus_i I_i^\bullet$
represents $\bigoplus_iE_i$. Each injective term is $\Gamma$-acyclic: the resolution concentrated
in degree zero computes its higher derived sections as zero. Step 1 gives
$R^q\Gamma(J^r)=\bigoplus_i R^q\Gamma(I_i^r)=0$ for $q>0$. The unbounded acyclic-complex theorem
applies, with the uniform bound $d$, and computes $R\Gamma(E_i)$ and $R\Gamma(\bigoplus_iE_i)$ by
$\Gamma(I_i^\bullet)$ and $\Gamma(J^\bullet)$ respectively, naturally on all coprojections. The
$q=0$ comparison of Step 1 gives a termwise isomorphism
$\theta^r:\bigoplus_i\Gamma(I_i^r)\to\Gamma(J^r)$. Since $d_J\iota_i=\iota_i d_{I_i}$, equality on
every coprojection gives $\Gamma(d_J)\theta^r=\theta^{r+1}(\bigoplus_i\Gamma(d_{I_i}))$. Thus
$\theta$ is a complex isomorphism preserving coprojections. Termwise sums compute coproducts in
$D(\Lambda)$, proving that the canonical comparison $\bigoplus_iR\Gamma(E_i)\to
R\Gamma(\bigoplus_iE_i)$ is invertible. No assertion that $J^\bullet$ is K-injective is needed.
Dependencies: lem-pur-kinjective-degreewise-existence, lem-kun-grothendieck-derived-coproducts,
lem-kun-finite-cd-acyclic-complex, lem-pc-derived-module-direct-sums.

3. Let $a:(\operatorname{Sh}(X_{\Et}),\Lambda_X)\to(\operatorname{Sets},\Lambda)$ be the terminal
geometric morphism, presented using the small etale site and the one-object point site. Its module
inverse image is the constant-sheaf functor: a presheaf map from the constant presheaf $M$ to a
sheaf $F$ is determined by its component $M\to F(X)$ at the terminal object, and conversely
restriction of that component defines every component on $U\to X$. For the constant presheaf of
rings $\mathcal O(U)=\Lambda$, the component maps are $\Lambda$-linear. The module-sheafification
interface, applied to this presheaf ring and the constant presheaf module $M$, extends its action
to $\mathcal O^\#=\Lambda_X$ and identifies $\Lambda_X$-linear maps $\underline M\to F$ with these
presheaf $\Lambda$-linear maps, hence with module maps $M\to\Gamma(X,F)$, and its coefficient ring
map is the identity $a^{-1}\Lambda=\Lambda_X$. The constant-complex construction preserves
quasi-isomorphisms, so $La^*K=\underline K$. The derived ringed-topos adjunction identifies $Ra_*$
with $R\Gamma$. Apply the ringed projection-mate statement to this morphism and the fixed $E$. It
supplies exact functors $F(K)=R\Gamma(E)\otimes^L_\Lambda K$ and $G(K)=R\Gamma(E\otimes^L_\Lambda
La^*K)$ and a natural transformation $\alpha:F\to G$, compatible with shifts and distinguished
triangles. Its component is adjoint to $(\varepsilon_E\otimes1)\mu_{R\Gamma(E),K}$, hence is
exactly the canonical map in the item, including its connecting-square compatibility.
Dependencies: def-kun-constant-sheaf, lem-weil-pbc-ringed-projection-mate-exact,
lem-pc-sites-module-sheafification-interface.

4. The functor $F$ preserves set-indexed coproducts. Here is the module-complex argument, so that
no etale-sheaf tensor lemma is misapplied to $D(\Lambda)$. On the point site choose K-flat
flat-term models $P$ of $R\Gamma(E)$ and $C_i$ of $K_i$. The canonical distribution map
$\operatorname{Tot}(P\otimes\bigoplus_i C_i)\cong\bigoplus_i\operatorname{Tot}(P\otimes C_i)$
sends $p\otimes(c_i)_i$ to $(p\otimes c_i)_i$ on finite-support tensors; its inverse uses the
coprojections. Both maps respect $d_P\otimes1+(-1)^p1\otimes d_C$. For an acyclic complex $B$, the
degree-$n$ distribution isomorphism is $\bigoplus_{p+q=n}B^p\otimes(\bigoplus_i
C_i^q)\cong\bigoplus_i\bigoplus_{p+q=n}B^p\otimes C_i^q$, with the displayed signed differentials.
Thus $\operatorname{Tot}(B\otimes(\bigoplus_i C_i))$ is the sum of the acyclic
$\operatorname{Tot}(B\otimes C_i)$, whose cycles and boundaries are respectively the sums of
cycles and boundaries. The terms of $\bigoplus_i C_i$ are flat, since tensoring a module short
exact sequence with a sum is the sum of the exact tensor sequences. The derived-tensor descent
statement now computes both sides by these total complexes. Termwise module sums compute derived
coproducts, so the displayed isomorphism localizes to the canonical coproduct comparison for $F$.
This also includes the empty family.
Dependencies: lem-pc-kflat-resolution, def-pc-kflat-complex, def-pc-flat-sheaf-modules,
def-pc-tensor-complex-sheaves, lem-weil-pbc-site-derived-tensor-descent,
lem-pc-derived-module-direct-sums.

5. The functor $G$ preserves set-indexed coproducts as well. The derived adjunction of Step 3
makes $L=La^*$ a left adjoint to $R=R\Gamma$. Explicitly
Hom(L(⨁ᵢ Kᵢ), H) = Hom(⨁ᵢ Kᵢ, RH) = ∏ᵢ Hom(Kᵢ, RH) = ∏ᵢ Hom(LKᵢ, H),
naturally in $H$, and the bijections take the legs to $L$ of the original coprojections. This is
the coproduct universal property, so $L$ preserves these sums. Tensor with $E$ in the etale
derived category preserves sums by the cited tensor theorem. Applying the coproduct comparison for
$R\Gamma$ proved in Step 2 proves the assertion for their composite $G$. Under the two functors'
coproduct comparisons, naturality on each coprojection identifies $\alpha_{\bigoplus_iK_i}$ with
$\bigoplus_i\alpha_{K_i}$. Thus if every $\alpha_{K_i}$ is invertible, the direct sum of their
inverses is an inverse of this component.
Dependencies: lem-weil-pbc-ringed-projection-mate-exact, lem-kun-derived-tensor-direct-sums.

6. Let $\mathcal C$ be the full subcategory of $D(\Lambda)$ consisting of $K$ for which $\alpha_K$
is invertible. Under the tensor-unit identifications the projection mate satisfies
$\alpha_\Lambda=1_{R\Gamma(E)}$. Its compatibility with integer shifts identifies
$\alpha_{\Lambda[k]}$ with the shift of that identity, so $\Lambda[k]\in\mathcal C$ for every
integer $k$. Dependency: lem-weil-pbc-ringed-projection-mate-exact.

7. For a distinguished triangle in $D(\Lambda)$, Step 3 produces a morphism between its images
under $F$ and $G$, including the shifted connecting square. The third-isomorphism triangle theorem
shows that if two vertices lie in $\mathcal C$, then the third does too. The class is also closed
under isomorphisms by naturality and under retracts: if $i:K\to H$, $r:H\to K$ satisfy $ri=1$ and
$\alpha_H$ is invertible, then $F(r)\alpha_H^{-1}G(i):G(K)\to F(K)$ is inverse to $\alpha_K$.
Indeed naturality gives $\alpha_K F(r)=G(r)\alpha_H$ and $G(i)\alpha_K=\alpha_H F(i)$, so the two
composites reduce to $G(ri)$ and $F(ri)$. Together with Steps 4-5 this proves all required closure
properties.
Dependencies: lem-weil-pbc-ringed-projection-mate-exact, lem-sf-triangle-morphism-iso.

8. Apply derived-module free generation with $A=\Lambda$. The subcategory $\mathcal C$ contains
all shifts $\Lambda[k]$ by Step 6 and is closed under set-indexed direct sums, third vertices of
distinguished triangles, and retracts by Steps 5 and 7. It therefore contains every object of
$D(\Lambda)$. Hence $\alpha_K$ is invertible for the arbitrary complex $K$ in the statement. This
is precisely the canonical tensor-with-constant-complex map identified in Step 3.
Dependency: lem-pc-derived-module-free-generation.
-/
theorem isIso_constantDerivedProjectionMap_of_finite_torsion_cd
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hcd : X.torsionEtaleCohomologicalDimension < ⊤)
    (hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0)
    (E : DerivedCategoryModule Λ X) (K : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    IsIso (constantDerivedProjectionMap (ModuleCat.{u + 1} Λ) X E K) := by
  sorry

end AlgebraicGeometry.Etale
