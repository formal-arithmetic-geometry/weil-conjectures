/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.CategoryTheory.Sites.RingedSitePoint
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTensorConeTwoOutOfThree
import Sheaf.Algebra.Homology.AcyclicKFlatTensor
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.CategoryTheory.Sites.ToposLocalizationSitePresentation
import Sheaf.Paper.KFlatRingedToposPullback

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Algebra.Homology.UniversalAcyclicModuleKFlat
import Sheaf.CategoryTheory.Sites.FpStalkRealization
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-!
# K-flatness and stalks of a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 0DEN, lemma-check-K-flat-stalks
(blueprint: lem-sfb-ringed-site-kflat-stalk-criterion).
-/

@[expose] public section
set_option autoImplicit false

universe u v w t
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

/-- K-flat complexes have K-flat stalks at every topos point, and a specified
conservative family detects K-flatness. RingedSitePoint fixes the ordinary stalk
ring, module action and functor on maps by inverse-image operation graphs. Such
presentations exist for every point, and both assertions hold for every presentation.
There is no flat-term or boundedness hypothesis, and the family may be empty.
Source: Stacks 0DEN (blueprint: lem-sfb-ringed-site-kflat-stalk-criterion).

Proof plan:
1. For any point $p$, exact transported module inverse image preserves kernels and cokernels.
Thus, using $H^n=\ker(d^n)/\operatorname{im}(d^{n-1})$ and
$\operatorname{im}(d)=\ker(\operatorname{coker}(d))$, it gives $H^n(K_p)\cong p^{-1}H^n(K)$ and
preserves acyclic complexes. Apply the ordinary total-tensor comparison to the ringed-topos map
$(\mathbf{Set},R_p)\to(\operatorname{Sh}(C),R)$ with identity coefficient map. Tensor extension
along that identity is removed by $a\otimes m\mapsto am$. Consequently
$(\operatorname{Tot}(F\otimes_RK))_p\cong\operatorname{Tot}(F_p\otimes_{R_p}K_p)$ for all
unbounded complexes. The cited comparison is already an isomorphism of signed total complexes, so
no boundedness or interchange of infinite products is being asserted. Uses:
lem-trf-geometric-inverse-image-exact, lem-pur-cochain-pullback-tensor-coherence,
def-weil-abstract-derived-category.
2. For the forward direction only, replace $\operatorname{Sh}(C)$ by a finite-limit subcanonical
site presentation using the presentation theorem with the terminal sheaf as its specified object.
Transport $R$, $K$, and $p$ along the topos equivalence. The inverse-image functors of this
equivalence and its inverse give inverse equivalences on module sheaves: their composites preserve
each addition and scalar action through the finite-product comparisons, so the topos inverse
equations are module-linear. Both functors are exact by the inverse-image theorem and commute with
total tensor by the ordinary cochain comparison. Hence K-flatness is preserved and reflected:
every acyclic test complex on one side is the image, up to the inverse equations, of an acyclic
test complex on the other, and its total tensor is the image of the corresponding total tensor.
The composite point gives the same stalk ring and stalk complex by these inverse equations. We may
therefore assume $C$ has finite limits without assuming this in the item. Uses:
lem-trf-topos-localization-site-presentation, lem-trf-geometric-inverse-image-exact,
lem-pur-cochain-pullback-tensor-coherence, def-trf-geometric-morphism, def-pc-kflat-complex.
3. Assume $K$ is K-flat. Choose a quasi-isomorphism $a:L\to K$ with $L$ K-flat and all $L^n$ flat,
using the site resolution theorem. Put $E=C(a)$. The quasi-isomorphism--cone criterion says $E$ is
acyclic. For every acyclic $A$, the two tensors with $L$ and $K$ are acyclic, so the tensor-cone
two-out-of-three theorem implies the tensor with $E$ is acyclic; this is exactly K-flatness of
$E$. The flat-term pullback theorem, applied to the point with coefficient map
$p^{-1}R\xrightarrow{\mathrm{id}}R_p$, proves $L_p$ K-flat. Its flat-term hypothesis is used only
for this chosen resolution, not for $K$ or $E$. Uses: lem-pc-kflat-resolution,
lem-pur-quasi-iso-cone-acyclic, lem-pc-kflat-tensor-cone-two-out-of-three, def-pc-kflat-complex,
lem-weil-pbc-ringed-topos-kflat-pullback.
4. We now handle an arbitrary acyclic K-flat $E$ on this finite-limit site. Fix a finitely
presented $R_p$-module $M$. The local realization theorem gives a pointed object $(U,x)$, its
lifted point $q$ of $C/U$, and an $R_U$-module sheaf $F$ with $F_q\cong M$ and $(E|_U)_q\cong
E_p$. Exact restriction makes $E|_U$ acyclic, and the restriction K-flat theorem makes it K-flat.
The universal tensor-acyclicity theorem therefore makes
$\operatorname{Tot}(F[0]\otimes_{R_U}E|_U)$ acyclic. Take its $q$-stalk: exactness and the
ordinary signed cochain tensor comparison identify this acyclic complex with
$\operatorname{Tot}(M[0]\otimes_{R_p}E_p)$. The signed symmetry from the same cochain comparison
theorem changes the factor order to $\operatorname{Tot}(E_p\otimes_{R_p}M[0])$; here the sign is
$1$ because $M$ has degree zero. Uses: lem-sfb-site-fp-stalk-realization,
lem-sfb-ringed-site-restriction-kflat, lem-pur-acyclic-kflat-tensor-arbitrary,
lem-trf-geometric-inverse-image-exact, lem-pur-cochain-pullback-tensor-coherence.
5. The preceding construction applies to every finitely presented $M$, so the universal-acyclicity
criterion for ordinary modules shows $E_p$ is K-flat. Return to $E=C(a)$ from step 3. Exact
additive inverse image commutes with the cone matrix: $p^{-1}(K^n\oplus L^{n+1})=K_p^n\oplus
L_p^{n+1}$ and its differential is still $(d_K,a;0,-d_L)$. Thus $E_p\cong C(a_p)$. For any acyclic
$R_p$-module complex $B$, the tensors with $L_p$ and $E_p$ are acyclic. Apply the tensor-cone
two-out-of-three theorem on the one-object ringed site presenting ordinary $R_p$-modules to obtain
acyclicity of $\operatorname{Tot}(B\otimes_{R_p}K_p)$. This is the module definition of
K-flatness, proving the forward direction for every point. Uses:
lem-sfb-universal-acyclic-module-kflat, lem-trf-geometric-inverse-image-exact,
def-weil-abstract-derived-category, lem-pc-kflat-tensor-cone-two-out-of-three,
def-pc-module-kflat-complex.
6. For the converse, let $F$ be any acyclic complex of $R$-module sheaves and put
$T=\operatorname{Tot}(F\otimes_RK)$. Exact inverse image makes each $F_{p_i}$ acyclic. K-flatness
of $K_{p_i}$ makes $\operatorname{Tot}(F_{p_i}\otimes_{R_{p_i}}K_{p_i})$ acyclic, and the ordinary
cochain comparison identifies this with $T_{p_i}$. Hence $p_i^{-1}H^n(T)=0$ for all $i,n$. The
underlying set-sheaf map $H^n(T)\to0$ becomes an isomorphism at every $p_i$, so conservativity
makes it an isomorphism. Its inverse is module-linear, since the only inverse section is zero.
Therefore all $H^n(T)$ vanish and $T$ is acyclic. Since $F$ was arbitrary, $K$ is K-flat. This
uses precisely the given family, including an empty family when its conservativity forces the
topos to be degenerate. Uses: lem-trf-geometric-inverse-image-exact,
lem-pur-cochain-pullback-tensor-coherence, def-weil-abstract-derived-category,
def-pc-module-kflat-complex, def-pc-kflat-complex.
-/
theorem ringedSite_kFlat_stalk_criterion
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{w})
    (K : CochainComplex (ringedSiteModules.{w}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :
    (∀ (p : GeometricMorphism (Type w) (Sheaf J.toGrothendieck (Type w)))
      (s : RingedSitePoint R p),
      IsKFlatIndependentCoefficients (R := R) K →
        (HomologicalComplex.quasiIso (ModuleCat.{w} s.ring) (.up ℤ)).kFlat
          ((s.modules.mapHomologicalComplex (.up ℤ)).obj K)) ∧
    (∀ (I : Type t)
      (p : I → GeometricMorphism (Type w) (Sheaf J.toGrothendieck (Type w)))
      (s : ∀ i : I, RingedSitePoint R (p i)),
      JointlyReflectIsomorphisms (fun i : I ↦ (p i).inverse) →
      (∀ i : I,
        (HomologicalComplex.quasiIso (ModuleCat.{w} (s i).ring) (.up ℤ)).kFlat
          (((s i).modules.mapHomologicalComplex (.up ℤ)).obj K)) →
      IsKFlatIndependentCoefficients (R := R) K) := by
  sorry

end CochainComplex
