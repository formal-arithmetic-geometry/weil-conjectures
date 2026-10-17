/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SiteCechEdgeNormalization
public import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
public import Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections
public import Mathlib.CategoryTheory.Sites.Pullback
public import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.SiteInjectiveCechAcyclic
import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
import Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic

import Sheaf.CategoryTheory.DoubleComplexTotal
import Sheaf.CategoryTheory.SiteCechComplex
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.Algebra.Homology.FirstQuadrantAugmentation
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Homology.ModelCategory.Injective
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic

/-!
# Canonical acyclic Čech edges and their compatibility

Source: Stacks Project, Cohomology on Sites, Tags 03AX, 03AZ, 03F7, 03FD
(blueprint: lem-weil-pbc-acyclic-cech-edge-compatibility).

Cohomology is expressed by right derived evaluation, as in the source's definition.
The existing cohomology-over-object comparison identifies it with `Sheaf.H'`.
Module cohomology is computed in the module category before forgetting scalars.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

-- The upstream theorem supplies the instance on every small ringed site.
attribute [instance] SheafOfModules.isGrothendieckAbelian

/-- The canonical edge exists, is independent of resolutions, is natural for
additive sheaf maps, and is invertible on tuple-acyclic coefficients.
Source: Stacks 03AX, 03AZ, 03F7
(blueprint: lem-weil-pbc-acyclic-cech-edge-compatibility).

Proof: (1) Apply Čech termwise to an injective resolution. (2) Exact augmented
injective Čech rows make alpha a quasi-isomorphism. (3) Tuple acyclicity makes
beta a quasi-isomorphism by first-quadrant augmentation; the transpose sign is
(-1)^(t*r), equal to one on both axes. (4) Lift an additive coefficient map to
resolutions. The induced total map commutes with both augmentations, giving
naturality. (5) Two lifts are homotopic; the total homotopy in Čech degree t is
(-1)^t times the Čech image of the resolution homotopy. Thus the normalized
edge is independent of the resolution and lift. This uses only additivity. 

Full DAG proof:

1. Choose a nonnegative injective resolution $a:A\to I^\bullet$ in abelian sheaves. Put
$D^{t,r}=\prod_{\mathbf i\in I_{\mathcal U}^{t+1}}I^r(U_{\mathbf i})$, where $I_{\mathcal U}$
denotes the finite index set of the covering (not the resolution). The Cech restriction
differential commutes with the resolution differential by naturality. Define $\alpha^n$ by
restricting $I^n(1)$ to the $(0,n)$ summand of $T=\operatorname{Tot}D$, and $\beta^n$ by
applying $a$ on every component of $\check C^n(\mathcal U,A)$ and including the $(n,0)$ summand.
Both are chain maps: restrictions of a global section have zero Cech differential, $d_Ia=0$, and
the vertical sign is $+1$ on the image of $\alpha$.
Uses: lem-weil-pbc-site-sheaves-enough-injectives, def-weil-pbc-site-cech-complex, def-sp-
double-complex-total.

2. For each $r$, the augmented row $0\to I^r(1)\to\check C^0(\mathcal U,I^r)\to\check
C^1(\mathcal U,I^r)\to\cdots$ is exact: its positive cohomology vanishes by injective Cech
acyclicity, and its degree-zero kernel is precisely the image of restriction by the sheaf
equalizer condition. Apply the first-quadrant augmentation lemma with the first index the Cech
degree. Its augmentation is $\alpha$, so $\alpha$ is a quasi-isomorphism. Each diagonal has only
$n+1$ summands; no boundedness of the Cech degree is needed.
Uses: lem-weil-pbc-site-injective-cech-acyclic, def-weil-pbc-sites-and-cohomology, lem-sc-first-
quadrant-column-augmentation.

3. For each fixed $t$, the resolution column has cohomology $\prod_{\mathbf i}H^r(U_{\mathbf
i},A)$: kernels and images of the differential in a finite product are computed componentwise.
The augmentation identifies its degree-zero kernel with $\prod_{\mathbf i}A(U_{\mathbf i})$, and
the hypothesis makes all positive cohomology zero. Apply the same augmentation lemma with the
resolution index first to obtain that $\beta$ is a quasi-isomorphism. Explicitly the transposed
total has differential $d_I+(-1)^r d_C$; multiplication by $(-1)^{tr}$ on bidegree $(t,r)$
identifies it with $T$, and is the identity on $r=0$, so its augmentation becomes exactly
$\beta$. Thus the specified edge $H^q(\alpha)^{-1}H^q(\beta)$ is an isomorphism for every
$q\ge0$.
Uses: def-weil-pbc-sites-and-cohomology, def-sp-double-complex-total, lem-sc-first-quadrant-
column-augmentation.

4. For an additive coefficient map $g:A\to A'$, lift $g$ to a map $v:I^\bullet\to I'^\bullet$ of
injective resolutions. On bidegree $(t,r)$ apply $v^r$ to each section. This defines a total map
$V:T\to T'$ and gives the literal chain-map equations $V\alpha=\alpha'\Gamma(v)$ and
$V\beta=\beta'\check C(g)$. On cohomology, $H(\Gamma(v))$ is the canonical coefficient map.
Multiplying the first equation by the inverses of $H(\alpha)$ and $H(\alpha')$ and using the
second proves $H(g)e_A=e_{A'}H(\check C(g))$. This uses only additivity and commutation with
restrictions, so semilinear maps that are additive are allowed.
Uses: lem-weil-pbc-injective-resolution-lift-exists, lem-weil-pbc-derived-functor-map-via-lift,
def-weil-pbc-site-cech-complex.

5. Take $g=\mathrm{id}_A$ in the preceding step to compare any two resolutions. Any two lifts
are homotopic, by applying uniqueness of lifts to the quasi-isomorphism $A[0]\to I^\bullet$. If
$v-w=d k+k d$, the induced total maps are homotopic via $K|_{(t,r)}=(-1)^t\check C^t(k^r)$.
Indeed the two horizontal contributions cancel, while the two vertical contributions are
$d_Ik+kd_I$ because the two signs $(-1)^t$ multiply to $1$. On global sections the homotopy is
$\Gamma(k)$. Therefore all induced cohomology maps agree. Comparisons for identities and
compositions agree by the same uniqueness, giving resolution independence of the specified edge
under the canonical cohomology identifications.
Uses: lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, def-sp-double-complex-total, def-
weil-pbc-sites-and-cohomology.
-/
theorem exists_acyclicCechEdge
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type u} [Finite T] {U : C} (hU : IsTerminal U)
    (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom) :
    ∃! e : ∀ (A : Sheaf J.toGrothendieck AddCommGrpCat.{u})
      (_hA : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
        IsZero (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (S.W p t))).rightDerived r).obj A)) (q : ℕ),
      (S.cohomologyFunctor q).obj A.obj ⟶
        ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj A,
      (∀ A hA q, S.IsNormalizedEdge (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u})
        q (e A hA q) ∧ IsIso (e A hA q)) ∧
      (∀ (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}) hA
        (B : Sheaf J.toGrothendieck AddCommGrpCat.{u}) hB (g : A ⟶ B) (q : ℕ),
        (S.cohomologyFunctor q).map g.hom ≫ e B hB q =
          e A hA q ≫
            ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived
              q).map g) := by
  sorry

/-- Normalized edges commute with site change and an additive coefficient map.
Source: Stacks 03AX and 03F7
(blueprint: lem-weil-pbc-acyclic-cech-edge-compatibility).

Proof: (6) Exact inverse image and the monomorphic injective-resolution
augmentation give an augmentation-preserving lift to the target resolution.
Its adjoint is v. Its global components w compute the canonical cohomology map.
Comparison with a resolution of the inverse image gives the same map by
uniqueness up to homotopy. (7) Apply v on every tuple, transported by c. Each
face commutes with its section map by naturality, so hC is a cochain map.
The induced total map commutes literally with alpha and beta. On cohomology,
cancel the invertible alpha maps to obtain the asserted square. 

Full DAG proof:

6. For site change choose $B\to J^\bullet$ injective on $\mathcal D$. Exactness of $f^{-1}$
makes $f^{-1}A[0]\to f^{-1}I^\bullet$ a degreewise monomorphic quasi-isomorphism. Lift the map
$f^{-1}A[0]\to B[0]\to J^\bullet$, whose first arrow is adjoint to $h$, along this augmentation
to $j:f^{-1}I^\bullet\to J^\bullet$, strictly over the augmentations. Adjunction gives
$v:I^\bullet\to f_*J^\bullet$. Its section maps are $I^r(V)\to J^r(uV)$, compatible with every
restriction. Their global map $w:\Gamma_{\mathcal C}I\to\Gamma_{\mathcal D}J$ computes $h_H$. To
check the last assertion against the canonical pullback, insert an injective resolution $L$ of
$f^{-1}A$, a lift $f^{-1}I\to L$, and a coefficient lift $L\to J$; the canonical pullback and
coefficient formulas compute their composite on sections. Its composite is homotopic to $j$ by
lift uniqueness, so it has the same cohomology map.
Uses: lem-weil-pbc-site-pullback-abelian-exact, lem-weil-pbc-lift-along-injective-quasi-iso,
lem-weil-pbc-site-cohomology-pullback, lem-weil-pbc-injective-resolution-lift-exists, lem-weil-
pbc-derived-functor-map-via-lift, lem-weil-pbc-lift-to-injective-unique-up-to-homotopy.

7. The section components of $v$ define $V^{t,r}:\check C^t(\mathcal U,I^r)\to\check
C^t(u\mathcal U,J^r)$, using the canonical tuple-product identifications preserved by $u$. For
each omitted index $a$, the equation $v_{U_{\mathbf
i}}\operatorname{res}_a=\operatorname{res}_{u(a)}v_{U_{\mathbf i\setminus a}}$ shows that $V$
commutes with $d_C$; since $v$ is a chain map it commutes with $d_I$ and hence the total
differential. On the two axes the equations are $V\alpha_{\mathcal C}=\alpha_{\mathcal D}w$ and
$V\beta_A=\beta_B h_C$. Both are literal equalities: the former is restriction naturality, the
latter is the strictly commuting lifted augmentation of step 6. Applying cohomology and
inverting both $H(\alpha)$ proves $h_H e_{\mathcal U,A}=e_{u\mathcal U,B}H(h_C)$. The two edges
are isomorphisms by steps 2--3 using the separately assumed acyclicity of $A$ and $B$.
Uses: def-weil-pbc-sites-and-cohomology, def-weil-pbc-site-cech-complex, def-sp-double-complex-
total.
-/
theorem acyclicCechEdge_siteChange
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (u : C ⥤ D)
    (hc : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map u ∈ K (u.obj X))
    (hp : ∀ (X Y Z : C) (R : Presieve X), R ∈ J X →
      ∀ (a : Y ⟶ X) (b : Z ⟶ X), R a → PreservesLimit (cospan a b) u)
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    {T : Type u} [Finite T] {U : C} (hU : IsTerminal U) (huU : IsTerminal (u.obj U))
    (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (S' : SiteCechComplex (fun t ↦ u.obj (f t)) (fun t ↦ u.map (hom t)))
    (c : ∀ (p : ℕ) (t : Fin (p + 1) → T), u.obj (S.W p t) ≅ S'.W p t)
    (hcpr : ∀ (p : ℕ) (t : Fin (p + 1) → T) (k : Fin (p + 1)),
      (c p t).hom ≫ S'.pr p t k = u.map (S.pr p t k))
    (A : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (B : Sheaf K.toGrothendieck AddCommGrpCat.{u})
    (h : A ⟶ (u.sheafPushforwardContinuous AddCommGrpCat.{u}
      J.toGrothendieck K.toGrothendieck).obj B)
    (hA : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
      IsZero (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (S.W p t))).rightDerived r).obj A))
    (hB : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
      IsZero (((sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (S'.W p t))).rightDerived r).obj B))
    (q : ℕ)
    (eA : (S.cohomologyFunctor q).obj A.obj ⟶
      ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj A)
    (eB : (S'.cohomologyFunctor q).obj B.obj ⟶
      ((sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj U))).rightDerived q).obj B)
    (heA : S.IsNormalizedEdge (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) q eA)
    (heB : S'.IsNormalizedEdge (sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u}) q eB)
    (I : InjectiveResolution A) (L : InjectiveResolution B) :
    (∃ v : I.cocomplex ⟶
      ((u.sheafPushforwardContinuous AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj L.cocomplex,
      I.ι.f 0 ≫ v.f 0 = h ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).map (L.ι.f 0)) ∧
    ∀ (v : I.cocomplex ⟶
      ((u.sheafPushforwardContinuous AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj L.cocomplex)
      (hv : I.ι.f 0 ≫ v.f 0 = h ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).map (L.ι.f 0)),
      ∃ (w : ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex ⟶
        ((sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj U))).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj L.cocomplex)
        (hC : S.complex A.obj ⟶ S'.complex B.obj),
        (∀ n : ℕ, w.f n = (v.f n).hom.app (op U)) ∧
        (∀ (n : ℕ) (s : S.cochains A.obj n) (t : Fin (n + 1) → T),
          (hC.f n s) t = B.obj.map (c n t).inv.op ((h.hom.app (op (S.W n t))) (s t))) ∧
        eA ≫ (I.isoRightDerivedObj (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom ≫
            HomologicalComplex.homologyMap w q ≫
              (L.isoRightDerivedObj (sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
                (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj U))) q).inv =
          HomologicalComplex.homologyMap hC q ≫ eB := by
  sorry

set_option maxHeartbeats 800000 in
-- Comparing two derived section functors requires repeated resolution elaboration.
/-- Forgetting scalar multiplication preserves the canonical normalized edge.
The comparison c is specified both by all resolution lifts and by the unique
morphism of universal delta-functors inducing the identity on sections.
Source: Stacks 03FC, 03FD and 03AX
(blueprint: lem-weil-pbc-acyclic-cech-edge-compatibility).

Proof: (8) Module sheaves are Grothendieck abelian and have injective
resolutions. Forgetting is exact; underlying module injectives are acyclic
for abelian evaluation, although they need not be injective abelian sheaves.
The acyclic-resolution theorem computes the comparison by any strict lift
from the forgotten module resolution to an abelian injective resolution.
(9) Both delta-functors are effaceable and universal. The comparison inducing
the identity in degree zero is unique. Dimension shifting along successive
resolution cokernels identifies it with the preceding acyclic-resolution
map, with the same connecting-map convention. (10) Module injective Čech
acyclicity makes alpha invertible; tuple module acyclicity does the same for
beta. The underlying Čech complexes and both augmentations are unchanged by
forgetting. Applying Čech to the resolution lift gives both augmentation
squares. Cancel alpha on cohomology, yielding the displayed edge equality. 

Full DAG proof:

8. The category of sheaves of left $\mathcal O$-modules on the small site $\mathcal C$ is
Grothendieck abelian by [lem-weil-pbc-ring-sheaves-grothendieck], in a universe containing the
site and coefficient values. Hence it has enough injectives by [lem-sp-grothendieck-enough-
injectives]. For modules choose a nonnegative injective module resolution $M\to P^\bullet$, as
in the statement's convention for module cohomology. After forgetting scalars it remains an
exact augmented resolution: kernels are sectionwise and the underlying sheaf of a cokernel is
the sheafification of the sectionwise abelian cokernel, so forgetting preserves kernels and
cokernels. Every $P^r_{ab}$ is acyclic for abelian evaluation at every object by the ringed-site
injective-module acyclicity theorem; it is not asserted to be an injective abelian sheaf. The
acyclic-resolution theorem therefore identifies $H^q(\Gamma(P_{ab}))$ with $H^q(\mathcal
C,M_{ab})$, by any augmentation-preserving map $P_{ab}\to J$ to an abelian injective resolution.
Such a strict map exists by the monomorphic quasi-isomorphism lifting lemma. Denote it by $k$.
Uses: def-weil-sheaf-of-modules-category, lem-sc-injective-module-abelian-acyclic-zariski,
lemma-weil-pbc-leray-acyclicity, lem-weil-pbc-lift-along-injective-quasi-iso, lem-weil-pbc-
module-sheaves-colimits-forgetful, lem-weil-pbc-ring-sheaves-grothendieck, lem-sp-grothendieck-
enough-injectives.

9. The canonical module-to-abelian identification is the resolution map $H^q(\Gamma(k))$ just
obtained. Here is its normalization: the module right-derived delta-functor is universal, while
abelian cohomology precomposed with exact forgetting is a delta-functor and vanishes in positive
degrees on module injectives. Hence it is effaceable and universal as well, and the unique
delta-functor morphism inducing the identity on sections is an isomorphism. Its value on $M\to
P^\bullet$ is the acyclic-resolution comparison: successively put $M_0=M$,
$M_{r+1}=\operatorname{coker}(M_r\to P^r)$ and use $0\to M_r\to P^r\to M_{r+1}\to0$. In degree
one both comparisons are induced by the identity on sections modulo the image of $\Gamma(P^0)$;
in higher degrees the connecting isomorphisms reduce degree by one, since the positive
cohomology of each $P^r$ vanishes in both theories. Induction therefore identifies the universal
comparison with $H^q(\Gamma(k))$ in every degree, with the same connecting-map convention.
Uses: lem-weil-pbc-right-derived-universal-delta-functor, lem-sc-injective-module-abelian-
acyclic-zariski, lemma-weil-pbc-leray-acyclicity, lem-weil-pbc-module-sheaves-colimits-
forgetful.

10. For $P$ the module restriction augmentation $\alpha_P:\Gamma(P)\to\operatorname{Tot}\check
C(\mathcal U,P)$ is a quasi-isomorphism by injective-module Cech acyclicity, the degree-zero
sheaf equalizer, and the same augmentation lemma used in step 2. The module coefficient
augmentation $\beta_M$ is a quasi-isomorphism by step 3 applied to module evaluation and the
assumed module acyclicity on every tuple. Underlying section Cech complexes and both axis maps
are unchanged on forgetting scalars. Applying $\check C$ termwise to $k:P_{ab}\to J$ gives $K$
between the two totals with $K\alpha_P=\alpha_J\Gamma(k)$ and $K\beta_M=\beta_{M_{ab}}$,
component by component. Consequently
$H(\Gamma(k))H(\alpha_P)^{-1}H(\beta_M)=H(\alpha_J)^{-1}H(\beta_{M_{ab}})$, the required
compatibility with the canonical identification of step 9. No claim that forgetting preserves
injectives or that tensoring with the ring sheaf is exact occurs.
Uses: lem-weil-pbc-ringed-site-injective-module-cech-acyclic, def-weil-pbc-sites-and-cohomology,
lem-sc-first-quadrant-column-augmentation, def-weil-pbc-site-cech-complex.
-/
theorem acyclicCechEdge_forgetModules
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck RingCat.{u})
    {T : Type u} [Finite T] {U : C} (hU : IsTerminal U)
    (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom) :
    ∃ c : ∀ q : ℕ,
      (SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q ≅
      SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q,
      (∀ M : SheafOfModules.{u} R,
        (SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).toRightDerivedZero.app M ≫
            (c 0).hom.app M =
          (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).toRightDerivedZero.app
              ((SheafOfModules.toSheaf R).obj M)) ∧
      (∃ (G H : CohomologicalDeltaFunctor (SheafOfModules.{u} R) AddCommGrpCat.{u})
        (g : ∀ q : ℕ, G.F q ≅
          (SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q)
        (h : ∀ q : ℕ, H.F q ≅ SheafOfModules.toSheaf R ⋙
          (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q),
        G.IsUniversal ∧ H.IsUniversal ∧
          ∃ t : CohomologicalDeltaFunctor.Hom G H,
            (∀ q : ℕ, (g q).inv ≫ t.app q ≫ (h q).hom = (c q).hom) ∧
            ∀ t' : CohomologicalDeltaFunctor.Hom G H,
              (g 0).inv ≫ t'.app 0 ≫ (h 0).hom = (c 0).hom → t' = t) ∧
      (∀ (M : SheafOfModules.{u} R) (P : InjectiveResolution M)
        (L : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
        (k : ((SheafOfModules.toSheaf R).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj P.cocomplex ⟶ L.cocomplex)
        (hk : (SheafOfModules.toSheaf R).map (P.ι.f 0) ≫ k.f 0 = L.ι.f 0)
        (q : ℕ),
        (c q).hom.app M =
          (P.isoRightDerivedObj (SheafOfModules.toSheaf R ⋙
            sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
              (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom ≫
          HomologicalComplex.homologyMap
            (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
              (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
                (ComplexShape.up ℕ)).map k) q ≫
          (L.isoRightDerivedObj (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).inv) ∧
      (∀ (M : SheafOfModules.{u} R)
        (hM : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
          IsZero (((SheafOfModules.toSheaf R ⋙
            sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
              (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (S.W p t))).rightDerived r).obj M))
        (hA : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
          IsZero (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (S.W p t))).rightDerived r).obj
              ((SheafOfModules.toSheaf R).obj M)))
        (q : ℕ)
        (eA : (S.cohomologyFunctor q).obj ((SheafOfModules.toSheaf R).obj M).obj ⟶
          ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj
              ((SheafOfModules.toSheaf R).obj M))
        (heA : S.IsNormalizedEdge
          (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u})
            (A := (SheafOfModules.toSheaf R).obj M) q eA),
        ∃! eM : (S.cohomologyFunctor q).obj ((SheafOfModules.toSheaf R).obj M).obj ⟶
          ((SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj M,
          S.IsNormalizedEdge
            (SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u})
              (A := M) q eM ∧ IsIso eM ∧ eM ≫ (c q).hom.app M = eA) := by
  sorry

end CategoryTheory
