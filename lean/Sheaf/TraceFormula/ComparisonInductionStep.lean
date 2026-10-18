/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Induction for comparison of two site topologies

Source: Stacks Project, Tags 0EZ3, 0EZE and 0EZF
(blueprint: lem-trf-comparison-induction-step).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CategoryTheory.RefinedTopologyComparison

/-- Abelian sheafification in the small-site universe. Source: Stacks Project,
Tag 00W1 (blueprint: lem-trf-comparison-induction-step).
This is the existing Grothendieck-abelian sheafification construction. -/
instance abelianSheafify {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian J _

/-- Direct images of geometric morphisms on abelian categories are additive,
as right adjoints. Source: Stacks Project, section-compare
(blueprint: lem-trf-comparison-induction-step). -/
instance geometricDirectAdditive {A : Type v} {B : Type w}
    [Category.{u} A] [Category.{u} B] [Abelian A] [Abelian B]
    (e : GeometricMorphism A B) : e.direct.Additive :=
  have := e.adj.isRightAdjoint
  Functor.additive_of_preserves_binary_products e.direct

/-- Relocalization along an arrow, with inverse image given by precomposition
with `Over.map f` and direct image by its right Kan extension. No global pullback
hypothesis is needed. Source: Stacks Project, section-compare-general and Sites, Tag 03EH
(blueprint: lem-trf-comparison-induction-step). -/
def relocalization {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {X Y : C} (f : X ⟶ Y) :
    GeometricMorphism (Sheaf (J.over X) AddCommGrpCat.{u})
      (Sheaf (J.over Y) AddCommGrpCat.{u}) where
  inverse := J.overMapPullback AddCommGrpCat.{u} f
  direct := (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u} (J.over X) (J.over Y)
  adj := (Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{u} (J.over X) (J.over Y)
  leftExact := inferInstance

/-- The inclusion from finer sheaves to coarser sheaves, with unchanged underlying
presheaf. Source: Stacks Project, section-compare
(blueprint: lem-trf-comparison-induction-step). -/
def comparisonDirect {C : Type u} [SmallCategory C]
    (J K : GrothendieckTopology C) (h : K ≤ J) :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u} :=
  ObjectProperty.ιOfLE (fun _ hF ↦ hF.of_le h)

/-- The canonical comparison: inclusion on underlying presheaves and finer
sheafification as inverse image. Its adjunction is the restriction of the usual
sheafification adjunction. Source: Stacks Project, section-compare
(blueprint: lem-trf-comparison-induction-step). -/
def comparison {C : Type u} [SmallCategory C]
    (J K : GrothendieckTopology C) (h : K ≤ J) :
    GeometricMorphism (Sheaf J AddCommGrpCat.{u}) (Sheaf K AddCommGrpCat.{u}) where
  inverse := sheafToPresheaf K AddCommGrpCat.{u} ⋙ presheafToSheaf J AddCommGrpCat.{u}
  direct := comparisonDirect J K h
  adj := (sheafificationAdjunction J AddCommGrpCat.{u}).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf K AddCommGrpCat.{u})
    (Functor.FullyFaithful.ofFullyFaithful (𝟭 (Sheaf J AddCommGrpCat.{u})))
    (Iso.refl _) (Iso.refl _)
  leftExact := inferInstance

/-- The comparison on slice sites: coverings in each slice are detected on
underlying objects. Source: Stacks Project, section-compare-general
(blueprint: lem-trf-comparison-induction-step). -/
def sliceComparison {C : Type u} [SmallCategory C]
    (τ τ' : Precoverage C) (h : τ' ≤ τ) (X : C) :
    GeometricMorphism (Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u})
      (Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}) :=
  comparison (τ.toGrothendieck.over X) (τ'.toGrothendieck.over X)
    (fun _ _ hS ↦ Precoverage.toGrothendieck_mono h _ hS)

/-- The implication (V_r) → (V_{r+1}) in the canonical slice-site situation.
Source: Stacks Project, Tag 0EZE, lemma-induction-step-V-C-general, with the five
hypotheses of Tag 0EZ3 (blueprint: lem-trf-comparison-induction-step).

The comparison and relocalization functors are the constructions above. In particular,
no arbitrary geometric morphisms, comparison isomorphisms, or derived functors are inputs.
The essential image defining A_X is written out in both the induction hypothesis and
conclusion. The conclusion includes the previously known degrees as well as degree r + 1.

Proof, following the DAG and source:
1. Fix $r\geq0$ and assume $(V_r)$. If $F\in\mathcal A_Y$, choose $F'\in\mathcal A'_Y$ with
$F=\epsilon_Y^{-1}F'$. Since $F'$ already is a $\tau$-sheaf, sheafification fixes it and
$\epsilon_{Y,*}F=F'$. For $g:Z\to Y$, the presheaf underlying $g_{\tau'}^{-1}F'$ is its
sectionwise restriction. By assumption (2) this restriction is in $\mathcal A'_Z$, hence already a
$\tau$-sheaf by (3). Consequently $g_\tau^{-1}F=\epsilon_Z^{-1}g_{\tau'}^{-1}F'\in\mathcal A_Z$
and $\epsilon_{Z,*}g_\tau^{-1}F=g_{\tau'}^{-1}\epsilon_{Y,*}F$. The comparison inverse image is
exact because it is abelian sheafification.

2. For $F\in\mathcal A_Y$, the sheaf $R^{r+1}\epsilon_{Y,*}F$ is the $\tau'$-sheafification of
$U\mapsto H^{r+1}_\tau(U,F)$. The localization isomorphism identifies this with cohomology on the
slice over $U$ with coefficient $F|_U\in\mathcal A_U$ from Step 1. Thus it suffices to show that
every such class becomes zero on a $\tau'$-cover of $U$: any map from a locally zero presheaf to a
sheaf is zero by sheaf separation; the sheafification adjunction then forces its sheafification to
be zero. We may rename $U$ as $Y$ and $F|_U$ as $F$; further $\tau'$-cover replacements can be
composed.

3. Every positive-degree cohomology class on either slice site is locally zero. Indeed, represent
it by a cocycle $s\in I^q(U)$ in an injective resolution of its sheaf, $q>0$. Exactness of the
resolution makes $I^{q-1}\to\ker(d^q)$ an epimorphism. Kernels are sectionwise; local surjectivity
supplies a covering and sections $t_i$ with $d t_i=s|_{U_i}$, so the restricted classes vanish.
Apply this with $q=r+1$ to $\xi\in H^{r+1}_\tau(Y,F)$, obtaining a $\tau$-cover killing $\xi$.

4. Refine that cover as in assumption (5): $V_j\to Y$ is a $\tau'$-cover, $f_j:W_j\to V_j$ lies in
$\mathcal P$ and is a singleton $\tau$-cover, and $W_{jk}\to W_j$ is a $\tau'$-cover. Each
composite $W_{jk}\to Y$ factors through an original member, so $\xi|_{W_{jk}}=0$. By Step 2 it is
enough to work over one $V_j$. Rename it $Y$, rename $W_j$ as $T$, and write $f:T\to Y$. The
resulting problem has $F\in\mathcal A_Y$, $f\in\mathcal P$ a singleton $\tau$-cover, and $\xi|_T$
killed by a $\tau'$-cover of $T$.

5. The next-degree comparison gives a unique $\theta\in
H^{r+1}_{\tau'}(T,\epsilon_{T,*}f_\tau^{-1}F)$ mapping to $\xi|_T$. On $T\times_YT$, the images of
the two pullbacks of $\theta$ are equal: both are the pullback of $\xi$ along the same composite
to $Y$. Restriction naturality and injectivity of that same comparison on $T\times_YT$ therefore
give $\operatorname{pr}_1^*\theta=\operatorname{pr}_2^*\theta$. This fibre product exists by (1),
and its restricted coefficient lies in the required class by Step 1.

6. Put $F'=\epsilon_{Y,*}F\in\mathcal A'_Y$; Step 1 identifies the coefficient of $\theta$ with
$F'|_T$. The equalizer-class lemma, with $q=r+1\geq1$, supplies a $\tau'$-cover $Y_a\to Y$ on
which $\theta$ becomes zero on $T\times_YY_a$. Its comparison image is the restriction of $\xi$
there. The base changed $f$ remains in $\mathcal P$ by (1) and remains a singleton $\tau$-cover by
the site axiom. After this allowed replacement we have reduced to $\xi|_T=0$.

7. Let $E=f_\tau^{-1}F$ and $D=Rf_{\tau,*}E$. Derived composition gives
$R\Gamma_\tau(Y,D)=R\Gamma_\tau(T,E)$ and identifies the map induced by the adjunction unit $F\to
D$ with cohomology restriction along $f$. Indeed at the underived level both maps send a section
to its restriction to the slice over $T$, and the canonical resolution comparison in the
composition theorem derives that same map. Thus $\xi$ maps to zero in $H^{r+1}_\tau(Y,D)$. Here
abelian sheaves are constant-$\mathbb Z$ modules with their unique integer action; apply the
ringed-topos composition theorem with these constant ring sheaves and the map to the punctual
topos.

8. Set $D_{\leq r}=\tau_{\leq r}D$ and $Q=\tau_{\geq r+1}D$. The standard truncation triangle is
$D_{\leq r}\to D\to Q\to$. Represent $Q$ by a complex zero below $r+1$, resolve it by injectives
zero below the same bound, and compute derived sections on that resolution. The resulting section
complex is zero below $r+1$, so $H^r_\tau(Y,Q)=0$. The long exact sequence of the truncation
triangle therefore makes $H^{r+1}_\tau(Y,D_{\leq r})\to H^{r+1}_\tau(Y,D)$ injective. The unit
$F\to D$ factors through $D_{\leq r}$ by t-structure orthogonality, since $F$ is in degree zero
and $r\geq0$. Consequently $\xi$ maps to zero already in $H^{r+1}_\tau(Y,D_{\leq r})$.

9. Put $D'=Rf_{\tau',*}f_{\tau'}^{-1}F'$ and $K=\tau_{\leq r}D'$. By Step 1,
$f_{\tau'}^{-1}F'=\epsilon_{T,*}E$. Use the adjoint comparison $b_E:\epsilon_Y^{-1}D'\to D$
specified by the truncated-direct-image lemma. Exactness of $\epsilon_Y^{-1}$ makes its cohomology
map in degree $i\leq r$ the $\tau$-sheafification of that lemma's canonical isomorphism
$R^if_{\tau',*}\epsilon_{T,*}E\to\epsilon_{Y,*}R^if_{\tau,*}E$. Sheafification of the right-hand
side is $R^if_{\tau,*}E$. Hence truncating $b_E$ gives an isomorphism
$\beta:\epsilon_Y^{-1}K\xrightarrow{\sim}D_{\leq r}$, including negative degrees, where both sides
vanish.

10. The augmentation $u':F'\to K$ is the factorization through $\tau_{\leq r}$ of the derived unit
for $f_{\tau'}$. Under $\epsilon_Y^{-1}F'=F$, the composite $\beta\circ\epsilon_Y^{-1}u'$ is the
factored unit $F\to D_{\leq r}$ of Step 8. To check the map, before truncating compose $F'\to
Rf_{\tau',*}f_{\tau'}^{-1}F'$ with $a_E$ from the comparison lemma. The composite is $F'\to
R\epsilon_{Y,*}F\to R\epsilon_{Y,*}D$: both are the unit for the composite adjunction, since
$\epsilon_{T,*}f_\tau^{-1}F=f_{\tau'}^{-1}\epsilon_{Y,*}F$. Taking the $\epsilon_Y$ adjoint
cancels its unit and counit and yields the unit for $f_\tau$. Functorial truncation preserves this
equality.

11. Choose the cone triangle $F'\xrightarrow{u'}K\to L\to F'[1]$. The degree-zero map is $F'\to
f_{\tau',*}f_{\tau'}^{-1}F'$, which on an object $U\to Y$ is restriction $F'(U)\to
F'(U\times_YT)$. It is injective since $F'$ is a $\tau$-sheaf and $U\times_YT\to U$ is a singleton
$\tau$-cover. From the triangle's cohomology sequence, $L$ has cohomology only in $[0,r]$, with
$\mathcal H^0(L)=\operatorname{coker}(F'\to f_{\tau',*}f_{\tau'}^{-1}F')$ and $\mathcal
H^i(L)=R^if_{\tau',*}f_{\tau'}^{-1}F'$ for $1\leq i\leq r$. Assumptions (2),(4) and weak Serre
closure under cokernels put all these sheaves in $\mathcal A'_Y$. This includes $r=0$.

12. Pull back the cone triangle by exact $\epsilon_Y^{-1}$, using $\beta$ and the augmentation
equality in Step 10. This gives $F\to D_{\leq r}\to\epsilon_Y^{-1}L\to F[1]$. Derived sections
preserve distinguished triangles, so exactness and Step 8 provide $\xi'\in
H^r_\tau(Y,\epsilon_Y^{-1}L)$ whose boundary is $\xi$. The truncated-cohomology comparison applies
to $L$ by Step 11, and lifts $\xi'$ to $\eta\in H^r_{\tau'}(Y,L)$.

13. Let $\zeta=\partial\eta\in H^{r+1}_{\tau'}(Y,F')$. Naturality of the long exact sequence, for
the comparison from the original cone triangle to its pulled-back triangle followed by derived
sections, gives $\epsilon_Y^*(\partial\eta)=\partial(\epsilon_Y^*\eta)=\partial\xi'=\xi$. This
uses the actual canonical comparison from Step 12; an arbitrary isomorphism of groups would not
suffice. By the positive-degree local-vanishing argument in Step 3, $\zeta$ is killed by a
$\tau'$-cover. Restricting its comparison image shows that $\xi$ is killed by the same cover.
Composing all earlier $\tau'$-covers proves the local assertion in Step 2. Thus
$R^{r+1}\epsilon_{Y,*}F=0$; together with $(V_r)$ this is $(V_{r+1})$.
-/
theorem comparisonInductionStep
    {C : Type u} [SmallCategory C]
    (τ τ' : Precoverage C)
    (hτsite : τ.IsSiteForCoverings) (hτ'site : τ'.IsSiteForCoverings)
    (hτ : τ' ≤ τ)
    (P : ∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop)
    (A' : ∀ X : C, Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u} → Prop)
    (hzero : ∀ X : C, A' X 0)
    (hiso : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}),
      Nonempty (H ≅ K) → A' X H → A' X K)
    (hkernel : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})
      (f : H ⟶ K), A' X H → A' X K → A' X (kernel f))
    (hcokernel : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})
      (f : H ⟶ K), A' X H → A' X K → A' X (cokernel f))
    (hextension : ∀ (X : C)
      (S : ShortComplex (Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})),
      S.ShortExact → A' X S.X₁ → A' X S.X₃ → A' X S.X₂)
    (hbaseChange : ∀ (X Y Y' : C) (f : X ⟶ Y), P f → ∀ g : Y' ⟶ Y,
      ∃ h : HasPullback f g, letI := h; P (pullback.snd f g))
    (hrelocalization : ∀ (X Y : C) (f : X ⟶ Y)
      (H : Sheaf (τ'.toGrothendieck.over Y) AddCommGrpCat.{u}),
      A' Y H → A' X ((relocalization τ'.toGrothendieck f).inverse.obj H))
    (htauSheaf : ∀ (X : C) (H : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}),
      A' X H → Presheaf.IsSheaf (τ.toGrothendieck.over X) H.obj)
    (hderivedImage : ∀ (X Y : C) (f : X ⟶ Y), P f →
      ∀ (H : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}), A' X H →
        ∀ i : ℕ, A' Y (((relocalization τ'.toGrothendieck f).direct.rightDerived i).obj H))
    (hrefinement : ∀ (U : C) (I : Type u) (U₀ : I → C) (a : ∀ i : I, U₀ i ⟶ U),
      Presieve.ofArrows U₀ a ∈ τ U →
      ∃ (J : Type u) (V W : J → C) (v : ∀ j : J, V j ⟶ U) (w : ∀ j : J, W j ⟶ V j)
        (K : J → Type u) (Z : ∀ j : J, K j → C) (z : ∀ (j : J) (k : K j), Z j k ⟶ W j),
        Presieve.ofArrows V v ∈ τ' U ∧
        (∀ j : J, Presieve.singleton (w j) ∈ τ (V j) ∧ P (w j)) ∧
        (∀ j : J, Presieve.ofArrows (Z j) (z j) ∈ τ' (W j)) ∧
        ∀ (j : J) (k : K j), ∃ (i : I) (b : Z j k ⟶ U₀ i),
          z j k ≫ w j ≫ v j = b ≫ a i)
    (r : ℕ)
    (hr : ∀ (X : C) (H : Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u}),
      (∃ H' : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u},
        A' X H' ∧ Nonempty (H ≅ (sliceComparison τ τ' hτ X).inverse.obj H')) →
      ∀ i : ℕ, 1 ≤ i → i ≤ r →
        IsZero (((sliceComparison τ τ' hτ X).direct.rightDerived i).obj H)) :
    ∀ (X : C) (H : Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u}),
      (∃ H' : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u},
        A' X H' ∧ Nonempty (H ≅ (sliceComparison τ τ' hτ X).inverse.obj H')) →
      ∀ i : ℕ, 1 ≤ i → i ≤ r + 1 →
        IsZero (((sliceComparison τ τ' hτ X).direct.rightDerived i).obj H) := by
  sorry

end CategoryTheory.RefinedTopologyComparison
