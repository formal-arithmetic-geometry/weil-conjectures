/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.TraceFormula.ComparisonInductionStep
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Local killing of an equalizer cohomology class

Source: Stacks Project, `sites-cohomology.tex`, Tag 0EZD, lemma-make-class-zero-general;
comparison/naturality conventions from section-compare-general
(blueprint: lem-trf-comparison-equalizer-class-killing).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CategoryTheory.RefinedTopologyComparison

/-- A positive cohomology class equalized on the fibre square is locally zero.

Source: Stacks Project, Tag 0EZD, lemma-make-class-zero-general
(blueprint: lem-trf-comparison-equalizer-class-killing).

Proof, following the DAG node and the source:
1. Work on $\mathcal D=\mathcal C_{\tau'}/Y$. By localization of object cohomology,
$H^q_{\tau'}(T,H'|_T)=H^q(T,H')$ for every $T\to Y$, naturally in arrows over $Y$; so all
pullbacks below are restriction maps of the cohomology presheaf of `H'` on this one site, which is
how the classes and maps in the statement are written.
2. The base change functor $V\mapsto V\times_YX$ (products exist by (1)) is continuous and presents
the relocalization $f_{\tau'}$; its direct image is $(f_{\tau',*}K)(V)=K(V\times_YX\to X)$.
3. Put $\mathcal G'=R^qf_{\tau',*}(H'|_X)$ and $P(V)=H^q(V\times_YX,H')$. The higher-direct-image
theorem identifies $\mathcal G'$ with the $\tau'$-sheafification of $P$; write
$e_V:P(V)\to\mathcal G'(V)$ for the natural canonical map and $\overline\theta=e_Y(\theta)$.
4. Applied to the identity of $\mathcal D$, the same theorem sheafifies $Q(V)=H^q(V,H')$ to
$R^q\mathrm{id}_*H'=0$ as $q\geq1$; local equality in sheafification gives a $\tau'$-covering
$\{W_k\to X\}$ with $\theta|_{W_k}=0$.
5. Naturality of $e$ gives $\overline\theta|_X=e_X(\operatorname{pr}_2^*\theta)$, hence
$=e_X(\operatorname{pr}_1^*\theta)$ by the equalizer hypothesis `heq`; and
$\operatorname{pr}_1^*\theta$ restricts to zero in $P(W_k)$ by Step 4.
6. The sheaf $\mathcal G'$ is separated for $\{W_k\to X\}$, so $\overline\theta|_X=0$.
7. By (2) $H'|_X\in\mathcal A'_X$, by (4) $\mathcal G'\in\mathcal A'_Y$, and by (3) $\mathcal G'$
is a $\tau$-sheaf; the singleton $\tau$-covering $\{X\to Y\}$ makes
$\mathcal G'(Y)\to\mathcal G'(X)$ injective, so $\overline\theta=0$.
8. Since $e_Y(\theta)=e_Y(0)$ in $P^\#(Y)$, local equality in sheafification gives a
$\tau'$-covering $\{Y_j\to Y\}$ with $\theta|_{Y_j}=0$ in $P(Y_j)$, i.e. $\theta$ restricts
to zero in $H^q(Y_j\times_YX,H')$ along the first projection, as in the conclusion.
-/
theorem comparisonEqualizerClassKilling
    {C : Type u} [SmallCategory C]
    (τ τ' : Precoverage C)
    (hτsite : τ.IsSiteForCoverings) (hτ'site : τ'.IsSiteForCoverings)
    (hτ : τ' ≤ τ)
    (P : ∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop)
    (A' : ∀ X : C,
      Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u} → Prop)
    (hzero : ∀ X : C, A' X 0)
    (hiso : ∀ (X : C)
      (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}),
      Nonempty (H ≅ K) → A' X H → A' X K)
    (hkernel : ∀ (X : C)
      (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})
      (g : H ⟶ K), A' X H → A' X K → A' X (kernel g))
    (hcokernel : ∀ (X : C)
      (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})
      (g : H ⟶ K), A' X H → A' X K → A' X (cokernel g))
    (hextension : ∀ (X : C)
      (S : ShortComplex (Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})),
      S.ShortExact → A' X S.X₁ → A' X S.X₃ → A' X S.X₂)
    (hbaseChange : ∀ (X Y Y' : C) (f : X ⟶ Y), P f → ∀ g : Y' ⟶ Y,
      ∃ h : HasPullback f g, letI := h; P (pullback.snd f g))
    (hrelocalization : ∀ (X Y : C) (f : X ⟶ Y)
      (H : Sheaf (τ'.toGrothendieck.over Y) AddCommGrpCat.{u}),
      A' Y H → A' X ((relocalization τ'.toGrothendieck f).inverse.obj H))
    (htauSheaf : ∀ (X : C)
      (H : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}),
      A' X H → Presheaf.IsSheaf (τ.toGrothendieck.over X) H.obj)
    [hExt : ∀ X : C, HasExt (Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})]
    (hderivedImage : ∀ (X Y : C) (f : X ⟶ Y), P f →
      ∀ (H : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}), A' X H →
        ∀ i : ℕ,
          A' Y (((relocalization τ'.toGrothendieck f).direct.rightDerived i).obj H))
    {X Y : C} (f : X ⟶ Y) (hf : P f)
    (hsingle : Presieve.singleton f ∈ τ Y)
    (hff : HasPullback f f)
    (H' : Sheaf (τ'.toGrothendieck.over Y) AddCommGrpCat.{u})
    (hH' : A' Y H') (q : ℕ) (hq : 1 ≤ q)
    (θ : Sheaf.H' H' q (Over.mk f))
    (heq :
      ((H'.cohomologyPresheaf q).map
          (Over.homMk (@pullback.fst C _ X X Y f f hff) :
            Over.mk (@pullback.fst C _ X X Y f f hff ≫ f) ⟶ Over.mk f).op) θ =
        ((H'.cohomologyPresheaf q).map
          (Over.homMk (@pullback.snd C _ X X Y f f hff)
            (by simp [pullback.condition]) :
            Over.mk (@pullback.fst C _ X X Y f f hff ≫ f) ⟶ Over.mk f).op) θ) :
    ∃ (I : Type u) (Yj : I → C) (a : ∀ j, Yj j ⟶ Y),
      Presieve.ofArrows Yj a ∈ τ' Y ∧
        ∀ j, ∃ hj : HasPullback f (a j),
          ((H'.cohomologyPresheaf q).map
            (Over.homMk (@pullback.fst C _ X (Yj j) Y f (a j) hj) :
              Over.mk (@pullback.fst C _ X (Yj j) Y f (a j) hj ≫ f) ⟶ Over.mk f).op) θ = 0 := by
  sorry

end CategoryTheory.RefinedTopologyComparison
