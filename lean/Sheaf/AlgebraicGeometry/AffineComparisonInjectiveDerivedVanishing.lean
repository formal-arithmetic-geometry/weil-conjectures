/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.AlgebraicGeometry.AffineComparisonEtaleCechPresentation
import Sheaf.AlgebraicGeometry.AffineComparisonCategoricalCechSystem
import Sheaf.CategoryTheory.CategoricalInjectiveCechExactness
import Sheaf.CategoryTheory.CategoricalFiniteCechCriterion
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing

/-!
# Affine comparison vanishing for Grothendieck abelian coefficients

The categorical form of the finite Čech argument in Stacks Project, Tag 099U.
(blueprint: stage3-affine-comparison-injective-derived-vanishing)
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- On an affine scheme, the comparison pullback of an injective étale sheaf has zero
positive derived global sections, with Grothendieck abelian coefficients.
Source: Stacks Project, Tag 099U, finite Čech proof with exact filtered colimits.
(blueprint: stage3-affine-comparison-injective-derived-vanishing)

Proof: use affine ind-étale objects over X as a basis. Every cover has a finite refinement
in this basis, and the basis is closed under fibre products. To check positive Čech
vanishing for a finite basis cover, present each member as a directed limit of affine
étale schemes over the covered object. The product of the finitely many directed index
sets is directed, and each stage family covers, since points lift through the original
cover. Fibre products commute with these limits. The comparison section formula and
continuity of étale sections identify each term, compatibly with every face map, with
the filtered colimit of its stage terms. Finite products and homology commute with this
colimit because A is Grothendieck abelian.

It remains to check finite affine étale covers of a basis object U. Present U as a directed
limit of affine étale X-schemes. Finite presentation descends the finite cover to one
stage, and joint surjectivity holds on a cofinal tail. Its intersections are the base
changes of the stage intersections. Apply section continuity again, with its naturality
for the face maps: the Čech complex is the filtered colimit of the Čech complexes of I
on the original étale site of X. Injectivity of I makes these complexes exact in positive
degrees. Thus every finite basis cover has vanishing positive Čech cohomology. The Čech
vanishing criterion gives zero derived evaluation on basis objects; take the terminal
object X. The empty cover has a zero positive complex, so the empty affine scheme is
included. This argument uses injectivity only on X's étale site and only finite products;
it does not assume exact infinite products or injectivity after arbitrary scheme pullback.
-/
theorem isZero_rightDerived_globalSections_comparisonUpperStar_of_isAffine
    (X : Scheme.{u}) [IsAffine X]
    (I : Sheaf X.smallEtaleTopology A) [Injective I] (q : ℕ) :
    IsZero (((sheafToPresheaf (Scheme.ProEt.topology X) A ⋙
      (evaluation X.ProEtᵒᵖ A).obj (op (MorphismProperty.Over.mk ⊤ (𝟙 X)
        (MorphismProperty.id_mem _ X)))).rightDerived (q + 1)).obj
      ((comparisonUpperStar A X).obj I)) := by
  have : Injective I.obj := (sheafificationAdjunction X.smallEtaleTopology A).map_injective
    I inferInstance
  apply CategoryTheory.Sheaf.isZero_rightDerived_eval_of_finiteCech
    (fun V : X.ProEt ↦ proAffineEtale V.hom) _ ((comparisonUpperStar A X).obj I) _
    _ (Scheme.AffineProEt.ofEtale (𝟙 X)).prop q
  · intro V hV R hR
    obtain ⟨n, U, hU, hUR, hcover⟩ := affineProEt_finite_refinement X V hV R hR
    exact ⟨n, U, fun k y ↦ affineProEt_cechNerve X V hV U hU k y, hUR, hcover⟩
  · intro V hV n U hnerve hcover k
    obtain ⟨D, hD, hfilter, S, hS⟩ :=
      exists_affine_etale_cech_system X V hV U hnerve hcover
    exact S.categoricalOriginalExactAt I hS k (fun i ↦
      Presheaf.exactAt_categoricalCech_of_injective I.obj
        (fun b ↦ Over.mk (S.f i b)) k)

end AlgebraicGeometry.ProEtale
