/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.AlgebraicGeometry.SupportLongExact
public import Sheaf.AlgebraicGeometry.SupportSiteComparison
public import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.PurityComparisonUnitInjectiveModel
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Site-comparison compatibility of the support boundary

Source: Stacks Project, `etale-cohomology.tex`, Tag 09XP, label
`section-cohomology-support`, with the etale/pro-etale refinement in the blueprint
(blueprint: lem-pur-support-comparison-boundary).

The statement records the two support long exact sequences and their canonical
adjunction-unit comparison ladder.  The boundary maps are normalized by the
snake boundary on every bounded-below injective model, so the sign convention is
part of the statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The adjunction-unit comparison on sections over any etale object of `T`.
Source: blueprint comparison-global-cohomology and comparison-pullback clauses;
(blueprint: lem-pur-support-comparison-boundary).
Proof: evaluate the actual comparison adjunction unit at the chosen etale object;
naturality is the componentwise unit naturality equation. -/
noncomputable def finiteComparisonSectionUnit (T : Scheme.{u}) (A : Type (u + 1)) [Ring A]
    (V : Scheme.Etale T) :
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op V)) ⋙ 𝟭 (ModuleCat.{u + 1} A) ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
          (evaluation _ _).obj (op ((Scheme.toProEt T).obj V))) where
  app F := ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F).hom.app
    (op V)
  naturality F G f := by
    exact congrArg (fun t ↦ t.hom.app (op V))
      ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.naturality f)

/-- The canonical derived comparison on sections over an arbitrary etale object.
At the terminal object this is the same unit-normalized map as
`finiteComparisonGlobalSections`; at an open complement it is the comparison map
used in the boundary ladder.
Source: blueprint comparison-global-cohomology and comparison-pullback clauses;
(blueprint: lem-pur-support-comparison-boundary).
Proof: apply right-derived-plus base change to `finiteComparisonSectionUnit`; the
comparison pullback coherence identifies its pro-etale target with the restriction
of the comparison on the open complement. -/
noncomputable def finiteComparisonSection (T : Scheme.{u}) (A : Type (u + 1)) [Ring A]
    (V : Scheme.Etale T) :
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op V)).rightDerivedFunctorPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
          (evaluation _ _).obj (op ((Scheme.toProEt T).obj V))).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
      (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op V))
      (G' := sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op ((Scheme.toProEt T).obj V)))
      (β := comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (γ := 𝟭 (ModuleCat.{u + 1} A)) (finiteComparisonSectionUnit T A V)

/-- The canonical comparison on supported hypercohomology in each integer degree.
Source: blueprint comparison map clause
(blueprint: lem-pur-support-comparison-boundary).
Proof: whisker the unit-normalized derived support comparison by the canonical
integer homology functor. -/
noncomputable def supportComparisonHypercohomology (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (q : ℤ) :
    Sheaf.supportHypercohomologyFunctor T.smallEtaleTopology
        (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) q ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        Sheaf.supportHypercohomologyFunctor (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i) q :=
  by
    simpa [Sheaf.supportHypercohomologyFunctor, etaleSupportKernel, supportSections] using
      (Functor.whiskerRight (supportComparison A i)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q) ≫
        (Functor.associator
          (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus
          (supportSections i A).rightDerivedFunctorPlus
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q)).hom)

/-- The canonical degreewise comparison on sections over an etale object.
Source: blueprint comparison-map clauses
(blueprint: lem-pur-support-comparison-boundary).
Proof: whisker `finiteComparisonSection` by integer homology and reassociate the
composite functors.  For the terminal object this is the unit-normalized global
comparison of `finiteComparisonGlobalSections`; for an open object the pullback
coherence identifies the target with the restriction comparison. -/
noncomputable def finiteComparisonSectionHypercohomology
    (T : Scheme.{u}) (A : Type (u + 1)) [Ring A] (V : Scheme.Etale T) (q : ℤ) :
    Sheaf.sectionHypercohomologyFunctor T.smallEtaleTopology
        (ModuleCat.{u + 1} A) V q ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} A) ((Scheme.toProEt T).obj V) q :=
  by
    simpa [Sheaf.sectionHypercohomologyFunctor] using
      (Functor.whiskerRight (finiteComparisonSection T A V)
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q) ≫
        (Functor.associator
          (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus
          ((sheafToPresheaf (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) ⋙
            (evaluation _ _).obj (op ((Scheme.toProEt T).obj V))).rightDerivedFunctorPlus)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q)).hom)


/-- The degreewise map of the recorded, unit-induced global comparison.
Source: global comparison clause of the blueprint
(blueprint: lem-pur-support-comparison-boundary). -/
noncomputable def finiteComparisonGlobalHypercohomology
    (T : Scheme.{u}) (A : Type (u + 1)) [Ring A] (q : ℤ) :
    Sheaf.sectionHypercohomologyFunctor T.smallEtaleTopology
        (ModuleCat.{u + 1} A) (Scheme.Etale.mk (𝟙 T)) q ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} A) (Scheme.ProEt.mk (𝟙 T)) q :=
  Functor.whiskerRight
    ((Functor.rightUnitor _).inv ≫
      (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
        (ModuleCat.{u + 1} A))).inv ≫ finiteComparisonGlobalSections T A)
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q) ≫
      (Functor.associator _ _ _).hom

/-- The coefficient identification on the open complement, using exactly the
unit-normalized isomorphism whose coherence is
`supportSiteComparison_pullback_coherent`, transported to the actual restriction functors.
Source: comparison-pullback clause of the blueprint
(blueprint: lem-pur-support-comparison-boundary). -/
noncomputable def supportBoundaryOpenCoefficientIso
    (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] :
    Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) U ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j :=
  Functor.isoWhiskerRight
    (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm
    (comparisonUpperStar (ModuleCat.{u + 1} A) U) ≪≫
  supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j ≪≫
  Functor.isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) T)
    (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)

/-- Unit normalization on the open, ensuring that evaluation of the unit on `T`
over the open object is the unit on the restricted sheaf on `U`, with the specified
coefficient identification. Deriving evaluation of this equation gives the open
comparison `finiteComparisonSectionHypercohomology` in the localization ladder.
Source: comparison-pullback and open-global-comparison clauses of the blueprint
(blueprint: lem-pur-support-comparison-boundary). -/
def SupportBoundaryOpenUnitNormalized
    (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] : Prop :=
  ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map
        ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F) =
      (comparisonAdjunction (ModuleCat.{u + 1} A) U).unit.app
          ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj F) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) U).map
          ((supportBoundaryOpenCoefficientIso A j).hom.app F)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

/-- A support boundary is the snake boundary on each injective section complex,
transported through the canonical right-derived comparison maps.
Source: Stacks Project Tag 09XP and (blueprint: lem-pur-support-comparison-boundary).
Proof: for an injective complex, the kernel-inclusion and restriction maps form a
short exact complex; its `ShortExact.δ` is the snake boundary. -/
def supportBoundaryNormalization {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [CommRing A]
    {V W : C} (j : W ⟶ V)
    (δ : Sheaf.SupportSequenceBoundary J (ModuleCat.{u + 1} A) j ⊤) : Prop :=
  ∀ (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
    [∀ r : ℤ, Injective (I.obj.X r)],
    ∃ (w :
        (NatTrans.mapHomologicalComplex
          (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j)
          (ComplexShape.up ℤ)).app I.obj ≫
        (NatTrans.mapHomologicalComplex
          ((sheafSections J (ModuleCat.{u + 1} A)).map j.op)
          (ComplexShape.up ℤ)).app I.obj = 0)
      (hS : (ShortComplex.mk _ _ w).ShortExact),
      ∀ q : ℤ,
        Sheaf.supportSequenceModelBoundary J (ModuleCat.{u + 1} A) j ⊤ δ I
          ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ (Iso.refl _) q =
          hS.δ q (q + 1) rfl

/-- Canonical etale/pro-etale support comparison preserves the normalized boundary.
Source: Stacks Project Tag 09XP and (blueprint: lem-pur-support-comparison-boundary).

Proof (the six steps of the node):

1. Work in a common universe in which both sites are small. Their ordinary $A$-module categories
are Grothendieck abelian by [prop-pur-kinjective-resolutions-exist], hence have enough injectives
by [lem-sp-grothendieck-enough-injectives]. Apply
[lem-sc-bounded-below-injective-resolution-existence] to choose a bounded-below injective module
resolution $F_p\to J^\bullet$. The module adjunction is [def-weil-pbc-site-comparison-morphism],
and its inverse image is exact by [lem-sf-comparison-pullback-exact]. Consequently
[lem-sp-right-adjoint-preserves-injectives] shows that $I^\bullet=\nu_{T,*}J^\bullet$ is bounded
below and termwise injective on the etale site. This uses preservation of injectives by direct
image, rather than an assertion that inverse image preserves injectives.

2. Let $a:F\to I^\bullet$ be the ordinary comparison unit followed by $\nu_{T,*}(F_p\to
J^\bullet)$. By the injective computation of right derived functors
[lem-weil-pbc-right-derived-plus-injective], $I^\bullet$ represents $R\nu_{T,*}F_p$, and by
[lem-pur-comparison-unit-injective-model], applied to $M=F$ in degree zero and the resolution
$F_p\to J^\bullet$, $a$ represents the derived adjunction unit under this identification. That
unit is an isomorphism by [thm-weil-pbc-site-comparison], with no constructibility hypothesis.
Thus $a$ is a quasi-isomorphism and is a specified etale injective resolution of $F$. The
direct-image formula [def-weil-pbc-site-comparison-morphism] gives $I^r(T)=J^r(T)$ and
$I^r(V)=J^r(V)$, with identical restriction maps and differentials. Taking kernels gives
$\Gamma_C(T_{\mathrm{et}},I^\bullet)=\Gamma_C(T_{\mathrm{proet}},J^\bullet)$, using
[def-pur-support-cohomology].

3. For completeness the degreewise surjectivity needed for localization also holds for module
injectives. For an injective module sheaf $E$,
[lem-weil-pbc-ringed-site-injective-module-injective-presheaf] makes its underlying module
presheaf injective. For the monomorphism $j:V\to T$, the map of free presheaves $A[h_V]\to A[h_T]$
is injective: on each object its basis map is the injection
$\operatorname{Hom}(-,V)\to\operatorname{Hom}(-,T)$. By the definition of injectivity
[def-sp-injective-resolutions], restriction of Hom into $E$ is surjective. The free-presheaf
Yoneda formula [lem-weil-pbc-free-yoneda-presheaf-module] identifies this with $E(T)\to E(V)$.
Therefore in either topology the three complexes $\ker(E^\bullet(T)\to E^\bullet(V))$,
$E^\bullet(T)$, $E^\bullet(V)$ form a degreewise short exact sequence when $E^\bullet$ is
$I^\bullet$ or $J^\bullet$. The kernel and both arrows respect the $A$-actions.

4. The support complex in each row computes the right-derived kernel functor of
[def-pur-support-cohomology], with the ordinary module-coefficient interpretation of
[lem-pur-support-site-comparison]; the middle complex computes global sections. The restrictions
$I^\bullet|_V$ and $J^\bullet|_V$ are injective resolutions on their respective sites by
[lem-weil-pbc-etale-restriction-injectives] and [lem-weil-pbc-proetale-restriction-injectives].
Thus the last complexes compute cohomology on $V$. These are precisely the injective localization
models for the long exact sequences of [thm-pur-with-support-exactness]. The finiteness of $A$
makes every coefficient sheaf torsion, and the hypotheses of the pro-etale clause hold. No
finiteness of the modules of sections is needed.

5. The equalities in Step 2 identify the two short exact sequences of Step 3 term by term,
including their inclusions and restriction arrows. They therefore give a morphism of short exact
cochain complexes. Its support component represents the canonical supported comparison of
[lem-pur-support-site-comparison]: first apply the etale derived support functor to the unit $F\to
R\nu_{T,*}F_p$, represented by the augmentation $a$, and then use the kernel identity of Step 2.
In the specified resolution $a:F\to I^\bullet$, the first operation is represented by the identity
on the support complex of $I^\bullet$. The middle component is the global comparison of
[lem-weil-pbc-comparison-global-cohomology] by the same unit computation. On $V$ it is the global
comparison for $j^{-1}F$: restriction of $a$ is the adjunction unit there, since the direct-image
restrictions are the same maps $J(T)\to J(V)$. The coefficient identification is the canonical
$j^{-1}F_p\cong\nu_V^*(j^{-1}F)$ of [lem-weil-pbc-comparison-pullback]. Thus the three cohomology
maps are exactly the specified $c_C^q,c_T^q,c_V^q$, rather than unspecified isomorphisms of their
groups.

6. Apply [lem-weil-pbc-complex-ses-long-exact-naturality] to this morphism of short exact
complexes. The result is a morphism of the full long exact sequences, with
$c_C^{q+1}\partial_{\mathrm{et}}^q=\partial_{\mathrm{pro}}^q c_V^q$. To see the sign explicitly, a
cocycle on $V$ is lifted to a cochain on $T$, its differential lies in the support kernel, and the
class of this differential is the connecting image. The termwise identifications send the chosen
lift and its differential to the same cochains in the other row. Both boundaries therefore give
the same class, with no negation. Naturality of the comparisons in
[lem-pur-support-site-comparison] and [lem-weil-pbc-comparison-global-cohomology], and coefficient
functoriality of [thm-pur-with-support-exactness], give naturality of all these squares in $F$.
All complexes and their arrows are $A$-linear, so their induced cohomology and connecting maps are
$A$-linear as well. -/
theorem exists_support_comparison_boundary
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    (C : Scheme.{u}) (i : C ⟶ T) [IsClosedImmersion i] :
    ∃ (δₑ : Sheaf.SupportSequenceBoundary T.smallEtaleTopology
        (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) ⊤)
      (δₚ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i) ⊤),
      ProEtale.SupportBoundaryOpenUnitNormalized A i.openComplement.ι ∧
      supportBoundaryNormalization T.smallEtaleTopology A
        (Etale.supportRestrictionArrow i) δₑ ∧
      supportBoundaryNormalization (Scheme.ProEt.topology T) A
        (ProEtale.supportRestrictionArrow i) δₚ ∧
      Sheaf.SupportSequenceExact T.smallEtaleTopology (ModuleCat.{u + 1} A)
        (Etale.supportRestrictionArrow i) ⊤ δₑ ∧
      Sheaf.SupportSequenceExact (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)
        (ProEtale.supportRestrictionArrow i) ⊤ δₚ ∧
      (∀ (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (δₑ q).app ⟨(DerivedCategory.Plus.singleFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F, trivial⟩ ≫
            (ProEtale.supportComparisonHypercohomology A i (q + 1)).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) =
          (ProEtale.finiteComparisonSectionHypercohomology T A
              (Scheme.Etale.mk i.openComplement.ι) q).app
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
            (δₚ q).app ⟨(DerivedCategory.Plus.singleFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
              (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).obj F,
              trivial⟩) ∧
      (∀ (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (Sheaf.supportHypercohomologyInclusion T.smallEtaleTopology
            (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) q).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
            (ProEtale.finiteComparisonGlobalHypercohomology T A q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) =
          (ProEtale.supportComparisonHypercohomology A i q).app
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
        (Sheaf.supportHypercohomologyInclusion (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i) q).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).obj F)) ∧
      (∀ (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (Sheaf.sectionHypercohomologyRestriction T.smallEtaleTopology
            (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) q).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
            (ProEtale.finiteComparisonSectionHypercohomology T A
              (Scheme.Etale.mk i.openComplement.ι) q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) =
          (ProEtale.finiteComparisonGlobalHypercohomology T A q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
        (Sheaf.sectionHypercohomologyRestriction (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i) q).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).obj F)) ∧
      (∀ (q : ℤ) (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
          (f : F ⟶ G),
        (Sheaf.supportHypercohomologyFunctor T.smallEtaleTopology
            (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) q).map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map f) ≫
            (ProEtale.supportComparisonHypercohomology A i q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj G) =
          (ProEtale.supportComparisonHypercohomology A i q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
        (Sheaf.supportHypercohomologyFunctor (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) (ProEtale.supportRestrictionArrow i) q).map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).map f)) ∧
      (∀ (q : ℤ) (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
          (f : F ⟶ G),
        (Sheaf.sectionHypercohomologyFunctor T.smallEtaleTopology
            (ModuleCat.{u + 1} A) (Scheme.Etale.mk (𝟙 T)) q).map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map f) ≫
            (ProEtale.finiteComparisonGlobalHypercohomology T A q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj G) =
          (ProEtale.finiteComparisonGlobalHypercohomology T A q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
        (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) (Scheme.ProEt.mk (𝟙 T)) q).map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
            (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).map f)) ∧
      (∀ (q : ℤ) (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
          (f : F ⟶ G),
        (Sheaf.sectionHypercohomologyFunctor T.smallEtaleTopology
            (ModuleCat.{u + 1} A) (Scheme.Etale.mk i.openComplement.ι) q).map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map f) ≫
            (ProEtale.finiteComparisonSectionHypercohomology T A
              (Scheme.Etale.mk i.openComplement.ι) q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj G) =
          (ProEtale.finiteComparisonSectionHypercohomology T A
              (Scheme.Etale.mk i.openComplement.ι) q).app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F) ≫
        (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} A) (Scheme.ProEt.mk i.openComplement.ι) q).map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0 ⋙
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus).map f)) := by
  sorry

end AlgebraicGeometry
