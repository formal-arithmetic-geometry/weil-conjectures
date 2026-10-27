module

public import Sheaf.AlgebraicGeometry.StackFibreCohomology
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Limits

import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Higher stack images and sheafified fibre cohomology

Source: Stacks Project, stacks-sheaves.tex, Tag 075G, lemma-pushforward-restriction
(blueprint: lem-sfb-stack-higher-image-fibre-cohomology-presheaf).

The comparison is normalized on every injective resolution. The fibre identification
uses independently derived sections on the comma model of the scheme 2-base change.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Module sheafification on the target, using the recorded Mathlib construction.
Source: Stacks 075G (blueprint: lem-sfb-stack-higher-image-fibre-cohomology-presheaf). -/
abbrev moduliCohomologySheafification {S : AlgebraicGeometry.Scheme.{u}}
    (G : BasedCategory.{v, w} (Over S)) (hG : IsFibredInGroupoids G)
    (τ : ModuliCohomologyTopology) :
    PresheafOfModules.{max (u + 1) v w} (moduliCohomologyRings G hG τ).obj ⥤
      ModuliCohomologyModules G hG τ :=
  letI : HasSheafify (moduliCohomologyTopology G τ)
      AddCommGrpCat.{max (u + 1) v w} := moduliCohomologyHasSheafify G τ
  letI : HasWeakSheafify (moduliCohomologyTopology G τ)
      AddCommGrpCat.{max (u + 1) v w} := HasSheafify.isRightAdjoint
  letI : (moduliCohomologyTopology G τ).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v w} := moduliCohomologyWEquals G τ
  PresheafOfModules.sheafification.{max (u + 1) v w}
    (R := moduliCohomologyRings G hG τ) (𝟙 (moduliCohomologyRings G hG τ).obj)

/-- Sheafification preserves finite limits by the existing exact-sheafification instance.
Source: Stacks 075G (blueprint: lem-sfb-stack-higher-image-fibre-cohomology-presheaf). -/
instance moduliCohomologySheafification_preservesFiniteLimits
    {S : AlgebraicGeometry.Scheme.{u}} (G : BasedCategory.{v, w} (Over S))
    (hG : IsFibredInGroupoids G) (τ : ModuliCohomologyTopology) :
    PreservesFiniteLimits (moduliCohomologySheafification G hG τ) :=
  letI := moduliCohomologyHasSheafify G τ
  letI := moduliCohomologyWEquals G τ
  inferInstanceAs (PreservesFiniteLimits
    (PresheafOfModules.sheafification.{max (u + 1) v w}
      (R := moduliCohomologyRings G hG τ) (𝟙 (moduliCohomologyRings G hG τ).obj)))

/-- Sheafification preserves colimits by its existing sheafification adjunction.
Source: Stacks 075G (blueprint: lem-sfb-stack-higher-image-fibre-cohomology-presheaf). -/
instance moduliCohomologySheafification_preservesFiniteColimits
    {S : AlgebraicGeometry.Scheme.{u}} (G : BasedCategory.{v, w} (Over S))
    (hG : IsFibredInGroupoids G) (τ : ModuliCohomologyTopology) :
    PreservesFiniteColimits (moduliCohomologySheafification G hG τ) :=
  letI := moduliCohomologyHasSheafify G τ
  letI := moduliCohomologyWEquals G τ
  inferInstanceAs (PreservesFiniteColimits
    (PresheafOfModules.sheafification.{max (u + 1) v w}
      (R := moduliCohomologyRings G hG τ) (𝟙 (moduliCohomologyRings G hG τ).obj)))

/-- The sheaf complex obtained by applying h_* to a source resolution.
Source: Stacks 075G (blueprint: lem-sfb-stack-higher-image-fibre-cohomology-presheaf). -/
abbrev moduliCohomologyImageComplex {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology)
    {M : ModuliCohomologyModules F hF τ} (I : InjectiveResolution M) :=
  ((moduliCohomologyPushforward hF hG a τ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    I.cocomplex

/-- The underlying presheaf complex of h_*I, whose cohomology is sectionwise.
Source: Stacks 075G (blueprint: lem-sfb-stack-higher-image-fibre-cohomology-presheaf). -/
abbrev moduliCohomologyImagePresheafComplex {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology)
    {M : ModuliCohomologyModules F hF τ} (I : InjectiveResolution M) :=
  ((moduliCohomologyPresheafPushforward hF hG a τ).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I.cocomplex

/-- Sheafifying the underlying presheaf complex recovers the original sheaf complex.
This uses the actual sheafification counit, degree by degree.
Source: Stacks 075G (blueprint: lem-sfb-stack-higher-image-fibre-cohomology-presheaf). -/
def moduliCohomologySheafifiedComplexIso {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology)
    {M : ModuliCohomologyModules F hF τ} (I : InjectiveResolution M) :
    ((moduliCohomologySheafification G hG τ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (moduliCohomologyImagePresheafComplex hF hG a τ I) ≅
      moduliCohomologyImageComplex hF hG a τ I :=
  letI : HasSheafify (moduliCohomologyTopology G τ)
      AddCommGrpCat.{max (u + 1) v w} := moduliCohomologyHasSheafify G τ
  letI : HasWeakSheafify (moduliCohomologyTopology G τ)
      AddCommGrpCat.{max (u + 1) v w} := HasSheafify.isRightAdjoint
  letI : (moduliCohomologyTopology G τ).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v w} := moduliCohomologyWEquals G τ
  (NatIso.mapHomologicalComplex
    (asIso (PresheafOfModules.sheafificationAdjunction.{max (u + 1) v w}
      (R := moduliCohomologyRings G hG τ)
      (𝟙 (moduliCohomologyRings G hG τ).obj)).counit) (ComplexShape.up ℕ)).app
        (moduliCohomologyImageComplex hF hG a τ I)

/-- The canonical cocycle comparison, computed on the specified resolution.
The exact-functor homology isomorphism respects cycle inclusions and quotient maps;
its inverse followed by the sheafification counit is the cocycle-to-sheaf map.
Source: Stacks 075G (blueprint: lem-sfb-stack-higher-image-fibre-cohomology-presheaf). -/
def moduliCohomologyResolutionComparison {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology) (q : ℕ)
    {M : ModuliCohomologyModules F hF τ} (I : InjectiveResolution M) :
    (moduliCohomologySheafification G hG τ).obj
        ((moduliFibreCohomologyPresheaf hF hG a τ q).obj M) ⟶
      (moduliCohomologyHigherImage hF hG a τ q).obj M :=
  (moduliCohomologySheafification G hG τ).map
      (I.isoRightDerivedObj (moduliCohomologyPresheafPushforward hF hG a τ) q).hom ≫
    (((moduliCohomologyImagePresheafComplex hF hG a τ I).sc q).mapHomologyIso
      (moduliCohomologySheafification G hG τ)).inv ≫
    (HomologicalComplex.homologyMapIso
      (moduliCohomologySheafifiedComplexIso hF hG a τ I) q).hom ≫
    (I.isoRightDerivedObj (moduliCohomologyPushforward hF hG a τ) q).inv

end CategoryTheory

namespace CategoryTheory

/-- The canonical fibre identification on a resolution and a map to a fibre resolution.
The section isomorphism is the counit-normalized compatible-family formula.
Source: Stacks 075G (blueprint: lem-sfb-stack-higher-image-fibre-cohomology-presheaf). -/
def moduliCohomologyFibreResolutionComparison {S : AlgebraicGeometry.Scheme.{u}}
    {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (a : BasedFunctor F G) (y : G.obj) (τ : ModuliCohomologyTopology) (q : ℕ)
    {M : ModuliCohomologyModules F hF τ} (I : InjectiveResolution M)
    (J : InjectiveResolution ((moduliCohomologyFibreRestriction hF hG a y τ).obj M))
    (t : ((moduliCohomologyFibreRestriction hF hG a y τ).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex) :
    (moduliCohomologyEvaluation G hG τ y).obj
        ((moduliFibreCohomologyPresheaf hF hG a τ q).obj M) ⟶
      (moduliCohomologyFibreGroups hF hG a y τ q).obj M :=
  (moduliCohomologyEvaluation G hG τ y).map
      (I.isoRightDerivedObj (moduliCohomologyPresheafPushforward hF hG a τ) q).hom ≫
    (((moduliCohomologyImagePresheafComplex hF hG a τ I).sc q).mapHomologyIso
      (moduliCohomologyEvaluation G hG τ y)).inv ≫
    HomologicalComplex.homologyMap
      ((NatIso.mapHomologicalComplex (moduliCohomologySectionsIso hF hG a y τ)
        (ComplexShape.up ℕ)).hom.app I.cocomplex) q ≫
    HomologicalComplex.homologyMap
      (((moduliCohomologyGlobalSections (moduliCohomologyFibre a y)
        (moduliCohomologyFibre_isFibred hF hG a y) τ).mapHomologicalComplex
          (ComplexShape.up ℕ)).map t) q ≫
    (J.isoRightDerivedObj (moduliCohomologyGlobalSections (moduliCohomologyFibre a y)
      (moduliCohomologyFibre_isFibred hF hG a y) τ) q).inv

/-- Higher images are the sheafifications of fibre cohomology, naturally in the module.
Source: Stacks 075G (blueprint: lem-sfb-stack-higher-image-fibre-cohomology-presheaf).

Proof: choose a nonnegative injective module resolution M→I and put K=h_*I.
The derived-map formula (lem-weil-pbc-derived-functor-map-via-lift) identifies
R^q h_*M with H^q(K). Underlying presheaf kernels and quotients are sectionwise,
so the presheaf cohomology of K has the stated restriction maps and scalar actions.
Test-fibre restriction is exact and preserves injectives by
lem-sfb-stack-test-fibre-restriction-injectives (Stacks 06X2). Thus its restriction
of I computes the independent fibre cohomology. The counit formula identifies
sections degree by degree; base change of tests restricts precisely these same
families. Consequently the fibre identification is the displayed resolution map.
Exact module sheafification (lem-weil-pbc-ringed-site-module-sheafification-exact)
preserves homology by lem-sp-exact-functor-preserves-homology (c), and its counit
identifies the sheafified presheaf complex with K. Their composite is the displayed
cocycle comparison, giving the natural sheaf isomorphism. Lift module morphisms
to maps of injective resolutions by lem-weil-pbc-injective-resolution-lift-exists;
the derived-map formula gives naturality and independence of every choice. On
fibres the same formula holds for every augmentation-compatible lift to any
injective resolution J; any two such lifts are homotopic. The scalar actions and
restrictions commute already on section complexes and descend to cohomology.
No representability, finiteness, flatness or quasi-coherence hypothesis is used. -/
theorem moduli_higherImage_fibreCohomology_presheaf
    {S : AlgebraicGeometry.Scheme.{u}} {F G : BasedCategory.{v, w} (Over S)}
    (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G)
    (a : BasedFunctor F G) (τ : ModuliCohomologyTopology) (q : ℕ) :
    (∃ σ : moduliFibreCohomologyPresheaf hF.1.1 hG.1.1 a τ q ⋙
          moduliCohomologySheafification G hG.1.1 τ ≅
        moduliCohomologyHigherImage hF.1.1 hG.1.1 a τ q,
      ∀ (M : ModuliCohomologyModules F hF.1.1 τ) (I : InjectiveResolution M),
        σ.hom.app M = moduliCohomologyResolutionComparison hF.1.1 hG.1.1 a τ q I) ∧
    ∀ y : G.obj,
      ∃ e : moduliFibreCohomologyPresheaf hF.1.1 hG.1.1 a τ q ⋙
            moduliCohomologyEvaluation G hG.1.1 τ y ≅
          moduliCohomologyFibreGroups hF.1.1 hG.1.1 a y τ q,
        (∀ (M : ModuliCohomologyModules F hF.1.1 τ) (I : InjectiveResolution M)
          (J : InjectiveResolution
            ((moduliCohomologyFibreRestriction hF.1.1 hG.1.1 a y τ).obj M))
          (t : ((moduliCohomologyFibreRestriction hF.1.1 hG.1.1 a y τ).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex),
          (moduliCohomologyFibreRestriction hF.1.1 hG.1.1 a y τ).map (I.ι.f 0) ≫ t.f 0 =
            J.ι.f 0 →
          e.hom.app M =
            moduliCohomologyFibreResolutionComparison hF.1.1 hG.1.1 a y τ q I J t) ∧
        ∀ (M : ModuliCohomologyModules F hF.1.1 τ)
          (b : (moduliCohomologyRings G hG.1.1 τ).obj.obj (op y))
          (x : ((moduliFibreCohomologyPresheaf hF.1.1 hG.1.1 a τ q).obj M).obj (op y)),
          e.hom.app M (b • x) =
            ((moduliCohomologyGlobalSections (moduliCohomologyFibre a y)
              (moduliCohomologyFibre_isFibred hF.1.1 hG.1.1 a y) τ).rightDerived q).map
                (moduliCohomologyFibreScalar hF.1.1 hG.1.1 a y τ M b) (e.hom.app M x) := by
  sorry

end CategoryTheory
