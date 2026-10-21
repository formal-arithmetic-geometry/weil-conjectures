/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.CompletedStalkReparametrizationCoherence
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.CategoryTheory.StrictRoosModel
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-! # Point sections of the specified completion cone

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (3), sectionwise cone
and canonical completion comparisons; Stacks Tag 0941
(blueprint: lem-trf-point-sections-completion-cone).

The chain comparison and its two projections are the existing `CompletedStalk.sectionsRoos`,
`roosFirst`, and `roosSecond`. Sections retain their canonical integral scalar action.
The natural-number index n denotes exponent n+1. All derived comparisons are normalized
on every flat-term K-flat representative, including unbounded representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointSectionsCompletionCone

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Spec of the specified geometric field Frobenius, on the original algebraic closure.
Source: blueprint clause (3), coefficient convention
(blueprint: lem-trf-point-sections-completion-cone). -/
def frobenius : Spec (.of D.k) ⟶ Spec (.of D.k) :=
  letI := Fintype.ofFinite D.k₀
  Spec.map (CommRingCat.ofHom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingHom)

/-- The existing section complex functor, with its canonical integral coefficient action.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
abbrev sections := CompletedStalk.sectionsComplex D l E

/-- The existing ordinary-module localization used by integral point sections.
Source: blueprint clause (3); Stacks 05RU
(blueprint: lem-trf-point-sections-completion-cone). -/
abbrev moduleQ := CompletedStalk.moduleQ l E

/-- Exact sections' specified comparison with termwise sections on representatives.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def factors : DerivedCategory.Q ⋙ pointFibreIntegralAmbient D l E ≅
    sections D l E ⋙ moduleQ l E :=
  @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointIntegralSections l E D.k) (pointIntegralSectionsAdditive l E D.k)
    (pointFibreIntegralLimits D l E) (pointFibreIntegralColimits D l E)

/-- The strict reduction tower P_n, with its actual quotient transitions.
Source: blueprint clause (3); identity-extension specialization of the recorded tower
(blueprint: lem-trf-point-sections-completion-cone). -/
abbrev reductions := integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))

/-- The completed identity coefficient extension, before applying sections.
Source: blueprint clause (3); Bhatt--Scholze 3.4.10
(blueprint: lem-trf-point-sections-completion-cone). -/
abbrev completion :=
  integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))

/-- The derived reduction-limit functor followed by exact sections.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def completedSections := completion D l E ⋙ pointFibreIntegralAmbient D l E

/-- The specified identity-extension model, followed by exact sections and the
identity on both sectionwise cone coordinates. No Roos-triangle filler is chosen.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def completionModel
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) :
    (completedSections D l E).obj (DerivedCategory.Q.obj P.obj) ≅
      (moduleQ l E).obj
        (integralOperationsRoos ((reductions D l E).obj P.obj ⋙ sections D l E)) :=
  (pointFibreIntegralAmbient D l E).mapIso
      ((integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E)
        (Spec (.of D.k))).app P) ≪≫
    (factors D l E).app
      ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
        (Spec (.of D.k))).obj P.obj) ≪≫
    (moduleQ l E).mapIso (CompletedStalk.sectionsRoos D l E ((reductions D l E).obj P.obj))

/-- The same model at any representative isomorphism q:Q(P) ≅ N.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def completionModelAt
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj) :=
  (completedSections D l E).mapIso q.symm ≪≫ completionModel D l E P

/-- The defining pullback representative, exact sections, and c_C, in that order.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def pullbackModel
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) :
    (pointFibreIntegralAmbient D l E).obj
        ((integralDerivedPullback l E (frobenius D)).obj (DerivedCategory.Q.obj P.obj)) ≅
      (moduleQ l E).obj (integralOperationsRoos
        ((integralOperationsPullbackTowerFunctor l E (frobenius D)).obj P.obj ⋙
          sections D l E)) :=
  (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullbackComparison l E (frobenius D)).app P) ≪≫
    (factors D l E).app
      ((integralOperationsPullbackComplexFunctor l E (frobenius D)).obj P.obj) ≪≫
    (moduleQ l E).mapIso (CompletedStalk.sectionsRoos D l E
      ((integralOperationsPullbackTowerFunctor l E (frobenius D)).obj P.obj))

/-- The specified beta on every resolution, using the defining pullback comparison.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def beta
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj) :=
  (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullback l E (frobenius D)).mapIso q.symm) ≪≫
    pullbackModel D l E P

/-- The augmentation a_P: exact sections of the specified completion unit, followed
by the identity on both sectionwise product coordinates. Its shifted coordinate is zero.
Source: blueprint clause (3); Bhatt--Scholze 3.5.2; Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def augmentation (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  (sections D l E).map ((completedScalarIdentityUnit l E (Spec (.of D.k))).app P) ≫
    (CompletedStalk.sectionsRoos D l E ((reductions D l E).obj P)).hom

/-- The normalization predicate fixes the actual completion map on every flat-term
K-flat resolution, rather than its composites with just the finite reductions.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def CompletionNormalization
    (α : (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
        pointFibreIntegralAmbient D l E ≅
      (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ completedSections D l E) : Prop :=
  ∀ (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj),
    (pointFibreIntegralAmbient D l E).map q.hom ≫ α.hom.app N ≫
        (completionModelAt D l E N P q).hom =
      (factors D l E).hom.app P.obj ≫ (moduleQ l E).map (augmentation D l E P.obj)

/-- The canonical completion comparison is an isomorphism, uniquely fixed by its
zero shifted coordinate and quotient augmentation on all resolutions.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone).
Proof: apply finiteFreeCompletedScalarComparison to the identity extension. Its
chain normalization is completedScalarIdentityUnit, with zero shifted component
and quotient units on the other component. Derived completeness of N makes it
invertible. Compose with exact sections. The representative comparison followed
by c_P is completionModelAt, giving the displayed whole-map equality. Naturality
of the identity-extension comparison supplies a natural isomorphism for every
derived morphism. Every constructible object has a good representative; cancellation
of its localized quasi-isomorphism proves uniqueness and resolution independence. -/
theorem completionComparison_existsUnique [Fact (l ≠ D.p)] :
    ∃! α : (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
        pointFibreIntegralAmbient D l E ≅
      (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ completedSections D l E,
      CompletionNormalization D l E α := by
  sorry

/-- The completion comparison selected by its unique whole-cone normalization.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def completionComparison [Fact (l ≠ D.p)] :=
  (completionComparison_existsUnique D l E).exists.choose

/-- The specified alpha_N on every resolution, with its actual evaluated quotient cone.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def alpha [Fact (l ≠ D.p)]
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj) :=
  (completionComparison D l E).app N ≪≫ completionModelAt D l E N P q

/-- The derived-limit property of the entire evaluated tower. The existential product
witness asserts existence; it makes no choice of a derived-limit comparison.
Source: blueprint clause (3); Stacks 08TC
(blueprint: lem-trf-point-sections-completion-cone). -/
def ModuleDerivedLimit
    (T : ℕᵒᵖ ⥤ CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ) : Prop :=
  ∃ hP : HasProduct (fun n : ℕ ↦ (moduleQ l E).obj (T.obj (op n))),
    @IsDerivedLimit _ _ _ _ _ (fun _n : ℤ ↦ inferInstance) _
      (fun n : ℕ ↦ (moduleQ l E).obj (T.obj (op n))) hP
      (fun n : ℕ ↦ (moduleQ l E).map (integralOperationsTowerStep T n))
      ((moduleQ l E).obj (integralOperationsRoos T))

/-- The map on H(D) induced by the already descended reduction construction, using
its specified model comparisons. It is defined independently of alpha.
Source: blueprint clause (3), derived naturality
(blueprint: lem-trf-point-sections-completion-cone). -/
def reductionMap
    {N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k))} (f : N ⟶ N')
    (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj)
    (q' : DerivedCategory.Q.obj P'.obj ≅ N'.obj) :=
  (completionModelAt D l E N P q).inv ≫ (completedSections D l E).map f.hom ≫
    (completionModelAt D l E N' P' q').hom

/-- The map on H(B) induced by completed pullback and its defining model comparisons.
It is defined independently of alpha and of any chosen Roos-triangle filler.
Source: blueprint clause (3), derived naturality
(blueprint: lem-trf-point-sections-completion-cone). -/
def pullbackMap
    {N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k))} (f : N ⟶ N')
    (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj)
    (q' : DerivedCategory.Q.obj P'.obj ≅ N'.obj) :=
  (beta D l E N P q).inv ≫ (pointFibreIntegralAmbient D l E).map
    ((integralDerivedPullback l E (frobenius D)).map f.hom) ≫
      (beta D l E N' P' q').hom

/-- Both canonical comparisons are natural for every derived morphism and every pair
of flat-term K-flat representatives. Taking f to be the identity gives independence
under the specified resolution comparisons.
Source: blueprint clause (3), comparison descent; Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def DerivedNaturality [Fact (l ≠ D.p)] : Prop :=
  ∀ (N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k))) (f : N ⟶ N')
    (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj)
    (q' : DerivedCategory.Q.obj P'.obj ≅ N'.obj),
    (alpha D l E N P q).hom ≫ reductionMap D l E f P P' q q' =
        (pointFibreIntegralAmbient D l E).map f.hom ≫ (alpha D l E N' P' q').hom ∧
      (beta D l E N P q).hom ≫ pullbackMap D l E f P P' q q' =
        (pointFibreIntegralAmbient D l E).map
          ((integralDerivedPullback l E (frobenius D)).map f.hom) ≫
            (beta D l E N' P' q').hom

/-- Exact sections commute with the normalized completion cone, its diagonal maps,
and its localized comparisons, with the specified alpha and beta.
Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model,
proof clause (3), sectionwise cone and comparison descent; Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone).

Proof, following all eight DAG steps:
1. Pro-etale products are sectionwise by lem-weil-proetale-countable-products-exact.
Exact point sections are additive and preserve binary biproducts. The product
identifications on both summands give the existing sectionsRoos, with precisely
its two projection normalizations.
2. In the signed coordinates (b,a), the differential on either side is
(-db-(1-s)a,da). Strict compatibility gives (1-s_Y)W=W(1-s_X).
Thus the existing RoosMap is diagonal on the two components, and sectionsRoos is
natural for all strict tower maps, not only maps between individual levels.
3. Products of surjections of modules are surjective by coordinatewise lifting.
The sheaf-module and ordinary-module categories therefore have exact countable
products. Apply lem-weil-derived-limit-products-core to both whole towers. Their
mapping-cocone triangles are Roos triangles, proving both derived-limit assertions.
4. Exact products preserve levelwise quasi-isomorphisms, so the cone does too.
Exact sections preserve quasi-isomorphisms. The naturality square consequently
also holds for their inverses after localization, and then for arbitrary roofs.
This is the strict-cone descent of lem-weil-strict-roos-comparison.
5. Derived change of rings computes all N_n on the single good representative P;
finite exact inverse image computes g_n*P_n. The actual quotient transitions are
those of reductions and integralOperationsPullbackTowerFunctor. Thus the two
evaluated cones represent exactly the two claimed derived inverse limits.
6. The identity-extension specialization of finiteFreeCompletedScalarComparison
is the specified completeness unit. On P its shifted coordinate is zero and its
unshifted coordinates are x mapped to x tensor 1. Composing exact sections with
sectionsRoos is exactly augmentation. Derived completeness makes it invertible.
7. The defining integralDerivedPullbackComparison identifies Lg*N with the
actual Roos complex on C. Exact sections, factors, and sectionsRoos on C are
precisely beta, fixing both its product components.
8. The two descended constructions and their representative comparisons are
natural on every derived morphism. Combine their naturality with step 2 to obtain
DerivedNaturality, including identity morphisms between any two resolutions.
No arbitrary comparison between separately chosen Roos triangles enters. -/
theorem pointSectionsCompletionCone [Fact (l ≠ D.p)] :
    (∀ T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ,
      (∀ (n : ℕ) (i : ℤ),
        (CompletedStalk.sectionsRoos D l E T).hom.f i ≫
            CompletedStalk.roosFirst (T ⋙ sections D l E) n i =
          (pointIntegralSections l E D.k).map (CompletedStalk.roosFirst T n i)) ∧
      (∀ (n : ℕ) (i : ℤ),
        (CompletedStalk.sectionsRoos D l E T).hom.f i ≫
            CompletedStalk.roosSecond (T ⋙ sections D l E) n i =
          (pointIntegralSections l E D.k).map (CompletedStalk.roosSecond T n i)) ∧
      integralOperationsDerivedLimitProperty l E (Spec (.of D.k)) T
          (DerivedCategory.Q.obj (integralOperationsRoos T)) ∧
        ModuleDerivedLimit l E (T ⋙ sections D l E)) ∧
    (∀ (T U : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (w : T ⟶ U),
      (sections D l E).map (integralOperationsRoosMap w) ≫
          (CompletedStalk.sectionsRoos D l E U).hom =
        (CompletedStalk.sectionsRoos D l E T).hom ≫
          integralOperationsRoosMap (Functor.whiskerRight w (sections D l E))) ∧
    (∀ (T U : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (w : T ⟶ U) (n : ℕ) (i : ℤ),
      (integralOperationsRoosMap w).f i ≫ CompletedStalk.roosFirst U n i =
          CompletedStalk.roosFirst T n i ≫ (w.app (op n)).f i ∧
        (integralOperationsRoosMap w).f i ≫ CompletedStalk.roosSecond U n i =
          CompletedStalk.roosSecond T n i ≫ (w.app (op n)).f (i + -1)) ∧
    (∀ (T U : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (w : T ⟶ U),
      (∀ n : ℕ, QuasiIso (w.app (op n))) →
        QuasiIso (integralOperationsRoosMap w) ∧
        QuasiIso (integralOperationsRoosMap (Functor.whiskerRight w (sections D l E)))) ∧
    (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (i : ℤ),
      (∀ (n : ℕ) (z : ((sections D l E).obj P).X i),
        (((augmentation D l E P).f i ≫
          CompletedStalk.roosFirst ((reductions D l E).obj P ⋙ sections D l E) n i).hom z) =
            integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) n
              (P.X i) (op (ProEt.mk (𝟙 (Spec (.of D.k))))) 1 z) ∧
      (∀ n : ℕ, (augmentation D l E P).f i ≫
        CompletedStalk.roosSecond ((reductions D l E).obj P ⋙ sections D l E) n i = 0)) ∧
    (∀ (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
      (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ N.obj),
      (pointFibreIntegralAmbient D l E).map q.hom ≫ (alpha D l E N P q).hom =
        (factors D l E).hom.app P.obj ≫ (moduleQ l E).map (augmentation D l E P.obj)) ∧
    (∀ (N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k))) (f : N ⟶ N')
      (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ N.obj)
      (q' : DerivedCategory.Q.obj P'.obj ≅ N'.obj) (w : P ⟶ P'),
      q.hom ≫ f.hom = DerivedCategory.Q.map w.hom ≫ q'.hom →
        reductionMap D l E f P P' q q' =
            (moduleQ l E).map (integralOperationsRoosMap
              (Functor.whiskerRight ((reductions D l E).map w.hom) (sections D l E))) ∧
          pullbackMap D l E f P P' q q' =
            (moduleQ l E).map (integralOperationsRoosMap
              (Functor.whiskerRight
                ((integralOperationsPullbackTowerFunctor l E (frobenius D)).map w.hom)
                (sections D l E)))) ∧
    DerivedNaturality D l E := by
  sorry

end WeilConjectures.PointSectionsCompletionCone
