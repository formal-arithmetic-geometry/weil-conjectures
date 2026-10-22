# AlgebraicGeometry.Etale.normalizationRestrictedIso and its construction block

## Reason

The three independent fixed-resolution comparison lemmas need the prescribed constructions. Move those constructions to a public data module to avoid an import cycle; the original module publicly reexports that module. All mathematical constructions and public types stay identical. The pushed-forward complex receives an explicit type. Four construction aliases become abbreviations, preserving their formulas while avoiding costly conversion through nested sheaf constructions. This is a dependency extraction, not a change to a mathematical object.

## Old

The following declaration block was in `Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization`:

```lean
module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.AlgebraicGeometry.RawRestrictedResolutionEvaluation
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
public import
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
import Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact

/-! # Normalization of raw and restricted cohomology classes

Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

/-- Termwise restriction of the prescribed injective resolution.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationRestrictionComplex {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    CochainComplex (Sheaf W.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ :=
  ((upperStar AddCommGrpCat.{u + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex

/-- Map an injective-resolution augmentation through an additive functor.
Source: Stacks Project, Tags 013K and 072W.
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationMappedAugmentation
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) [L.Additive] (A : C) (I : InjectiveResolution A) :
    (CochainComplex.singleFunctor D 0).obj (L.obj A) ⟶
      (L.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex :=
  (L.mapCochainComplexSingleFunctor 0).inv.app A ≫
    (L.mapHomologicalComplex (.up ℤ)).map I.ι'

private theorem normalizationMappedAugmentation_quasiIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) [L.Additive] [L.PreservesHomology]
    (A : C) (I : InjectiveResolution A) :
    QuasiIso (normalizationMappedAugmentation L A I) := by
  dsimp only [normalizationMappedAugmentation]
  infer_instance

/-- The restricted augmentation, with the single-complex comparison.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationRestrictionAugmentation {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} W.hom).obj F) ⟶
        normalizationRestrictionComplex W F I :=
  normalizationMappedAugmentation (upperStar AddCommGrpCat.{u + 1} W.hom) F I

/-- Exact restriction preserves the augmentation quasi-isomorphism.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization).
Proof: the augmentation is a quasi-isomorphism, inverse image is exact, and its
single-complex comparison is an isomorphism (step 1 of the node's proof). -/
theorem normalizationRestrictionAugmentation_quasiIso {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    QuasiIso (normalizationRestrictionAugmentation W F I) := by
  exact normalizationMappedAugmentation_quasiIso
    (upperStar AddCommGrpCat.{u + 1} W.hom) F I

/-- The restricted resolution is K-injective.
Source: Stacks Project, Tags 03Q8, 072W and 070J
(blueprint: lem-weil-pbc-raw-restricted-class-normalization).
Proof: etale restriction preserves injective abelian sheaves by
lem-sbc-etale-abelian-restriction-injectives. The restricted resolution is zero
in negative degrees, so the bounded-below injective criterion applies (step 1). -/
theorem normalizationRestrictionComplex_isKInjective {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (normalizationRestrictionComplex W F I).IsKInjective := by
  have : ∀ n : ℤ, Injective
      (((upperStar AddCommGrpCat.{u + 1} W.hom).mapHomologicalComplex
        (.up ℤ)).obj I.cochainComplex |>.X n) :=
    fun n ↦ injective_upperStar_obj_of_etale_addCommGrp W.hom (I.cochainComplex.X n)
  change CochainComplex.IsKInjective
    (((upperStar AddCommGrpCat.{u + 1} W.hom).mapHomologicalComplex
      (.up ℤ)).obj I.cochainComplex)
  exact CochainComplex.isKInjective_of_injective _ 0

/-- Restrict the prescribed resolution, retaining its augmentation.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationRestrictedResolution {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    ((CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} W.hom).obj F)).KInjectiveResolution where
  I := normalizationRestrictionComplex W F I
  ι := normalizationRestrictionAugmentation W F I
  quasiIso_ι := normalizationRestrictionAugmentation_quasiIso W F I
  isKInjective := normalizationRestrictionComplex_isKInjective W F I

/-- Sections of an etale restriction, naturally in the coefficient sheaf.
Source: Stacks Project, Tag 03Q8 (restriction to an etale object)
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationSectionsIso {X : Scheme.{u}} (W : X.Etale) :
    RawRestrictedComparison.underivedSections W ≅
      (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op W) := by
  let i : (MorphismProperty.Over.map ⊤ W.prop).obj
      (Scheme.Etale.mk (𝟙 W.left)) ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl W.left) (by rfl)
  exact Functor.isoWhiskerRight
      (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.hom W.prop)
      (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ≪≫
    Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections W.left.smallEtaleTopology AddCommGrpCat.{u + 1}
        (MorphismProperty.Over.mkIdTerminal @Etale W.left)) ≪≫
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso i.op.symm

/-- The pushed-forward resolution as a complex of presheaves.
Source: Stacks Project, Tag 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable abbrev normalizationPresheafComplex {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :=
  ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℤ)).obj
    (((lowerStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)

/-- Canonical resolution computation of restricted cohomology, with no raw Hom involved.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationRestrictedIso {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (V : S.Etale) :
    rawAffineRestrictedCohomology f q F V ≅
      ((normalizationPresheafComplex f F I).homology (q : ℤ)).obj (op V) :=
  (normalizationRestrictedResolution
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) F I).homologyRightDerivedFunctorObjIso
      (Sheaf.Γ (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ) ≪≫
  (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
    ((NatIso.mapHomologicalComplex
      (normalizationSectionsIso ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))
      (.up ℤ)).app I.cochainComplex) ≪≫
  ((normalizationPresheafComplex f F I).sc (q : ℤ)).mapHomologyIso
    ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op V))

/-- The canonical cocycle map: sheafify sectionwise homology, then use the counit
and the augmentation comparison for the prescribed resolution. A section cocycle
is sent to its class in the cohomology sheaf of the direct-image complex.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationResolutionClass {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (normalizationPresheafComplex f F I).homology (q : ℤ) ⟶
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj :=
  toSheafify S.smallEtaleTopology _ ≫
    ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((((normalizationPresheafComplex f F I).sc (q : ℤ)).mapHomologyIso
          (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})).inv ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex
            (sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).counit
            (.up ℤ)).app
            (((lowerStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex (.up ℤ)).obj
              I.cochainComplex)) (q : ℤ) ≫
        (I.isoRightDerivedObjCochainComplex
          (lowerStar AddCommGrpCat.{u + 1} f) q).inv ≫
        ((lowerStar AddCommGrpCat.{u + 1} f).homologyRightDerivedFunctorPlusObjSingleFunctorIso
          F q).inv))

/-- The specified map from restricted cohomology to higher-image sections.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationIota {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale) :
    rawAffineRestrictedCohomology f q F V ⟶
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.obj (op V) :=
  (normalizationRestrictedIso f q F (injectiveResolution F) V).hom ≫
    (normalizationResolutionClass f q F (injectiveResolution F)).app (op V)

/-- Restricted cohomology as a presheaf, transported from the sectionwise cohomology
of the chosen injective resolution. Its restriction is identified with cohomology
pullback in the normalization theorem below.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationRestrictedPresheaf {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj V := rawAffineRestrictedCohomology f q F V.unop
  map {V V'} t := (normalizationRestrictedIso f q F (injectiveResolution F) V.unop).hom ≫
    ((normalizationPresheafComplex f F (injectiveResolution F)).homology (q : ℤ)).map t ≫
    (normalizationRestrictedIso f q F (injectiveResolution F) V'.unop).inv
  map_id V := by simp
  map_comp t t' := by simp

/-- The map on the two fibre products induced by a morphism of etale objects.
Source: Stacks Project, Tag 03Q8
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationChartMap {X S : Scheme.{u}} (f : X ⟶ S)
    {V V' : S.Etale} (t : V' ⟶ V) : pullback V'.hom f ⟶ pullback V.hom f :=
  (MorphismProperty.Over.pullback @Etale ⊤ f).map t |>.left

/-- The actual cohomology pullback between etale charts, followed by inverse-image
composition on the coefficients. No raw Hom or transported restriction is used.
Source: Stacks Project, Tag 03Q8
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationCohomologyRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etale} (t : V' ⟶ V) :
    rawAffineRestrictedCohomology f q F V ⟶ rawAffineRestrictedCohomology f q F V' :=
  rawAffineComplexPullback (q : ℤ) (normalizationChartMap f t)
      ((CochainComplex.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj F)) ≫
    (cohomology AddCommGrpCat.{u + 1} (pullback V'.hom f) (q : ℤ)).map
      (DerivedCategory.Q.map
        (((upperStar AddCommGrpCat.{u + 1}
            (normalizationChartMap f t)).mapCochainComplexSingleFunctor 0).hom.app _ ≫
          (CochainComplex.singleFunctor _ 0).map
            ((upperStarComp AddCommGrpCat.{u + 1} (normalizationChartMap f t)
              (pullback.snd V.hom f) (pullback.snd V'.hom f)
              (MorphismProperty.Over.w
                ((MorphismProperty.Over.pullback @Etale ⊤ f).map t)).symm).inv.app F)))

set_option backward.isDefEq.respectTransparency true in
/-- Additivity of the prescribed derived-adjunction class construction.
Source: Stacks Project, Tag 03Q8
(blueprint: lem-weil-pbc-raw-restricted-class-normalization).
Proof: precomposition with the exact inverse-image single comparison is additive;
the derived adjunction is an additive Hom equivalence; zeroth homology and the
shift comparison are additive. Evaluation at the fixed identity generator is
additive as well. Their composite therefore preserves sums (proof step 6). -/
theorem normalizationClass_add {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale)
    (z z' : (abelianHigherDirectImageRawPresheaf f q F).obj (op V)) :
    abelianHigherDirectImageClass f q F V (z + z') =
      abelianHigherDirectImageClass f q F V z + abelianHigherDirectImageClass f q F V z' := by
  let c := toSheafify S.smallEtaleTopology (abelianHigherDirectImageRawPresheaf f q F) ≫
    (canonicalComparison f q F).hom.hom
  have h := (c.app (op V)).hom.map_add z z'
  change (toSheafify S.smallEtaleTopology _ ≫
      (canonicalComparison f q F).hom.hom).app (op V) (z + z') =
    (toSheafify S.smallEtaleTopology _ ≫
      (canonicalComparison f q F).hom.hom).app (op V) z +
    (toSheafify S.smallEtaleTopology _ ≫
      (canonicalComparison f q F).hom.hom).app (op V) z' at h
  simpa only [canonicalComparison_class] using h

/-- Bundle the existing canonical class function as an abelian-group morphism.
Its value is exactly abelianHigherDirectImageClass, without selecting a map from
an existence theorem.
Source: Stacks Project, Tag 03Q8
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationKappaComponent {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale) :
    (abelianHigherDirectImageRawPresheaf f q F).obj (op V) ⟶
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.obj (op V) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (abelianHigherDirectImageClass f q F V)
    (normalizationClass_add f q F V))

set_option backward.isDefEq.respectTransparency true in
/-- Naturality in etale objects of the prescribed canonical class map.
Source: Stacks Project, Tag 03Q8
(blueprint: lem-weil-pbc-raw-restricted-class-normalization).
Proof: the free represented map sends the identity generator at V' to the
restriction of the generator at V. Naturality of the single comparison and the
derived adjunction turns precomposition by this map into precomposition of its
adjunct. Zeroth homology and the shift comparison preserve this equality;
evaluating the restricted generator gives the restriction of the original class.
This is the generator calculation of proof steps 4 and 6. -/
theorem normalizationKappaComponent_naturality {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etaleᵒᵖ} (t : V ⟶ V') :
    (abelianHigherDirectImageRawPresheaf f q F).map t ≫
        normalizationKappaComponent f q F V'.unop =
      normalizationKappaComponent f q F V.unop ≫
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.map t := by
  let c := toSheafify S.smallEtaleTopology (abelianHigherDirectImageRawPresheaf f q F) ≫
    (canonicalComparison f q F).hom.hom
  have hc (U : S.Etale) : normalizationKappaComponent f q F U = c.app (op U) := by
    ext z
    exact (canonicalComparison_class f q F U z).symm
  rw [hc, hc]
  exact c.naturality t

/-- The presheaf class map with components given by the landed canonical class
construction, using its separately stated naturality.
Source: Stacks Project, Tag 03Q8
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationKappa {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    abelianHigherDirectImageRawPresheaf f q F ⟶
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj where
  app V := normalizationKappaComponent f q F V.unop
  naturality _ _ t := normalizationKappaComponent_naturality f q F t

/-- The unique sheafification lift of the specified raw class map.
Source: Stacks Project, Tag 03Q8 and the sheafification adjunction
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationLift {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (abelianHigherDirectImageRawPresheaf f q F) ⟶
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  ((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (normalizationKappa f q F)

/-- The coefficient map on the raw derived-Hom presheaf.
Source: Stacks Project, Tag 03Q8
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationRawCoefficient {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    abelianHigherDirectImageRawPresheaf f q F ⟶ abelianHigherDirectImageRawPresheaf f q G :=
  Functor.whiskerLeft _ (preadditiveYoneda.map
    ((shiftFunctor _ (q : ℤ)).map ((DerivedCategory.Plus.singleFunctor _ 0).map φ)))

/-- The coefficient map on restricted derived cohomology.
Source: Stacks Project, Tag 03Q8
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationRestrictedCoefficient {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (V : S.Etale) :
    rawAffineRestrictedCohomology f q F V ⟶ rawAffineRestrictedCohomology f q G V :=
  (cohomology AddCommGrpCat.{u + 1} (pullback V.hom f) (q : ℤ)).map
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
      ((upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).map φ)))

/-- The coefficient map on higher direct images.
Source: Stacks Project, Tag 03Q8
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationHigherCoefficient {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) :=
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    (R+((f)_*[AddCommGrpCat.{u + 1}]).map ((DerivedCategory.Plus.singleFunctor _ 0).map φ))

```

## New

The constructions move into the new public data module below. The original module
publicly imports it. Existing geometric instances are cached locally during elaboration.
The pushed-forward complex receives an explicit type and becomes a regular definition.
The aliases normalizationIota, normalizationRawCoefficient,
normalizationRestrictedCoefficient and normalizationHigherCoefficient become abbreviations.
Their types and mathematical formulas are preserved. The transported presheaf is assembled
by a generic conjugation constructor with the same objects and restriction composites.
This controls conversion cost without changing any chosen resolution or comparison.
No target signature changes. The moved definitions and their consumers are included for
independent review of preservation of target meaning.

```lean
module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.AlgebraicGeometry.RawRestrictedResolutionEvaluation
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
public import
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison

/-! # Data for normalization of raw and restricted cohomology classes

Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: def-weil-pbc-raw-restricted-normalization-data).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance

/-- Termwise restriction of the prescribed injective resolution.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationRestrictionComplex {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    CochainComplex (Sheaf W.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ :=
  ((upperStar AddCommGrpCat.{u + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex

/-- Map an injective-resolution augmentation through an additive functor.
Source: Stacks Project, Tags 013K and 072W.
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationMappedAugmentation
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) [L.Additive] (A : C) (I : InjectiveResolution A) :
    (CochainComplex.singleFunctor D 0).obj (L.obj A) ⟶
      (L.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex :=
  (L.mapCochainComplexSingleFunctor 0).inv.app A ≫
    (L.mapHomologicalComplex (.up ℤ)).map I.ι'

private theorem normalizationMappedAugmentation_quasiIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) [L.Additive] [L.PreservesHomology]
    (A : C) (I : InjectiveResolution A) :
    QuasiIso (normalizationMappedAugmentation L A I) := by
  dsimp only [normalizationMappedAugmentation]
  infer_instance

/-- The restricted augmentation, with the single-complex comparison.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationRestrictionAugmentation {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} W.hom).obj F) ⟶
        normalizationRestrictionComplex W F I :=
  normalizationMappedAugmentation (upperStar AddCommGrpCat.{u + 1} W.hom) F I

/-- Exact restriction preserves the augmentation quasi-isomorphism.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: def-weil-pbc-raw-restricted-normalization-data).
Proof: the augmentation is a quasi-isomorphism, inverse image is exact, and its
single-complex comparison is an isomorphism (step 1 of the node's proof). -/
theorem normalizationRestrictionAugmentation_quasiIso {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    QuasiIso (normalizationRestrictionAugmentation W F I) := by
  exact normalizationMappedAugmentation_quasiIso
    (upperStar AddCommGrpCat.{u + 1} W.hom) F I

/-- The restricted resolution is K-injective.
Source: Stacks Project, Tags 03Q8, 072W and 070J
(blueprint: def-weil-pbc-raw-restricted-normalization-data).
Proof: etale restriction preserves injective abelian sheaves by
lem-sbc-etale-abelian-restriction-injectives. The restricted resolution is zero
in negative degrees, so the bounded-below injective criterion applies (step 1). -/
theorem normalizationRestrictionComplex_isKInjective {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (normalizationRestrictionComplex W F I).IsKInjective := by
  have : ∀ n : ℤ, Injective
      (((upperStar AddCommGrpCat.{u + 1} W.hom).mapHomologicalComplex
        (.up ℤ)).obj I.cochainComplex |>.X n) :=
    fun n ↦ injective_upperStar_obj_of_etale_addCommGrp W.hom (I.cochainComplex.X n)
  change CochainComplex.IsKInjective
    (((upperStar AddCommGrpCat.{u + 1} W.hom).mapHomologicalComplex
      (.up ℤ)).obj I.cochainComplex)
  exact CochainComplex.isKInjective_of_injective _ 0

/-- Restrict the prescribed resolution, retaining its augmentation.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationRestrictedResolution {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    ((CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} W.hom).obj F)).KInjectiveResolution where
  I := normalizationRestrictionComplex W F I
  ι := normalizationRestrictionAugmentation W F I
  quasiIso_ι := normalizationRestrictionAugmentation_quasiIso W F I
  isKInjective := normalizationRestrictionComplex_isKInjective W F I

/-- Sections of an etale restriction, naturally in the coefficient sheaf.
Source: Stacks Project, Tag 03Q8 (restriction to an etale object)
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationSectionsIso {X : Scheme.{u}} (W : X.Etale) :
    RawRestrictedComparison.underivedSections W ≅
      (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op W) := by
  let i : (MorphismProperty.Over.map ⊤ W.prop).obj
      (Scheme.Etale.mk (𝟙 W.left)) ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl W.left) (by rfl)
  exact Functor.isoWhiskerRight
      (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.hom W.prop)
      (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ≪≫
    Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections W.left.smallEtaleTopology AddCommGrpCat.{u + 1}
        (MorphismProperty.Over.mkIdTerminal @Etale W.left)) ≪≫
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso i.op.symm

/-- The pushed-forward resolution as a complex of presheaves.
Source: Stacks Project, Tag 072W
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationPresheafComplex {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    CochainComplex (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ :=
  ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℤ)).obj
    (((lowerStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)

/-- Canonical resolution computation of restricted cohomology, with no raw Hom involved.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationRestrictedIso {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F)
    (V : S.Etale) :
    rawAffineRestrictedCohomology f q F V ≅
      ((normalizationPresheafComplex f F I).homology (q : ℤ)).obj (op V) :=
  (normalizationRestrictedResolution
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) F I).homologyRightDerivedFunctorObjIso
      (Sheaf.Γ (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ) ≪≫
  (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
    ((NatIso.mapHomologicalComplex
      (normalizationSectionsIso ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))
      (.up ℤ)).app I.cochainComplex) ≪≫
  ((normalizationPresheafComplex f F I).sc (q : ℤ)).mapHomologyIso
    ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op V))

/-- The canonical cocycle map: sheafify sectionwise homology, then use the counit
and the augmentation comparison for the prescribed resolution. A section cocycle
is sent to its class in the cohomology sheaf of the direct-image complex.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationResolutionClass {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (normalizationPresheafComplex f F I).homology (q : ℤ) ⟶
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj :=
  toSheafify S.smallEtaleTopology _ ≫
    ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((((normalizationPresheafComplex f F I).sc (q : ℤ)).mapHomologyIso
          (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})).inv ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex
            (sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).counit
            (.up ℤ)).app
            (((lowerStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex (.up ℤ)).obj
              I.cochainComplex)) (q : ℤ) ≫
        (I.isoRightDerivedObjCochainComplex
          (lowerStar AddCommGrpCat.{u + 1} f) q).inv ≫
        ((lowerStar AddCommGrpCat.{u + 1} f).homologyRightDerivedFunctorPlusObjSingleFunctorIso
          F q).inv))

/-- The specified map from restricted cohomology to higher-image sections.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable abbrev normalizationIota {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale) :
    rawAffineRestrictedCohomology f q F V ⟶
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.obj (op V) :=
  (normalizationRestrictedIso f q F (injectiveResolution F) V).hom ≫
    (normalizationResolutionClass f q F (injectiveResolution F)).app (op V)

/-- Transport a functor through a specified family of object isomorphisms.
The construction keeps the functor laws abstract, avoiding expansion of the
concrete resolution comparisons when projecting an object or a restriction map.
Source: conjugation of the functor laws by the given isomorphisms.
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationTransportPresheaf
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    (A : C → D) (e : ∀ V : C, A V ≅ P.obj V) : C ⥤ D where
  obj := A
  map {V V'} t := (e V).hom ≫ P.map t ≫ (e V').inv
  map_id V := by simp
  map_comp t t' := by simp

/-- Restricted cohomology as a presheaf, transported from the sectionwise cohomology
of the chosen injective resolution. Its restriction is identified with cohomology
pullback in the normalization theorem below.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationRestrictedPresheaf {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  normalizationTransportPresheaf
    ((normalizationPresheafComplex f F (injectiveResolution F)).homology (q : ℤ))
    (fun V ↦ rawAffineRestrictedCohomology f q F V.unop)
    (fun V ↦ normalizationRestrictedIso f q F (injectiveResolution F) V.unop)

/-- The map on the two fibre products induced by a morphism of etale objects.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationChartMap {X S : Scheme.{u}} (f : X ⟶ S)
    {V V' : S.Etale} (t : V' ⟶ V) : pullback V'.hom f ⟶ pullback V.hom f :=
  (MorphismProperty.Over.pullback @Etale ⊤ f).map t |>.left

/-- The actual cohomology pullback between etale charts, followed by inverse-image
composition on the coefficients. No raw Hom or transported restriction is used.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationCohomologyRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etale} (t : V' ⟶ V) :
    rawAffineRestrictedCohomology f q F V ⟶ rawAffineRestrictedCohomology f q F V' :=
  rawAffineComplexPullback (q : ℤ) (normalizationChartMap f t)
      ((CochainComplex.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj F)) ≫
    (cohomology AddCommGrpCat.{u + 1} (pullback V'.hom f) (q : ℤ)).map
      (DerivedCategory.Q.map
        (((upperStar AddCommGrpCat.{u + 1}
            (normalizationChartMap f t)).mapCochainComplexSingleFunctor 0).hom.app _ ≫
          (CochainComplex.singleFunctor _ 0).map
            ((upperStarComp AddCommGrpCat.{u + 1} (normalizationChartMap f t)
              (pullback.snd V.hom f) (pullback.snd V'.hom f)
              (MorphismProperty.Over.w
                ((MorphismProperty.Over.pullback @Etale ⊤ f).map t)).symm).inv.app F)))

set_option backward.isDefEq.respectTransparency true in
/-- Additivity of the prescribed derived-adjunction class construction.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-raw-restricted-normalization-data).
Proof: precomposition with the exact inverse-image single comparison is additive;
the derived adjunction is an additive Hom equivalence; zeroth homology and the
shift comparison are additive. Evaluation at the fixed identity generator is
additive as well. Their composite therefore preserves sums (proof step 6). -/
theorem normalizationClass_add {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale)
    (z z' : (abelianHigherDirectImageRawPresheaf f q F).obj (op V)) :
    abelianHigherDirectImageClass f q F V (z + z') =
      abelianHigherDirectImageClass f q F V z + abelianHigherDirectImageClass f q F V z' := by
  let c := toSheafify S.smallEtaleTopology (abelianHigherDirectImageRawPresheaf f q F) ≫
    (canonicalComparison f q F).hom.hom
  have h := (c.app (op V)).hom.map_add z z'
  change (toSheafify S.smallEtaleTopology _ ≫
      (canonicalComparison f q F).hom.hom).app (op V) (z + z') =
    (toSheafify S.smallEtaleTopology _ ≫
      (canonicalComparison f q F).hom.hom).app (op V) z +
    (toSheafify S.smallEtaleTopology _ ≫
      (canonicalComparison f q F).hom.hom).app (op V) z' at h
  simpa only [canonicalComparison_class] using h

/-- Bundle the existing canonical class function as an abelian-group morphism.
Its value is exactly abelianHigherDirectImageClass, without selecting a map from
an existence theorem.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationKappaComponent {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale) :
    (abelianHigherDirectImageRawPresheaf f q F).obj (op V) ⟶
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.obj (op V) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (abelianHigherDirectImageClass f q F V)
    (normalizationClass_add f q F V))

set_option backward.isDefEq.respectTransparency true in
/-- Naturality in etale objects of the prescribed canonical class map.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-raw-restricted-normalization-data).
Proof: the free represented map sends the identity generator at V' to the
restriction of the generator at V. Naturality of the single comparison and the
derived adjunction turns precomposition by this map into precomposition of its
adjunct. Zeroth homology and the shift comparison preserve this equality;
evaluating the restricted generator gives the restriction of the original class.
This is the generator calculation of proof steps 4 and 6. -/
theorem normalizationKappaComponent_naturality {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etaleᵒᵖ} (t : V ⟶ V') :
    (abelianHigherDirectImageRawPresheaf f q F).map t ≫
        normalizationKappaComponent f q F V'.unop =
      normalizationKappaComponent f q F V.unop ≫
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.map t := by
  let c := toSheafify S.smallEtaleTopology (abelianHigherDirectImageRawPresheaf f q F) ≫
    (canonicalComparison f q F).hom.hom
  have hc (U : S.Etale) : normalizationKappaComponent f q F U = c.app (op U) := by
    ext z
    exact (canonicalComparison_class f q F U z).symm
  rw [hc, hc]
  exact c.naturality t

/-- The presheaf class map with components given by the landed canonical class
construction, using its separately stated naturality.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationKappa {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    abelianHigherDirectImageRawPresheaf f q F ⟶
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj where
  app V := normalizationKappaComponent f q F V.unop
  naturality _ _ t := normalizationKappaComponent_naturality f q F t

/-- The unique sheafification lift of the specified raw class map.
Source: Stacks Project, Tag 03Q8 and the sheafification adjunction
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable def normalizationLift {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (abelianHigherDirectImageRawPresheaf f q F) ⟶
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  ((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (normalizationKappa f q F)

/-- The coefficient map on the raw derived-Hom presheaf.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable abbrev normalizationRawCoefficient {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    abelianHigherDirectImageRawPresheaf f q F ⟶ abelianHigherDirectImageRawPresheaf f q G :=
  Functor.whiskerLeft _ (preadditiveYoneda.map
    ((shiftFunctor _ (q : ℤ)).map ((DerivedCategory.Plus.singleFunctor _ 0).map φ)))

/-- The coefficient map on restricted derived cohomology.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable abbrev normalizationRestrictedCoefficient {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (V : S.Etale) :
    rawAffineRestrictedCohomology f q F V ⟶ rawAffineRestrictedCohomology f q G V :=
  (cohomology AddCommGrpCat.{u + 1} (pullback V.hom f) (q : ℤ)).map
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
      ((upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).map φ)))

/-- The coefficient map on higher direct images.
Source: Stacks Project, Tag 03Q8
(blueprint: def-weil-pbc-raw-restricted-normalization-data). -/
noncomputable abbrev normalizationHigherCoefficient {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) :=
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    (R+((f)_*[AddCommGrpCat.{u + 1}]).map ((DerivedCategory.Plus.singleFunctor _ 0).map φ))

end AlgebraicGeometry.Etale
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization | F2 | Publicly reexports the prescribed construction block and proves its theorem from the independent comparison lemmas. |
| Sheaf.AlgebraicGeometry.RawRestrictedResolutionNaturality | F2 | New theorem consumer; uses the same constructed resolution comparison. |
| Sheaf.AlgebraicGeometry.RawRestrictedResolutionRestriction | F2 | New theorem consumer; uses the same chart and cohomology restriction maps. |
| Sheaf.AlgebraicGeometry.RawRestrictedResolutionClass | F2 | New theorem consumer; uses the same cocycle-class construction. |

`tools/downstream.py Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization --uses normalizationRestrictedIso` reports zero downstream modules and the item itself as the sole user. A repository-wide search for all normalization declaration names agrees. There are no forced adaptations and no target signature changes.

## Status

landed 20261022T011833-L-3222256 2026-10-22 (merge of deliver/F2/Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization)
