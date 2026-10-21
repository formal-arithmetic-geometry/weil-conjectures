module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.AlgebraicGeometry.RawRestrictedResolutionEvaluation
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
public import
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
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

/-- The restricted augmentation, with the single-complex comparison.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization). -/
noncomputable def normalizationRestrictionAugmentation {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} W.hom).obj F) ⟶
        normalizationRestrictionComplex W F I :=
  ((upperStar AddCommGrpCat.{u + 1} W.hom).mapCochainComplexSingleFunctor 0).inv.app F ≫
    ((upperStar AddCommGrpCat.{u + 1} W.hom).mapHomologicalComplex (.up ℤ)).map I.ι'

/-- Exact restriction preserves the augmentation quasi-isomorphism.
Source: Stacks Project, Tags 03Q8 and 072W
(blueprint: lem-weil-pbc-raw-restricted-class-normalization).
Proof: the augmentation is a quasi-isomorphism, inverse image is exact, and its
single-complex comparison is an isomorphism (step 1 of the node's proof). -/
theorem normalizationRestrictionAugmentation_quasiIso {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    QuasiIso (normalizationRestrictionAugmentation W F I) := by
  sorry

/-- The restricted resolution is K-injective.
Source: Stacks Project, Tags 03Q8, 072W and 070J
(blueprint: lem-weil-pbc-raw-restricted-class-normalization).
Proof: etale restriction preserves injective abelian sheaves by
lem-sbc-etale-abelian-restriction-injectives. The restricted resolution is zero
in negative degrees, so the bounded-below injective criterion applies (step 1). -/
theorem normalizationRestrictionComplex_isKInjective {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (normalizationRestrictionComplex W F I).IsKInjective := by
  sorry

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
  sorry

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
  sorry

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

/-- Raw evaluation is an isomorphism of presheaves, and its class in the higher
direct image is exactly the canonical cocycle class. The specified sheafification
lift is invertible, and all comparisons commute with coefficient morphisms.
Source: Stacks Project, Tags 03Q8 and 072W; agent expansion of the class calculation
(blueprint: lem-weil-pbc-raw-restricted-class-normalization).

Proof:
1. Resolve F by a bounded-below complex I of injective abelian sheaves.
Etale inverse image is exact and preserves injectives, so its restriction is a
K-injective resolution. The restriction/sections isomorphism identifies its
sections complex with I evaluated at the etale fibre product.
2. By the K-injective Hom comparison, a raw derived class is represented by a
chain map from the single free represented inverse image to I[q]. Its degree-zero
component evaluated at the pulled-back identity generator is a section cycle s.
3. The resolution evaluation equality of lem-sbc-raw-restricted-resolution-evaluation
and chainEvaluation of lem-sbc-raw-restricted-homotopy-sections-iso say that the
specified raw evaluation is the class of s. The homology shift comparison retains
the same class: the invertible sign changes neither cycles nor boundaries.
4. For a morphism of etale objects, free representability sends the identity
generator to the restricted generator. Its ordinary adjunct therefore evaluates
to the restriction of s. Etale cohomology pullback, inverse-image composition and
restriction/sections comparisons give that same restricted cocycle. This proves
presheaf naturality and the equality with the cohomology restriction map.
5. The theorem lem-sbc-raw-restricted-cohomology-comparison-is-iso makes every
component invertible. Their inverses are natural by cancelling the component maps.
6. The derived inverse-image adjunction on I[q] is represented by the ordinary
termwise adjunction: counit naturality and the triangle identity identify the
adjunct of the representative. Zeroth homology, the direct-image shift comparison
and the identity generator give exactly the cohomology-sheaf class of s.
7. Apply lem-weil-pbc-site-higher-direct-image-sheafified-presheaf to the etale
base-change continuous functor, with its exact inverse image. Its canonical cocycle
map sends the class of s to that same section. Sheafify the presheaf evaluation
isomorphism; the canonical site comparison is invertible. Sheafification uniqueness
identifies their composite with normalizationLift, so that lift is invertible.
8. Represent a coefficient morphism by a chain map I to I'. Each construction sends
s to its image under that map. Homotopic choices differ by boundaries. Thus the
raw evaluation, cocycle class, raw class map and sheafification lift commute with
coefficients. The argument includes q = 0 and the empty fibre product. -/
theorem rawRestrictedClassNormalization {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (∃ c : abelianHigherDirectImageRawPresheaf f q F ≅
      normalizationRestrictedPresheaf f q F,
      ∀ V : S.Etale, c.hom.app (op V) = rawRestrictedCohomologyComparison f q F V) ∧
    (∀ (V V' : S.Etale) (t : V' ⟶ V),
      (normalizationRestrictedPresheaf f q F).map t.op =
        normalizationCohomologyRestriction f q F t) ∧
    (∀ (V : S.Etale) (z : (abelianHigherDirectImageRawPresheaf f q F).obj (op V)),
      (normalizationKappa f q F).app (op V) z = abelianHigherDirectImageClass f q F V z) ∧
    IsIso (normalizationLift f q F) ∧
    (∀ (V : S.Etale) (z : (abelianHigherDirectImageRawPresheaf f q F).obj (op V)),
      normalizationIota f q F V (rawRestrictedCohomologyComparison f q F V z) =
        abelianHigherDirectImageClass f q F V z) ∧
    (∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ G),
      (∀ V : S.Etale,
        (normalizationRawCoefficient f q φ).app (op V) ≫
            rawRestrictedCohomologyComparison f q G V =
          rawRestrictedCohomologyComparison f q F V ≫
            normalizationRestrictedCoefficient f q φ V) ∧
      (∀ V : S.Etale,
        normalizationRestrictedCoefficient f q φ V ≫ normalizationIota f q G V =
          normalizationIota f q F V ≫ (normalizationHigherCoefficient f q φ).hom.app (op V)) ∧
      (normalizationRawCoefficient f q φ ≫ normalizationKappa f q G =
        normalizationKappa f q F ≫ (normalizationHigherCoefficient f q φ).hom) ∧
      ((presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (normalizationRawCoefficient f q φ) ≫ normalizationLift f q G =
        normalizationLift f q F ≫ normalizationHigherCoefficient f q φ)) := by
  sorry

end AlgebraicGeometry.Etale
