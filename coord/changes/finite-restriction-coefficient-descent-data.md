# FiniteRestrictionCoefficient rational descent data

## Reason

The two proof steps for integral construction and rational descent must be separate
modules. Rational descent needs the existing RationalComparisons and DirectImageDescent
interfaces, which previously lived alongside the main theorem. Moving these definitions
into a public data module permits the main theorem to import that proof step without
an import cycle. All fully qualified names, types, visibility, and defining terms are
preserved; only the owning module and blueprint docstring tags change. This is an
interface relocation, with no change to any mathematical statement or definition.

## Old

In lean/Sheaf/Paper/FiniteRestrictionCoefficientDescent.lean:

```lean
set_option genSizeOf false in
set_option genInjectivity false in
/-- The raw rational diagram on the prescribed stage system. Morphism and Hom
records retain the associator and the compatibility of both actual arrows.
Localization is normalized on every integral object and every tensor morphism.
Source: Bhatt--Scholze 6.8.14; common-stage quotient construction
(blueprint: lem-zl-finite-restriction-coefficient-descent). -/
structure RationalComparisons (I : IntegralComparisons l f y Ω) where
  diagram : Vertex → (stageSystem l Ω X).Morphism (stageSystem l Ω s)
  exchange : StageSystem.Morphism.Hom (diagram .source) (diagram .middle)
  restriction : StageSystem.Morphism.Hom (diagram .middle) (diagram .target)
  objects : ∀ (q : Vertex) (A : Index l Ω) (K : Stage l Ω X A),
    ((diagram q).Φ A).obj K = ⟨((I.diagram A).functor q).obj K.obj⟩
  maps : ∀ (q : Vertex) (A : Index l Ω) (K M : IntegralStage l Ω X A)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω A)))
    (g : K ⟶ M),
    HEq (((diagram q).Φ A).map
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω A)] g :
        (localization l Ω X A).obj K ⟶ (localization l Ω X A).obj M))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω A)]
        ((I.diagram A).functor q).map g :
          (localization l Ω s A).obj (((I.diagram A).functor q).obj K) ⟶
            (localization l Ω s A).obj (((I.diagram A).functor q).obj M))
  exchange_components : ∀ (A : Index l Ω) (K : IntegralStage l Ω X A),
    HEq ((exchange.τ A).app ((localization l Ω X A).obj K))
      ((localization l Ω s A).map ((I.diagram A).exchange.app K))
  restriction_components : ∀ (A : Index l Ω) (K : IntegralStage l Ω X A),
    HEq ((restriction.τ A).app ((localization l Ω X A).obj K))
      ((localization l Ω s A).map ((I.diagram A).restriction.app K))
  scalar_components : ∀ (q : Vertex) (A B : Index l Ω) (h : A ≤ B)
    (K : IntegralStage l Ω X A),
    HEq (((diagram q).β h).hom.app ((localization l Ω X A).obj K))
      ((localization l Ω s B).map ((I.beta q A B h).hom.app K))

/-- Both descended maps are constructed by the existing representative quotient,
so they carry the same finite-stage components, including identities and composition.
Source: Bhatt--Scholze 6.8.14
(blueprint: lem-zl-finite-restriction-coefficient-descent). -/
def RationalComparisons.descendedExchange {I : IntegralComparisons l f y Ω}
    (R : RationalComparisons l f y Ω I) :=
  CategoryTheory.StageSystem.Morphism.descNatTrans R.exchange

/-- The descended counit restriction is the specified compatible family, not a
newly chosen arrow between isomorphic functors.
Source: Bhatt--Scholze 6.8.14
(blueprint: lem-zl-finite-restriction-coefficient-descent). -/
def RationalComparisons.descendedRestriction {I : IntegralComparisons l f y Ω}
    (R : RationalComparisons l f y Ω I) :=
  CategoryTheory.StageSystem.Morphism.descNatTrans R.restriction



/-- Exact sections use the specified inverse sections-tensor comparison, naturally
on every integral arrow, and the prescribed rational fibre comparison.
Source: Bhatt--Scholze 6.8.14; point-section scalar normalization
(blueprint: lem-zl-finite-restriction-coefficient-descent). -/
def SectionsCompatible (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) : Prop :=
  (∀ (A B : Index l Ω) (h : A ≤ B)
    (M N : IntegralStage l Ω (Spec (.of D.k)) A) (g : M ⟶ N),
    (pointCompletedDerivedSections D.k l (Coefficient.{u} l Ω B)).map
        ((integralScalarExtension l (Coefficient.{u} l Ω A) (Coefficient.{u} l Ω B)
          (coefficientInclusion l Ω A B h) (Spec (.of D.k))).map g.hom) ≫
        (pointSectionsScalarExtensionIso l (Coefficient.{u} l Ω A) (Coefficient.{u} l Ω B)
          (coefficientInclusion l Ω A B h) D hl N.obj
          ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω A) D hl N.obj).mpr
            N.property)).hom =
      (pointSectionsScalarExtensionIso l (Coefficient.{u} l Ω A) (Coefficient.{u} l Ω B)
        (coefficientInclusion l Ω A B h) D hl M.obj
        ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω A) D hl M.obj).mpr
          M.property)).hom ≫
        (pointIntegralModuleDerivedTensor l (Coefficient.{u} l Ω A)
          (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h)).map
          ((pointCompletedDerivedSections D.k l (Coefficient.{u} l Ω A)).map g.hom)) ∧
  (∀ (A B : Index l Ω) (h : A ≤ B)
    (M N : Stage l Ω (Spec (.of D.k)) A) (g : M ⟶ N),
    ((transition l Ω (Spec (.of D.k)) A B h) ⋙
        pointRationalFibre D l hl (Coefficient.{u} l Ω B)).map g ≫
        (pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω A)
          (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h)).hom.app N =
      (pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω A)
        (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h)).hom.app M ≫
        (pointRationalFibre D l hl (Coefficient.{u} l Ω A) ⋙
          DerivedCategory.pointFdScalarExtension
            (coefficientInclusion l Ω A B h).toRingHom).map g)

/-- The stagewise rational direct image descends with exactly its normalized
scalar comparisons; its standard pair and heart retain stagewise exactness.
Source: Bhatt--Scholze 6.8.14, 6.8.15
(blueprint: lem-zl-finite-restriction-coefficient-descent). -/
def DirectImageDescent (G : Geometry l Ω f y) : Prop :=
  ∃ F : (stageSystem l Ω X).Morphism (stageSystem l Ω Y),
    (∀ A : Index l Ω, F.Φ A = G.rationalImage.rational A) ∧
    (∀ (A B : Index l Ω) (h : A ≤ B), HEq (F.β h)
      (G.rationalImage.theta A B h).symm) ∧
    TExactDescent l Ω X F ∧ HeartExactDescent l Ω X F

```

## New

In lean/Sheaf/Paper/FiniteRestrictionCoefficientDescentData.lean, publicly reexported by
the original module:

```lean
set_option genSizeOf false in
set_option genInjectivity false in
/-- The raw rational diagram on the prescribed stage system. Morphism and Hom
records retain the associator and the compatibility of both actual arrows.
Localization is normalized on every integral object and every tensor morphism.
Source: Bhatt--Scholze 6.8.14; common-stage quotient construction
(blueprint: def-zl-finite-restriction-coefficient-descent-data). -/
structure RationalComparisons (I : IntegralComparisons l f y Ω) where
  diagram : Vertex → (stageSystem l Ω X).Morphism (stageSystem l Ω s)
  exchange : StageSystem.Morphism.Hom (diagram .source) (diagram .middle)
  restriction : StageSystem.Morphism.Hom (diagram .middle) (diagram .target)
  objects : ∀ (q : Vertex) (A : Index l Ω) (K : Stage l Ω X A),
    ((diagram q).Φ A).obj K = ⟨((I.diagram A).functor q).obj K.obj⟩
  maps : ∀ (q : Vertex) (A : Index l Ω) (K M : IntegralStage l Ω X A)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω A)))
    (g : K ⟶ M),
    HEq (((diagram q).Φ A).map
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω A)] g :
        (localization l Ω X A).obj K ⟶ (localization l Ω X A).obj M))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω A)]
        ((I.diagram A).functor q).map g :
          (localization l Ω s A).obj (((I.diagram A).functor q).obj K) ⟶
            (localization l Ω s A).obj (((I.diagram A).functor q).obj M))
  exchange_components : ∀ (A : Index l Ω) (K : IntegralStage l Ω X A),
    HEq ((exchange.τ A).app ((localization l Ω X A).obj K))
      ((localization l Ω s A).map ((I.diagram A).exchange.app K))
  restriction_components : ∀ (A : Index l Ω) (K : IntegralStage l Ω X A),
    HEq ((restriction.τ A).app ((localization l Ω X A).obj K))
      ((localization l Ω s A).map ((I.diagram A).restriction.app K))
  scalar_components : ∀ (q : Vertex) (A B : Index l Ω) (h : A ≤ B)
    (K : IntegralStage l Ω X A),
    HEq (((diagram q).β h).hom.app ((localization l Ω X A).obj K))
      ((localization l Ω s B).map ((I.beta q A B h).hom.app K))

/-- Both descended maps are constructed by the existing representative quotient,
so they carry the same finite-stage components, including identities and composition.
Source: Bhatt--Scholze 6.8.14
(blueprint: def-zl-finite-restriction-coefficient-descent-data). -/
def RationalComparisons.descendedExchange {I : IntegralComparisons l f y Ω}
    (R : RationalComparisons l f y Ω I) :=
  CategoryTheory.StageSystem.Morphism.descNatTrans R.exchange

/-- The descended counit restriction is the specified compatible family, not a
newly chosen arrow between isomorphic functors.
Source: Bhatt--Scholze 6.8.14
(blueprint: def-zl-finite-restriction-coefficient-descent-data). -/
def RationalComparisons.descendedRestriction {I : IntegralComparisons l f y Ω}
    (R : RationalComparisons l f y Ω I) :=
  CategoryTheory.StageSystem.Morphism.descNatTrans R.restriction



/-- Exact sections use the specified inverse sections-tensor comparison, naturally
on every integral arrow, and the prescribed rational fibre comparison.
Source: Bhatt--Scholze 6.8.14; point-section scalar normalization
(blueprint: def-zl-finite-restriction-coefficient-descent-data). -/
def SectionsCompatible (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) : Prop :=
  (∀ (A B : Index l Ω) (h : A ≤ B)
    (M N : IntegralStage l Ω (Spec (.of D.k)) A) (g : M ⟶ N),
    (pointCompletedDerivedSections D.k l (Coefficient.{u} l Ω B)).map
        ((integralScalarExtension l (Coefficient.{u} l Ω A) (Coefficient.{u} l Ω B)
          (coefficientInclusion l Ω A B h) (Spec (.of D.k))).map g.hom) ≫
        (pointSectionsScalarExtensionIso l (Coefficient.{u} l Ω A) (Coefficient.{u} l Ω B)
          (coefficientInclusion l Ω A B h) D hl N.obj
          ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω A) D hl N.obj).mpr
            N.property)).hom =
      (pointSectionsScalarExtensionIso l (Coefficient.{u} l Ω A) (Coefficient.{u} l Ω B)
        (coefficientInclusion l Ω A B h) D hl M.obj
        ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω A) D hl M.obj).mpr
          M.property)).hom ≫
        (pointIntegralModuleDerivedTensor l (Coefficient.{u} l Ω A)
          (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h)).map
          ((pointCompletedDerivedSections D.k l (Coefficient.{u} l Ω A)).map g.hom)) ∧
  (∀ (A B : Index l Ω) (h : A ≤ B)
    (M N : Stage l Ω (Spec (.of D.k)) A) (g : M ⟶ N),
    ((transition l Ω (Spec (.of D.k)) A B h) ⋙
        pointRationalFibre D l hl (Coefficient.{u} l Ω B)).map g ≫
        (pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω A)
          (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h)).hom.app N =
      (pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω A)
        (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h)).hom.app M ≫
        (pointRationalFibre D l hl (Coefficient.{u} l Ω A) ⋙
          DerivedCategory.pointFdScalarExtension
            (coefficientInclusion l Ω A B h).toRingHom).map g)

/-- The stagewise rational direct image descends with exactly its normalized
scalar comparisons; its standard pair and heart retain stagewise exactness.
Source: Bhatt--Scholze 6.8.14, 6.8.15
(blueprint: def-zl-finite-restriction-coefficient-descent-data). -/
def DirectImageDescent (G : Geometry l Ω f y) : Prop :=
  ∃ F : (stageSystem l Ω X).Morphism (stageSystem l Ω Y),
    (∀ A : Index l Ω, F.Φ A = G.rationalImage.rational A) ∧
    (∀ (A B : Index l Ω) (h : A ≤ B), HEq (F.β h)
      (G.rationalImage.theta A B h).symm) ∧
    TExactDescent l Ω X F ∧ HeartExactDescent l Ω X F

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteRestrictionCoefficientDescent | C4 | Publicly imports the new data module; all old names and terms remain available. |

The downstream.py --uses checks for RationalComparisons, SectionsCompatible,
DirectImageDescent, descendedExchange, and descendedRestriction find only the item
module itself. No consumer adaptation is needed. Target statements and the meanings of
the definitions they use are unchanged. The node attachments now record the new owning
module, while the main theorem remains attached to its original module and node.

## Status

landed 20261025T122609-L-1789509 2026-10-25 (merge of deliver/C4/Sheaf.Paper.FiniteRestrictionCoefficientDescent)
