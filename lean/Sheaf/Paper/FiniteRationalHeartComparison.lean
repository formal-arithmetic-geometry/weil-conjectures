/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.ConstructiblePullbackTExact
public import Sheaf.Paper.PbcRationalTransport
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.IntegralPullbackSystemComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Sheaf.Paper.LocalizedTStructure
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.Paper.IntegralPullbackCompletedComparison
import Sheaf.Paper.PointProEtaleSectionsExactOfUniverses
import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Rational hearts and the specified finite-fibre restrictions

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15;
Weil blueprint, proof of lem-zl-finite-pushforward, exactness and stalks
(blueprint: lem-zl-finite-rational-heart-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TensorProduct
namespace WeilConjectures.FiniteRationalHeart

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The integral pullback with the residue-unit instances supplied by the finite-field
convention. Source: BS 6.5.9, 6.8.15
(blueprint: lem-zl-finite-rational-heart-comparison). -/
abbrev pull {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (g : X ⟶ Y) :=
  @constructibleIntegralPullback l _ E _ _ _ X Y g
    (constructiblePullbackResidueUnits D l hl X)
    (constructiblePullbackResidueUnits D l hl Y)

/-- The unique raw extension, keeping integral objects and extending Hom scalars.
Source: BS 6.8.14(2) (blueprint: lem-zl-finite-rational-heart-comparison). -/
abbrev extension {X Y : Scheme.{u}}
    (T : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    [T.Additive] [T.Linear (Padic.coefficientExtensionIntegers l E)] :=
  ScalarLocalization.transport (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E) T

/-- The two full integral presentations agree through the already normalized coefficient
transport; their rational comparison keeps these objects and tensors the same arrows.
Source: BS 6.8.11(3), 6.8.14(2)
(blueprint: lem-zl-finite-rational-heart-comparison).
Proof: finite-type schemes over k are Noetherian and finite dimensional, and l is a
unit. Apply integralStratifiedPerfectDetailed to identify the predicates through
integralDetailedTransport. This coefficient equivalence is fixed by every quotient
projection, so it restricts to the full subcategories. Its raw rationalization acts on
pure tensors by the displayed formula; the inverse has the inverse coefficient formula.
Images of integral triangles give the same rational triangulation. The localized
standard classes are their isomorphism closures. Localized truncation identifies every
rational heart object with the localization of an integral heart object. -/
theorem categories (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))] :
    (∀ K : DerivedCategory (scalarReductionSource l E W),
      sfIntegralConstructible l E W K ↔
        PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E)
          ((integralDetailedTransport W l E).obj K)) ∧
    (∃ J : sfIntegralConstructibleCategory l E W ≌
        PbcBoundedConstructibleComplete W (pbcIntegralDatum l E),
      (∀ K, (J.functor.obj K).obj = (integralDetailedTransport W l E).obj K.obj) ∧
      (∀ (K L : sfIntegralConstructibleCategory l E W) (a : K ⟶ L),
        HEq (J.functor.map a).hom ((integralDetailedTransport W l E).map a.hom)) ∧
      ∃ JE : sfRationalConstructibleCategory l E W ≌
          PbcRationalCategory W (pbcIntegralDatum l E) (pbcUniformizer l E),
        (∀ K, JE.functor.obj K = ⟨J.functor.obj K.obj⟩) ∧
        (∀ (K L : sfIntegralConstructibleCategory l E W) (a : K ⟶ L)
          (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
          HEq (JE.functor.map (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a :
            (sfRationalConstructibleLocalization l E W).obj K ⟶
              (sfRationalConstructibleLocalization l E W).obj L))
            ((pbcRationalCoefficientEquiv l E).symm (sfRationalCoefficientEquiv l E c)
              ⊗ₜ[PbcIntegralRing l E] J.functor.map a))) ∧
    (∀ (b : Bool) (n : ℤ) (K : sfIntegralConstructibleCategory l E W),
      sfIntegralStandardClass l E W b n K →
        sfRationalStandardClass l E W b n
          ((sfRationalConstructibleLocalization l E W).obj K)) ∧
    (∀ F : sfRationalHeart l E W,
      ∃ K : sfIntegralConstructibleCategory l E W,
        sfIntegralStandardClass l E W true 0 K ∧
        sfIntegralStandardClass l E W false 0 K ∧
        Nonempty (F.obj ≅ (sfRationalConstructibleLocalization l E W).obj K)) := by
  sorry

/-- The ring identification respects the actual finite reductions and exact scalar
restriction, rather than replacing the completed ring by an unspecified isomorphic one.
Source: BS 6.5.1, 6.8.11(3)
(blueprint: lem-zl-finite-rational-heart-comparison).
Proof: the canonical finite-level coefficient comparisons commute with transition
maps. The two completions are limits of this identified system; the limit universal
property gives the stated projection equations. Restriction along a ring isomorphism
has inverse restriction along its inverse, and is exact on underlying module sheaves. -/
theorem coefficients (W : Scheme.{u}) :
    (∀ n : ℕ,
      (integralDetailedCoefficientComparison W l E).hom ≫
          limit.π (integralCoefficientSheafSystem l E W) (Opposite.op n) =
        (adicLisseForget W).map
            (pbcAdicProjection W (pbcIntegralDatum l E) n) ≫
          (integralDetailedLevelComparison W l E n).hom) ∧
    PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison W l E).hom) ∧
    PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison W l E).hom) := by
  sorry

/-- The finite-coefficient adjunction with its actual sectionwise right adjoint.
Source: Stacks 03D3, 07A6 (blueprint: lem-zl-finite-rational-heart-comparison). -/
def finiteAdj {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f ⊣
      proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  (((proEtaleConstantRingAdjunction (Padic.coefficientExtensionRing l E (n + 1)) f).ofNatIsoRight
    (proEtaleUnitLerayDirectImageIso
      (Padic.coefficientExtensionRing l E (n + 1)) f)).mapDerivedCategoryRightDerivedAdjunction)


/-- Finite exchange, the transpose of pullback of the counit through the canonical
composition comparisons of pur713-def-pullback-comparison. Source: Stacks 0959, 07A7
(blueprint: lem-zl-finite-rational-heart-comparison). -/
def finiteExchange {X Y S s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (v : S ⟶ X) (h : S ⟶ s) (w : v ≫ f = h ≫ y) (n : ℕ)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))) :
    (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) y).obj
      ((proEtaleConstantDerivedDirectImage f
        (Padic.coefficientExtensionRing l E (n + 1))).obj K) ⟶
    (proEtaleConstantDerivedDirectImage h
      (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) v).obj K) :=
  ((finiteAdj l E h n).homEquiv _ _)
    ((proEtaleConstantRingPullbackComposition h y
        (Padic.coefficientExtensionRing l E (n + 1))).hom.app
        ((proEtaleConstantDerivedDirectImage f
          (Padic.coefficientExtensionRing l E (n + 1))).obj K) ≫
      (eqToIso (congrArg (fun g ↦ (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) g).obj
          ((proEtaleConstantDerivedDirectImage f
            (Padic.coefficientExtensionRing l E (n + 1))).obj K)) w.symm)).hom ≫
      (proEtaleConstantRingPullbackComposition v f
        (Padic.coefficientExtensionRing l E (n + 1))).inv.app
        ((proEtaleConstantDerivedDirectImage f
          (Padic.coefficientExtensionRing l E (n + 1))).obj K) ≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) v).map
          ((finiteAdj l E f n).counit.app K))


/-- The finite counit-germ restriction to a specified geometric lift.
Source: Stacks 03QP(1) (blueprint: lem-zl-finite-rational-heart-comparison). -/
def finiteGerm {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
    (x : s ⟶ X) (w : x ≫ f = y) (n : ℕ)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))) :
    (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) y).obj
      ((proEtaleConstantDerivedDirectImage f
        (Padic.coefficientExtensionRing l E (n + 1))).obj K) ⟶
    (proEtaleConstantRingDerivedPullback
      (Padic.coefficientExtensionRing l E (n + 1)) x).obj K :=
  (eqToIso (congrArg (fun g ↦ (proEtaleConstantRingDerivedPullback
    (Padic.coefficientExtensionRing l E (n + 1)) g).obj
      ((proEtaleConstantDerivedDirectImage f
        (Padic.coefficientExtensionRing l E (n + 1))).obj K)) w.symm)).hom ≫
    (proEtaleConstantRingPullbackComposition x f
      (Padic.coefficientExtensionRing l E (n + 1))).inv.app
      ((proEtaleConstantDerivedDirectImage f
        (Padic.coefficientExtensionRing l E (n + 1))).obj K) ≫
    (proEtaleConstantRingDerivedPullback
      (Padic.coefficientExtensionRing l E (n + 1)) x).map
        ((finiteAdj l E f n).counit.app K)


/-- The supplied integral identification with the strict direct-image tower. Each
projection is retained; `comparison` is required to intertwine it with the Roos one.
Source: BS 6.5, 6.8.15 (blueprint: lem-zl-finite-rational-heart-comparison). -/
structure TowerComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    (K : sfIntegralConstructibleCategory l E X) where
  [products : HasProduct (sfDirectImageTerm l E f K.obj)]
  tower : @SfIntegralDirectImage l _ E _ _ _ X Y f K.obj products
  projection : ∀ n : ℕ, (T.obj K).obj ⟶ sfDirectImageTerm l E f K.obj n
  comparison : (T.obj K).obj ≅ tower.obj
  normalized : ∀ n : ℕ,
    comparison.hom ≫ tower.projection ≫
      Pi.π (sfDirectImageTerm l E f K.obj) n = projection n


/-- Reduction of the supplied tower image, obtained by scalar adjunction from its
specified projection. Source: Stacks 07A6
(blueprint: lem-zl-finite-rational-heart-comparison). -/
def TowerComparison.reduction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {T : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y}
    {K : sfIntegralConstructibleCategory l E X} (c : TowerComparison l E f T K) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj (T.obj K).obj ⟶
      sfFiniteDerivedDirectImage l E f K.obj n :=
  ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
    (c.projection n)


/-- The fibre carries its actual second projection as structure morphism.
Source: base-change convention (blueprint: lem-zl-finite-rational-heart-comparison). -/
instance fibreOver {X Y s : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y) :
    (pullback f y).Over s := ⟨pullback.snd f y⟩

/-- Finite base change supplies the finite-type structure on the actual fibre.
Source: finite morphisms are of finite type
(blueprint: lem-zl-finite-rational-heart-comparison). -/
instance fibreFiniteType {X Y s : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (y : s ⟶ Y) :
    LocallyOfFiniteType (pullback f y ↘ s) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd f y))

/-- Finite base change is quasi-compact.
Source: finite morphisms (blueprint: lem-zl-finite-rational-heart-comparison). -/
instance fibreQuasiCompact {X Y s : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (y : s ⟶ Y) :
    QuasiCompact (pullback f y ↘ s) :=
  inferInstanceAs (QuasiCompact (pullback.snd f y))

/-- Finite base change is separated.
Source: finite morphisms (blueprint: lem-zl-finite-rational-heart-comparison). -/
instance fibreSeparated {X Y s : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (y : s ⟶ Y) :
    IsSeparated (pullback f y ↘ s) :=
  inferInstanceAs (IsSeparated (pullback.snd f y))

/-- Positive-level pullback reduction with exactly the residue-unit structures of `pull`:
the recorded canonical reduction comparison of def-sf-integral-pullback-reduction-comparison.
Source: BS 6.5.9(5) (blueprint: lem-zl-finite-rational-heart-comparison). -/
abbrev reduction {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (g : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (n : ℕ) :=
  @integralSystemPullbackReductionIso l _ E _ _ _ X Y g
    (constructiblePullbackResidueUnits D l hl X)
    (constructiblePullbackResidueUnits D l hl Y) K P e n

/-- All geometric lifts of y, with the commuting equation retained.
Source: finite stalk formula (blueprint: lem-zl-finite-rational-heart-comparison). -/
abbrev Lifts {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Spec (.of D.k) ⟶ Y) :=
  {x : Spec (.of D.k) ⟶ X // x ≫ f = y}

/-- Geometric lifts through a finite fibre form a finite set, including the empty fibre.
Source: BS 6.8.15; finite stalk formula
(blueprint: lem-zl-finite-rational-heart-comparison).
Proof: on an affine neighbourhood Spec B of y the inverse image is Spec C with C
finite over B. The fibre algebra C tensor_B k is finite dimensional and Artinian.
It has finitely many maximal ideals, all with residue field k since k is algebraically
closed. Its k-points are exactly the lifts in the displayed subtype, by the pullback
universal property. Thus this subtype is finite. -/
@[instance] theorem lifts_finite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y) : Finite (Lifts D f y) := by
  sorry

/-- The unique lift into the actual pullback, with second component the identity.
Source: base-change universal property
(blueprint: lem-zl-finite-rational-heart-comparison). -/
def lift {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Spec (.of D.k) ⟶ Y)
    (x : Lifts D f y) : Spec (.of D.k) ⟶ pullback f y :=
  pullback.lift x.val (𝟙 _) (x.property.trans (Category.id_comp y).symm)

/-- The lift has exactly its two stipulated projections, and is unique with them.
Source: pullback universal property
(blueprint: lem-zl-finite-rational-heart-comparison).
Proof: pullback.lift_fst and pullback.lift_snd give the equations; pullback.hom_ext
proves uniqueness from these two equations. -/
theorem lift_projections {A B : Scheme.{u}} (g : A ⟶ B)
    (z : Spec (.of D.k) ⟶ B) (x : Lifts D g z) :
    lift D g z x ≫ pullback.fst g z = x.val ∧
    lift D g z x ≫ pullback.snd g z = 𝟙 _ ∧
    ∀ j : Spec (.of D.k) ⟶ pullback g z,
      j ≫ pullback.fst g z = x.val → j ≫ pullback.snd g z = 𝟙 _ →
        j = lift D g z x := by
  sorry

/-- Sections on the coefficient point followed by degree zero, exactly as in the
recorded stalk and ordinary-cohomology conventions.
Source: BS 6.8.15 (blueprint: lem-zl-finite-rational-heart-comparison). -/
def pointH0 := pointRationalFibre D l hl E ⋙ DerivedCategory.coefficientFdCohomology E 0

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [IsFinite f] (y : Spec (.of D.k) ⟶ Y)

/-- The actual map on one restricted finite direct-image term.
Source: the tower direct-image definition
(blueprint: lem-zl-finite-rational-heart-comparison). -/
def termMap {A B : Scheme.{u}} (g : A ⟶ B)
    {K L : sfIntegralConstructibleCategory l E A} (a : K ⟶ L) (n : ℕ) :
    sfDirectImageTerm l E g K.obj n ⟶ sfDirectImageTerm l E g L.obj n :=
  (scalarReductionDerivedRestriction l E B n).map
    ((proEtaleConstantDerivedDirectImage g
      (Padic.coefficientExtensionRing l E (n + 1))).map
        ((scalarReductionDerivedExtension l E A n).map a.hom))

/-- The stipulated integral exchange and counit-germ restrictions. Normalization is
an equality of the actual reduced arrows, tested on every good representative.
Source: BS 6.8.14(2), 6.8.15; Stacks 0959, 03QP
(blueprint: lem-zl-finite-rational-heart-comparison). -/
structure Restrictions
    (T : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    (H : sfIntegralConstructibleCategory l E (pullback f y) ⥤
      sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (cT : ∀ K, TowerComparison l E f T K)
    (cH : ∀ K, TowerComparison l E (pullback.snd f y) H K) where
  tower_natural : ∀ (K L : sfIntegralConstructibleCategory l E X)
    (a : K ⟶ L) (n : ℕ),
    (T.map a).hom ≫ (cT L).projection n =
      (cT K).projection n ≫ termMap l E f a n
  fibre_tower_natural :
    ∀ (K L : sfIntegralConstructibleCategory l E (pullback f y)) (a : K ⟶ L) (n : ℕ),
      (H.map a).hom ≫ (cH L).projection n =
        (cH K).projection n ≫ termMap l E (pullback.snd f y) a n
  beta : T ⋙ pull D l hl E y ≅ pull D l hl E (pullback.fst f y) ⋙ H
  rho : ∀ K : sfIntegralConstructibleCategory l E X,
    H.obj ((pull D l hl E (pullback.fst f y)).obj K) ≅
      ⨁ fun x : Lifts D f y ↦ (pull D l hl E x.val).obj K
  rho_natural : ∀ (K L : sfIntegralConstructibleCategory l E X) (a : K ⟶ L),
    H.map ((pull D l hl E (pullback.fst f y)).map a) ≫ (rho L).hom =
      (rho K).hom ≫ biproduct.map (fun x : Lifts D f y ↦ (pull D l hl E x.val).map a)
  beta_reduction : ∀ (K : sfIntegralConstructibleCategory l E X)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ (T.obj K).obj)
    (Q : (integralOperationsGoodComplex l E X).FullSubcategory)
    (d : DerivedCategory.Q.obj Q.obj ≅ K.obj) (n : ℕ),
    (scalarReductionDerivedExtension l E (Spec (.of D.k)) n).map
        (beta.hom.app K).hom ≫
      TowerComparison.reduction l E
        (cH ((pull D l hl E (pullback.fst f y)).obj K)) n ≫
      (proEtaleConstantDerivedDirectImage (pullback.snd f y)
        (Padic.coefficientExtensionRing l E (n + 1))).map
          (reduction D l hl E (pullback.fst f y) K Q d n).hom =
    (reduction D l hl E y (T.obj K) P e n).hom ≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) y).map
          (TowerComparison.reduction l E (cT K) n) ≫
      finiteExchange l E f y (pullback.fst f y) (pullback.snd f y)
        pullback.condition n ((scalarReductionDerivedExtension l E X n).obj K.obj)
  rho_reduction : ∀ (K : sfIntegralConstructibleCategory l E X) (x : Lifts D f y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ (T.obj K).obj)
    (Q : (integralOperationsGoodComplex l E X).FullSubcategory)
    (d : DerivedCategory.Q.obj Q.obj ≅ K.obj) (n : ℕ),
    (scalarReductionDerivedExtension l E (Spec (.of D.k)) n).map
      ((beta.hom.app K) ≫ (rho K).hom ≫
        biproduct.π (fun z : Lifts D f y ↦ (pull D l hl E z.val).obj K) x).hom ≫
      (reduction D l hl E x.val K Q d n).hom =
    (reduction D l hl E y (T.obj K) P e n).hom ≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) y).map
          (TowerComparison.reduction l E (cT K) n) ≫
      finiteGerm l E f y x.val x.property n
        ((scalarReductionDerivedExtension l E X n).obj K.obj)

/-- The prescribed rational pullback with the finite-field residue-unit structures.
Source: rational pullback convention
(blueprint: lem-zl-finite-rational-heart-comparison). -/
abbrev rpull {A B : Scheme.{u}}
    [A.Over (Spec (.of D.k))] [B.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (A ↘ Spec (.of D.k))] [QuasiCompact (A ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of D.k))] [QuasiCompact (B ↘ Spec (.of D.k))]
    (g : A ⟶ B) :=
  @rationalDerivedPullback l _ E _ _ _ A B g
    (constructiblePullbackResidueUnits D l hl A)
    (constructiblePullbackResidueUnits D l hl B)

/-- Its recorded integral-object comparison, used to normalize the localized arrows.
Source: localPullbackObjectIso
(blueprint: lem-zl-finite-rational-heart-comparison). -/
abbrev pullIso {A B : Scheme.{u}}
    [A.Over (Spec (.of D.k))] [B.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (A ↘ Spec (.of D.k))] [QuasiCompact (A ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of D.k))] [QuasiCompact (B ↘ Spec (.of D.k))]
    (g : A ⟶ B) (K : sfRationalConstructibleCategory l E B) :=
  @localPullbackObjectIso l _ E _ _ _ A B g
    (constructiblePullbackResidueUnits D l hl A)
    (constructiblePullbackResidueUnits D l hl B) K

/-- The projections of precisely the Roos vertex used by ordinary cohomology.
Source: integralImage, Stacks 07A6
(blueprint: lem-zl-finite-rational-heart-comparison). -/
def ordinaryProjection (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    (K : sfIntegralConstructibleCategory l E W) (n : ℕ) :
    (integralImage D l hl E W K).obj ⟶ sfDirectImageTerm l E (W ↘ Spec (.of D.k)) K.obj n := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (W ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  let w := sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
    E (W ↘ Spec (.of D.k)) K.obj K.property
  letI := w.1.choose
  let L : SfIntegralDirectImage l E (W ↘ Spec (.of D.k)) K.obj := w.1.choose_spec.some
  exact L.projection ≫ Pi.π _ n

/-- The ordinary-image comparison retains every projection, so the middle object
cannot be replaced by an unrelated isomorphic complex.
Source: BS 6.5, ordinary cohomology convention
(blueprint: lem-zl-finite-rational-heart-comparison). -/
def OrdinaryComparison
    (H : sfIntegralConstructibleCategory l E (pullback f y) ⥤
      sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (cH : ∀ K, TowerComparison l E (pullback.snd f y) H K)
    (K : sfIntegralConstructibleCategory l E (pullback f y)) :=
  {c : H.obj K ≅ integralImage D l hl E (pullback f y) K //
    ∀ n : ℕ, c.hom.hom ≫ ordinaryProjection D l hl E (pullback f y) K n =
      (cH K).projection n}

/-- The actual ordinary-cohomology comparison after raw localization. Both endpoint
transports are the prescribed rational pullback object equality.
Source: ordinary cohomology and raw rationalization conventions
(blueprint: lem-zl-finite-rational-heart-comparison). -/
def ordinaryIso
    (H : sfIntegralConstructibleCategory l E (pullback f y) ⥤
      sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    [H.Additive] [H.Linear (Padic.coefficientExtensionIntegers l E)]
    (cH : ∀ K, TowerComparison l E (pullback.snd f y) H K)
    (c : ∀ K, OrdinaryComparison D l hl E f y H cH K)
    (K : sfRationalConstructibleCategory l E X) :
    (extension l E H).obj ((rpull D l hl E (pullback.fst f y)).obj K) ≅
      rationalImage D l hl E (pullback f y)
        ((rpull D l hl E (pullback.fst f y)).obj K) :=
  (extension l E H).mapIso (pullIso D l hl E (pullback.fst f y) K) ≪≫
    (sfRationalConstructibleLocalization l E (Spec (.of D.k))).mapIso
      (c ((pull D l hl E (pullback.fst f y)).obj K.obj)).val ≪≫
    eqToIso (congrArg (rationalImage D l hl E (pullback f y))
      ((@rationalDerivedPullback_existsUnique l _ E _ _ _ _ _ (pullback.fst f y)
        (constructiblePullbackResidueUnits D l hl (pullback f y))
        (constructiblePullbackResidueUnits D l hl X)).exists.choose_spec.2.1 K)).symm

/-- The map on the recorded ordinary H0 objects, transported through the comparison
that preserves all Roos projections. No independent ordinary-cohomology object is used.
Source: ordinaryImage convention, BS 6.8.15
(blueprint: lem-zl-finite-rational-heart-comparison). -/
def ordinaryMap
    (H : sfIntegralConstructibleCategory l E (pullback f y) ⥤
      sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    [H.Additive] [H.Linear (Padic.coefficientExtensionIntegers l E)]
    (cH : ∀ K, TowerComparison l E (pullback.snd f y) H K)
    (c : ∀ K, OrdinaryComparison D l hl E f y H cH K)
    {K L : sfRationalConstructibleCategory l E X} (a : K ⟶ L) :
    rationalOrdinaryCohomology D l hl E (pullback f y)
        ((rpull D l hl E (pullback.fst f y)).obj K) 0 ⟶
      rationalOrdinaryCohomology D l hl E (pullback f y)
        ((rpull D l hl E (pullback.fst f y)).obj L) 0 :=
  (pointH0 D l hl E).map (ordinaryIso D l hl E f y H cH c K).inv ≫
    ((rpull D l hl E (pullback.fst f y)) ⋙ extension l E H ⋙ pointH0 D l hl E).map a ≫
      (pointH0 D l hl E).map (ordinaryIso D l hl E f y H cH c L).hom

/-- The raw extension is uniquely determined, including its exact triangulated
structure with the localized supplied shift comparison.
Source: BS 6.8.14(2); ScalarLocalization.transport_exact
(blueprint: lem-zl-finite-rational-heart-comparison).
Proof: pure tensors generate every Hom. Linearity forces a tensor z ⊗ a to map to
z ⊗ T(a), and additivity handles sums, so transport_unique identifies any extension.
Localize the supplied shift comparison and every integral distinguished triangle.
The isomorphic-image definition of the localized triangulation gives exactness. -/
theorem raw_extension
    (T : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    [T.Additive] [T.Linear (Padic.coefficientExtensionIntegers l E)]
    [T.CommShift ℤ] [T.IsTriangulated] :
    (∀ (J : sfRationalConstructibleCategory l E X ⥤
        sfRationalConstructibleCategory l E Y) [J.Additive]
        [J.Linear (Localization.Away (Padic.coefficientExtensionUniformizer l E))],
      (∀ K : sfIntegralConstructibleCategory l E X,
        J.obj ((sfRationalConstructibleLocalization l E X).obj K) =
          (sfRationalConstructibleLocalization l E Y).obj (T.obj K)) →
      (∀ (K L : sfIntegralConstructibleCategory l E X) (a : K ⟶ L),
        HEq (J.map ((sfRationalConstructibleLocalization l E X).map a))
          ((sfRationalConstructibleLocalization l E Y).map (T.map a))) →
      J = extension l E T) ∧
    ∃ cs : (extension l E T).CommShift ℤ,
      (fun [comm : (extension l E T).CommShift ℤ] ↦
        (extension l E T).IsTriangulated ∧
        ∀ K : sfIntegralConstructibleCategory l E X,
          HEq (((extension l E T).commShiftIso (1 : ℤ)).hom.app
            ((sfRationalConstructibleLocalization l E X).obj K))
            ((sfRationalConstructibleLocalization l E Y).map
              ((T.commShiftIso (1 : ℤ)).hom.app K))) (comm := cs) := by
  sorry

/-- Exact point sections, standard-heart interpretation, and the actual finite
biproduct comparison. These retain the point coefficient convention and its scalar
normalization, also for an empty fibre.
Source: Stacks 0982, 098H; BS 6.8.14(2), 6.8.15
(blueprint: lem-zl-finite-rational-heart-comparison).
Proof: the coefficient point is weakly contractible, so evaluation at its final
object preserves epimorphisms and all kernels. Coefficient restriction is exact.
Localization at the uniformizer is flat: clearing a power of the uniformizer gives
cycle representatives for localized kernels, and images localize. Thus cohomology
commutes with sections and rationalization. For a standard-heart object all degrees
other than zero vanish. Apply the additive point functor to the finite biproduct
identities to obtain its canonical comparison isomorphism. The scalar formula in
pointRationalFibre and coefficient cohomology gives the displayed E-linearity. -/
theorem point_sections :
    PreservesFiniteLimits (pointIntegralSections l E D.k) ∧
    PreservesFiniteColimits (pointIntegralSections l E D.k) ∧
    (∀ (F : sfRationalHeart l E (Spec (.of D.k))) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.coefficientFdCohomology E j).obj
        ((pointRationalFibre D l hl E).obj F.obj))) ∧
    (∀ K : Lifts D f y → sfRationalConstructibleCategory l E (Spec (.of D.k)),
      ∃ hb : HasBiproduct ((pointRationalFibre D l hl E).obj ∘ K),
        (fun [bip : HasBiproduct ((pointRationalFibre D l hl E).obj ∘ K)] ↦
          IsIso (Functor.biproductComparison (pointRationalFibre D l hl E) K))
            (bip := hb) ∧
        IsIso (Functor.biproductComparison (pointH0 D l hl E) K)) ∧
    (∀ (K L : sfRationalConstructibleCategory l E (Spec (.of D.k)))
      (a : K ⟶ L) (z : E),
      (pointH0 D l hl E).map ((sfRationalCoefficientEquiv l E).symm z • a) =
        z • (pointH0 D l hl E).map a) := by
  sorry

/-- Raw rationalization, exact hearts, and the two specified finite-fibre arrows.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15;
blueprint proof of lem-zl-finite-pushforward
(blueprint: lem-zl-finite-rational-heart-comparison).
Proof: use categories to compare the integral and raw rational presentations.
ScalarLocalization.transport extends T on objects and tensors, uniquely by linearity.
The integral standard bounds imply rational t-exactness using integral representatives.
Exactness carries a triangle of heart terms to one of heart terms, hence gives an exact
heart functor. Localize the supplied beta and rho, including their actual components;
the displayed normalization equations record this operation. Uniqueness of the Roos
limit gives the ordinary comparison preserving each projection. Completed pullback
bounds apply to y, v and every x, so these have their heart interpretations. Point
sections are exact, and localization commutes with kernels and images by clearing a
power of the uniformizer. It therefore commutes with cohomology. The finite biproduct
identities survive these functors, including the empty sum. Apply pointH0 to the actual
localized beta and rho and use ordinaryIso to identify the middle with ordinary H0.
Their naturality squares hold on integral maps, and then on fractions by linearity.
The point scalar-action formula gives E-linearity of every displayed arrow. -/
theorem rational_heart_comparison
    (T : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    [T.Additive] [T.Linear (Padic.coefficientExtensionIntegers l E)]
    [T.CommShift ℤ] [T.IsTriangulated]
    (hT : ∀ (b : Bool) (n : ℤ) (K : sfIntegralConstructibleCategory l E X),
      sfIntegralStandardClass l E X b n K →
        sfIntegralStandardClass l E Y b n (T.obj K))
    (H : sfIntegralConstructibleCategory l E (pullback f y) ⥤
      sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    [H.Additive] [H.Linear (Padic.coefficientExtensionIntegers l E)]
    (cT : ∀ K, TowerComparison l E f T K)
    (cH : ∀ K, TowerComparison l E (pullback.snd f y) H K)
    (R : Restrictions D l hl E f y T H cT cH) :
    (∀ (b : Bool) (n : ℤ) (K : sfRationalConstructibleCategory l E X),
      sfRationalStandardClass l E X b n K →
        sfRationalStandardClass l E Y b n ((extension l E T).obj K)) ∧
    (rpull D l hl E y).IsTExact
      (sfRationalStandardTStructure l E Y D hl)
      (sfRationalStandardTStructure l E (Spec (.of D.k)) D hl) ∧
    (rpull D l hl E (pullback.fst f y)).IsTExact
      (sfRationalStandardTStructure l E X D hl)
      (sfRationalStandardTStructure l E (pullback f y) D hl) ∧
    (∀ x : Lifts D f y, (rpull D l hl E x.val).IsTExact
      (sfRationalStandardTStructure l E X D hl)
      (sfRationalStandardTStructure l E (Spec (.of D.k)) D hl)) ∧
    (∃ Fh : sfRationalHeart l E X ⥤ sfRationalHeart l E Y,
      Fh ⋙ (sfRationalHeartProperty l E Y).ι =
        (sfRationalHeartProperty l E X).ι ⋙ extension l E T ∧
      PreservesFiniteLimits Fh ∧ PreservesFiniteColimits Fh) ∧
    ∃ c : ∀ K, OrdinaryComparison D l hl E f y H cH K,
      ∃ βE : extension l E T ⋙ rpull D l hl E y ≅
          rpull D l hl E (pullback.fst f y) ⋙ extension l E H,
        ∃ ρE : ∀ K : sfRationalConstructibleCategory l E X,
            (extension l E H).obj ((rpull D l hl E (pullback.fst f y)).obj K) ≅
              ⨁ fun x : Lifts D f y ↦ (rpull D l hl E x.val).obj K,
          (∀ K : sfRationalConstructibleCategory l E X,
            βE.app K = pullIso D l hl E y ((extension l E T).obj K) ≪≫
              (sfRationalConstructibleLocalization l E (Spec (.of D.k))).mapIso
                (R.beta.app K.obj) ≪≫
              ((extension l E H).mapIso
                (pullIso D l hl E (pullback.fst f y) K)).symm) ∧
          (∀ (K : sfRationalConstructibleCategory l E X) (x : Lifts D f y),
            (ρE K).hom ≫
                biproduct.π (fun z : Lifts D f y ↦ (rpull D l hl E z.val).obj K) x ≫
                (pullIso D l hl E x.val K).hom =
              (extension l E H).map (pullIso D l hl E (pullback.fst f y) K).hom ≫
                (sfRationalConstructibleLocalization l E (Spec (.of D.k))).map
                  ((R.rho K.obj).hom ≫
                    biproduct.π
                      (fun z : Lifts D f y ↦ (pull D l hl E z.val).obj K.obj) x)) ∧
          (∀ (K L : sfRationalConstructibleCategory l E X) (a : K ⟶ L),
            (extension l E H).map ((rpull D l hl E (pullback.fst f y)).map a) ≫
                (ρE L).hom =
              (ρE K).hom ≫ biproduct.map
                (fun x : Lifts D f y ↦ (rpull D l hl E x.val).map a)) ∧
          ∃ a : ∀ F : sfRationalHeart l E X,
              (pointH0 D l hl E).obj
                  ((rpull D l hl E y).obj ((extension l E T).obj F.obj)) ≅
                rationalOrdinaryCohomology D l hl E (pullback f y)
                  ((rpull D l hl E (pullback.fst f y)).obj F.obj) 0,
            ∃ b : ∀ F : sfRationalHeart l E X,
                rationalOrdinaryCohomology D l hl E (pullback f y)
                    ((rpull D l hl E (pullback.fst f y)).obj F.obj) 0 ≅
                  ⨁ fun x : Lifts D f y ↦
                    (pointH0 D l hl E).obj ((rpull D l hl E x.val).obj F.obj),
              (∀ F : sfRationalHeart l E X,
                a F = (pointH0 D l hl E).mapIso (βE.app F.obj) ≪≫
                  (pointH0 D l hl E).mapIso (ordinaryIso D l hl E f y H cH c F.obj) ∧
                (b F).hom = (pointH0 D l hl E).map
                    (ordinaryIso D l hl E f y H cH c F.obj).inv ≫
                  (pointH0 D l hl E).map (ρE F.obj).hom ≫
                    Functor.biproductComparison (pointH0 D l hl E)
                      (fun x : Lifts D f y ↦ (rpull D l hl E x.val).obj F.obj)) ∧
              (∀ (F G : sfRationalHeart l E X) (r : F ⟶ G),
                ((extension l E T) ⋙ rpull D l hl E y ⋙ pointH0 D l hl E).map r.hom ≫
                    (a G).hom =
                  (a F).hom ≫ ordinaryMap D l hl E f y H cH c r.hom) ∧
              (∀ (F G : sfRationalHeart l E X) (r : F ⟶ G),
                ordinaryMap D l hl E f y H cH c r.hom ≫ (b G).hom =
                  (b F).hom ≫ biproduct.map
                    (fun x : Lifts D f y ↦
                      (rpull D l hl E x.val ⋙ pointH0 D l hl E).map r.hom)) ∧
              (∀ (F G : sfRationalHeart l E X) (r : F ⟶ G) (z : E),
                ordinaryMap D l hl E f y H cH c
                    ((sfRationalCoefficientEquiv l E).symm z • r.hom) =
                  z • ordinaryMap D l hl E f y H cH c r.hom) := by
  sorry

end WeilConjectures.FiniteRationalHeart
