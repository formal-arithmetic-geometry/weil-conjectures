/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.IntegralOperationsWellDefined
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization

/-!
# Completed stalks and source reparametrization

Source: Stacks Project, sites.tex, Tags 05V1 and 0F4F; proetale.tex, Tags 0993 and 099N;
blueprint main-20261015, thm-trf-l-function-euler-product.proof.md, Step 1, Local powers,
input (b) (blueprint: lem-trf-completed-stalk-reparametrization-coherence).

The normalization is an equation of maps of whole strict quotient towers. Its realization
uses the specified diagonal map on both Roos coordinates, never detection by reductions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedStalk

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [lprime : Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

include lprime in
/-- The coefficient prime is a unit on the point, both in stalks and residue fields.
Source: blueprint finite-field convention; Stacks 099N
(blueprint: lem-trf-completed-stalk-reparametrization-coherence).
Proof: the cardinality of k₀ gives characteristic p, which extends to its algebraic
closure k and to the residue field of Spec k. The distinct prime l is nonzero in k,
hence a unit. The stalk and residue field at the unique point are canonically k. -/
theorem pointUnits [Fact (l ≠ D.p)] :
    (∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x)) ∧
      (∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).residueField x)) := by
  sorry

/-- The point's invertibility instance, derived from the fixed prime-to-p convention.
Source: blueprint finite-field convention; Stacks 099N
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
instance pointInvertible [Fact (l ≠ D.p)] (x : Spec (.of D.k)) :
    Invertible (l : (Spec (.of D.k)).residueField x) := (pointUnits D l).2 x |>.invertible

/-- `J_v = Fib_s Lv*`, viewed through the faithful full-subcategory inclusion of its target.
Source: Stacks 05V1, 099N; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def integralFibre {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X) :=
  (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E v ⋙
    pointFibreIntegralAmbient D l E

/-- The comparison is exactly Fib of the inverse specified integral compositor.
Source: Stacks 05V1, 0F4F, 099N; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def comparison [Fact (l ≠ D.p)] (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y) (M : sfIntegralConstructibleCategory l E X) :
    (integralFibre D l E v).obj ((constructibleIntegralPullback l E f).obj M) ≅
      (integralFibre D l E (v ≫ f)).obj M :=
  (pointFibreIntegralAmbient D l E).mapIso (integralComparisonComposition l E C v f M).symm

/-- Sections in each degree, retaining the same lifted integral coefficient ring.
Source: Stacks 099N; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
abbrev sectionsComplex := (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)

/-- The simultaneous strict section tower of v*P_n with the actual quotient transitions.
Source: Stacks 099N(5), 0941; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def sectionTower {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (P : CochainComplex (integralTowerModules l E X) ℤ) :=
  (integralOperationsPullbackTowerFunctor l E v).obj P ⋙ sectionsComplex D l E

/-- The pointed lift from the final point object into the base-changed neighbourhood.
Source: Stacks 05V1; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def pointedLift {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (U : ProEtaleGeometricNeighbourhood v) :
    ProEt.mk (𝟙 (Spec (.of D.k))) ⟶ (proEtaleBaseChange v).obj U.right :=
  MorphismProperty.Over.homMk
    (pullback.lift U.hom.left (𝟙 _) (by
      change U.hom.left ≫ U.right.hom = (𝟙 _) ≫ v
      exact U.hom.w.trans (Category.id_comp v).symm)) (by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 _
      exact pullback.lift_snd _ _ _)

/-- Restrict a finite pullback-unit section along a pointed lift. These elements are
exactly the finite stalk germs in final-object section coordinates.
Source: Stacks 05V1, 0F4F, 0993; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def germSection {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (P : CochainComplex (integralTowerModules l E X) ℤ) (n : ℕ) (i : ℤ)
    (U : ProEtaleGeometricNeighbourhood v)
    (a : (((unrestrictedIntegralFiniteComplex l E X n).obj P).X i).val.obj (op U.right)) :
    ((sectionTower D l E v P).obj (op n)).X i :=
  (((integralPullbackFiniteComplex l E v P n).X i).val.map (pointedLift D v U).op)
    (integralOperationsPullbackGenerator l E v n
      (((unrestrictedIntegralFiniteComplex l E X n).obj P).X i) U.right a)

/-- The unique strict tower transport, normalized by the finite germ rule on every
complex, every degree, and every pointed neighbourhood. Naturality includes all chain maps.
Source: Stacks 05V1, 0F4F, 0993, 0941; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence).
Proof: finite pullback-stalk coherence identifies sections of v*P_n with (P_n)_v.
Reindex neighbourhoods by Spec alpha; this sends [U,u,a] to [U,u Spec alpha,a].
The unit-normalized finite pullback model identifies this with germSection. The same
rule with alpha inverse is inverse. Reduction changes only a, so these maps commute
with all quotient transitions and form an isomorphism of entire strict towers.
Their chain-map naturality is the naturality of the finite comparison. Germs generate
each stalk, hence the rule uniquely determines every component and the whole tower map. -/
theorem towerReparam_existsUnique {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (α : D.k ≃+* D.k) :
    ∃! R : (integralOperationsPullbackTowerFunctor l E v) ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sectionsComplex D l E) ≅
      (integralOperationsPullbackTowerFunctor l E
        (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)) ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sectionsComplex D l E),
      ∀ (P : CochainComplex (integralTowerModules l E X) ℤ) (n : ℕ) (i : ℤ)
        (U : ProEtaleGeometricNeighbourhood v)
        (a : (((unrestrictedIntegralFiniteComplex l E X n).obj P).X i).val.obj (op U.right)),
        ((R.hom.app P).app (op n)).f i (germSection D l E v P n i U a) =
          germSection D l E _ P n i ((proEtaleStalkNeighbourhoodReparam v α).obj U) a := by
  sorry

/-- The normalized entire tower map, not unrelated maps on individual reductions.
Source: Stacks 05V1, 0941; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def towerReparam {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X) (α : D.k ≃+* D.k) :=
  (towerReparam_existsUnique D l E v α).exists.choose


/-- The unshifted coordinate of a Roos complex followed by one product projection.
Source: Stacks 0941; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def roosFirst {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ) (i : ℤ) :=
  (CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism (K := fun m ↦ T.obj (op m))
      (integralOperationsTowerStep T))).f i ≫ (Pi.π (fun m ↦ T.obj (op m)) n).f i

/-- The shifted coordinate of the same concrete Roos complex.
Source: Stacks 0941; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def roosSecond {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ) (i : ℤ) :=
  (CochainComplex.mappingCocone.snd
    (towerTransitionEndomorphism (K := fun m ↦ T.obj (op m))
      (integralOperationsTowerStep T))).v i (i + -1) rfl ≫
        (Pi.π (fun m ↦ T.obj (op m)) n).f (i + -1)

/-- Sections commute with the concrete Roos complex. Both coordinate equations are
required: specifying only the unshifted projections would not determine this map.
Source: Stacks 0941, exact point sections; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence).
Proof: evaluation and restriction of scalars preserve sectionwise products. Apply
these product identifications on each summand of Cone(1-s)[-1]. The differential
is preserved because the section functor is additive and preserves transitions.
The inverse uses the inverse product identifications. Product projections and the
two biproduct projections jointly determine every degree map, proving uniqueness. -/
theorem sectionsRoos_existsUnique
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ∃! e : (sectionsComplex D l E).obj (integralOperationsRoos T) ≅
        integralOperationsRoos (T ⋙ sectionsComplex D l E),
      (∀ (n : ℕ) (i : ℤ), e.hom.f i ≫ roosFirst (T ⋙ sectionsComplex D l E) n i =
        (pointIntegralSections l E D.k).map (roosFirst T n i)) ∧
      (∀ (n : ℕ) (i : ℤ), e.hom.f i ≫ roosSecond (T ⋙ sectionsComplex D l E) n i =
        (pointIntegralSections l E D.k).map (roosSecond T n i)) := by
  sorry

/-- The unique comparison preserving both Roos coordinates.
Source: Stacks 0941; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def sectionsRoos
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  (sectionsRoos_existsUnique D l E T).exists.choose

/-- The point fibre's existing small-Hom localization of module complexes.
Source: blueprint point targets; Stacks 05RU
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
abbrev moduleQ := @DerivedCategory.Q
  (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
  (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- The canonical whole-cone realization on every simultaneous good representative.
Its maps are the recorded pullback comparison, exact-sections localization comparison,
and the product-and-biproduct comparison fixed on both coordinates above.
Source: Stacks 099N, 0941; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def realization {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (K : sfIntegralConstructibleCategory l E X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) :
    (integralFibre D l E v).obj K ≅
      (moduleQ l E).obj (integralOperationsRoos (sectionTower D l E v P.obj)) :=
  (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullback l E v).mapIso e.symm) ≪≫
    (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullbackComparison l E v).app P) ≪≫
    (@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
      _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
      (pointIntegralSections l E D.k) _ _ _).app
      ((integralOperationsPullbackComplexFunctor l E v).obj P.obj) ≪≫
    (moduleQ l E).mapIso
      (sectionsRoos D l E ((integralOperationsPullbackTowerFunctor l E v).obj P.obj))

/-- Completed reparametrization is uniquely specified by realization of the entire
normalized strict tower map, for every good representative and every representative iso.
Source: Stacks 05V1, 099N, 0941; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence).
Proof: conjugate the diagonal two-coordinate Roos map of towerReparam by realization.
Changing the K-flat representative gives commuting quotient diagrams, and the normalized
pullback descent identifies their realizations. Thus the conjugate is independent of the
representative. Localization descends the natural chain transformation to all roofs;
the inverse chain transport descends too. Every constructible object has a good
representative, so the displayed equality determines the natural isomorphism uniquely. -/
theorem reparam_existsUnique {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (α : D.k ≃+* D.k) :
    ∃! r : integralFibre D l E v ≅
        integralFibre D l E (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v),
      ∀ (K : sfIntegralConstructibleCategory l E X)
        (P : (integralOperationsGoodComplex l E X).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ K.obj),
        r.hom.app K ≫ (realization D l E _ K P e).hom =
          (realization D l E v K P e).hom ≫
            (moduleQ l E).map (integralOperationsRoosMap
              ((towerReparam D l E v α).hom.app P.obj)) := by
  sorry

/-- The completed source transport determined by the full strict-tower normalization.
Source: Stacks 05V1, 0941; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def reparam {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X) (α : D.k ≃+* D.k) :=
  (reparam_existsUnique D l E v α).exists.choose


/-- The source automorphism as an actual scheme isomorphism, with the usual Spec map.
Source: Stacks 05V1; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def sourceIso (α : D.k ≃+* D.k) : Spec (.of D.k) ≅ Spec (.of D.k) :=
  Scheme.Spec.mapIso α.toCommRingCatIso.op

/-- Restriction from the identity final object to the isomorphic object (s,delta).
Source: Stacks 05V1; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def sourceArrow (α : D.k ≃+* D.k) :
    ProEt.mk (sourceIso D α).hom ⟶ ProEt.mk (𝟙 (Spec (.of D.k))) :=
  MorphismProperty.Over.homMk (sourceIso D α).hom (Category.comp_id _)

/-- Section restriction followed by inverse-image insertion, in the dependency's
canonical sectionwise inverse-image model. This is uniquely fixed on every section.
Source: Stacks 05V1 and the isomorphism inverse-image formula; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence).
Proof: at the final object the sectionwise inverse image is M(s,delta). Restrict
along delta to define rho. Constants are preserved by the specified completed
coefficient map, so the map is O_E-linear. Restriction along delta inverse is its
inverse. Restriction commutes with module maps, giving naturality; the formula on
every section determines the natural isomorphism uniquely. -/
theorem sectionRestriction_existsUnique (α : D.k ≃+* D.k) :
    ∃! ρ : pointIntegralSections l E D.k ≅
        AlgebraicGeometry.ProEtale.inverseImageIntegralModules l E (sourceIso D α).hom ⋙
          pointIntegralSections l E D.k,
      ∀ (M : integralTowerModules l E (Spec (.of D.k)))
        (a : (pointIntegralSections l E D.k).obj M),
        ρ.hom.app M a = M.val.map (sourceArrow D α).op a := by
  sorry

/-- The normalized restriction isomorphism on all integral sheaves.
Source: Stacks 05V1; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def sectionRestriction (α : D.k ≃+* D.k) :=
  (sectionRestriction_existsUnique D l E α).exists.choose

/-- Exact section restriction descended to arbitrary derived morphisms.
Source: Stacks 05V1 and localization; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def derivedSectionRestriction (α : D.k ≃+* D.k) :
    pointFibreIntegralAmbient D l E ≅
      AlgebraicGeometry.ProEtale.inverseImageIntegralDerived l E (sourceIso D α).hom ⋙
        pointFibreIntegralAmbient D l E :=
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI := pointIntegralSectionsAdditive l E D.k
  letI := isoSectionwiseModuleInverseImage_additive (sourceIso D α).hom
    (AlgebraicGeometry.ProEtale.inverseImageCompletedCoefficientMap l E (sourceIso D α).hom)
  letI := pointFibreIntegralLimits D l E
  letI := pointFibreIntegralColimits D l E
  letI := isoSectionwiseModuleInverseImage_limits (sourceIso D α).hom
    (AlgebraicGeometry.ProEtale.inverseImageCompletedCoefficientMap l E (sourceIso D α).hom)
  letI := isoSectionwiseModuleInverseImage_colimits (sourceIso D α).hom
    (AlgebraicGeometry.ProEtale.inverseImageCompletedCoefficientMap l E (sourceIso D α).hom)
  Functor.mapDerivedCategoryNatIso (sectionRestriction D l E α) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The specified j: restriction, inverse-image insertion, then the actual chosen-resolution
comparison kappa, including its zero shifted Roos coordinate.
Source: Stacks 05V1, 099N; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def sectionMap [Fact (l ≠ D.p)] (α : D.k ≃+* D.k)
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (pointFibreIntegralAmbient D l E).obj N.obj ⟶
      (pointFibreIntegralAmbient D l E).obj
        ((integralDerivedPullback l E (sourceIso D α).hom).obj N.obj) :=
  (derivedSectionRestriction D l E α).hom.app N.obj ≫
    (pointFibreIntegralAmbient D l E).map
      (AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived l E
        (sourceIso D α).hom (pointUnits D l).1 (pointUnits D l).1 N.obj)

/-- The identity-point identification, with the specified completeness-unit normalization.
Source: Stacks 099N, 0941; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def identityFibre [Fact (l ≠ D.p)] (C : IntegralComparisonSystem.{u} l)
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (integralFibre D l E (𝟙 (Spec (.of D.k)))).obj N ≅
      (pointFibreIntegralAmbient D l E).obj N.obj :=
  (pointFibreIntegralAmbient D l E).mapIso
    (integralComparisonUnit l E C (Spec (.of D.k)) N)

/-- All integral coherence equations for the specified comparisons. Heterogeneous
identities insert only the equalities of composed scheme maps (associativity, units,
and the contravariant Spec composition law).
Source: Stacks 05V1, 0F4F, 099N, 0941; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
structure IntegralCoherent [Fact (l ≠ D.p)] (C : IntegralComparisonSystem.{u} l) : Prop where
  /-- Naturality in every integral derived arrow, not only chosen chain maps. -/
  naturality : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y)
    (M N : sfIntegralConstructibleCategory l E X) (a : M ⟶ N),
    (integralFibre D l E v).map ((constructibleIntegralPullback l E f).map a) ≫
        (comparison D l E C f v N).hom =
      (comparison D l E C f v M).hom ≫ (integralFibre D l E (v ≫ f)).map a
  /-- Pullback-composition coherence with the specified compositor chi. -/
  composition : ∀ {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (f : Y ⟶ X) (h : Z ⟶ Y) (w : Spec (.of D.k) ⟶ Z)
    (M : sfIntegralConstructibleCategory l E X),
    HEq (comparison D l E C (h ≫ f) w M).hom
      ((pointFibreIntegralAmbient D l E).map
          ((integralDerivedPullback l E w).map
            (integralComparisonComposition l E C h f M).hom) ≫
        (comparison D l E C h w ((constructibleIntegralPullback l E f).obj M)).hom ≫
        (comparison D l E C f (w ≫ h) M).hom)
  /-- Identity comparison under the specified identity-pullback identification. -/
  identity : ∀ (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (v : Spec (.of D.k) ⟶ X) (M : sfIntegralConstructibleCategory l E X),
    HEq (comparison D l E C (𝟙 X) v M).hom
      ((pointFibreIntegralAmbient D l E).map ((integralDerivedPullback l E v).map
        (integralComparisonUnit l E C X M).hom))
  /-- Pullback comparison commutes with source reparametrization. -/
  mixed : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y) (α : D.k ≃+* D.k)
    (M : sfIntegralConstructibleCategory l E X),
    HEq ((comparison D l E C f v M).hom ≫ (reparam D l E (v ≫ f) α).hom.app M)
      ((reparam D l E v α).hom.app ((constructibleIntegralPullback l E f).obj M) ≫
        (comparison D l E C f ((sourceIso D α).hom ≫ v) M).hom)
  /-- Spec reverses ring composition: the single automorphism is beta after alpha. -/
  reparamComposition : ∀ (X : Scheme.{u}) (v : Spec (.of D.k) ⟶ X)
    (α β : D.k ≃+* D.k) (M : sfIntegralConstructibleCategory l E X),
    HEq ((reparam D l E v α).hom.app M ≫
        (reparam D l E ((sourceIso D α).hom ≫ v) β).hom.app M)
      ((reparam D l E v (α.trans β)).hom.app M)
  /-- The identity source automorphism acts as the identity. -/
  reparamIdentity : ∀ (X : Scheme.{u}) (v : Spec (.of D.k) ⟶ X)
    (M : sfIntegralConstructibleCategory l E X),
    HEq ((reparam D l E v (RingEquiv.refl D.k)).hom.app M)
      (𝟙 ((integralFibre D l E v).obj M))
  /-- Equality of the specified section map and germ-normalized whole-tower transport. -/
  sections : ∀ (α : D.k ≃+* D.k)
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))),
    HEq (sectionMap D l E α N ≫
        (identityFibre D l E C
          ((constructibleIntegralPullback l E (sourceIso D α).hom).obj N)).inv ≫
        (comparison D l E C (sourceIso D α).hom (𝟙 (Spec (.of D.k))) N).hom)
      ((identityFibre D l E C N).inv ≫
        (reparam D l E (𝟙 (Spec (.of D.k))) α).hom.app N)


/-- Rationalization on the point's integral target, in the same small-Hom localizations
as its recorded fibre functors. Source: blueprint raw rationalization and point targets
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def fieldTensor :=
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} E)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)).mapDerivedCategory

/-- The recorded rational point fibre through its faithful coefficient/module size lift.
Source: blueprint point targets, order 1509
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def rationalPointFibre [Fact (l ≠ D.p)] :=
  letI : HasDerivedCategory.{u} (ModuleCat.{u} E) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} E)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  pointRationalFibre D l (Fact.out : l ≠ D.p) E ⋙
    (DerivedCategory.pointFiniteDimensional E).ι ⋙ (pointFibreModuleLift E).mapDerivedCategory

/-- The rational `J_v`, using the actual raw rational pullback and point fibre.
Source: Stacks 05V1, 099N; blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def rationalFibre [Fact (l ≠ D.p)] {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)] (v : Spec (.of D.k) ⟶ X) :=
  rationalDerivedPullback l E v ⋙ rationalPointFibre D l E

/-- The canonical identification of the actual rational point fibre with integral sections
rationalized. It uses the existing size-descent counit, not an unspecified comparison.
Source: blueprint point targets and raw rationalization
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def rationalPointNormalization [Fact (l ≠ D.p)]
    (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (rationalPointFibre D l E).obj K ≅
      (fieldTensor l E).obj ((pointFibreIntegralAmbient D l E).obj K.obj.obj) :=
  letI : HasDerivedCategory.{u} (ModuleCat.{u} E) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} E)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI := pointFibreSizeLift_equivalence E
  (pointFibreModuleLift E).mapDerivedCategory.mapIso
      ((DerivedCategory.pointFiniteDimensional E).ι.mapIso
        (pointRationalFibreObjIso D l (Fact.out : l ≠ D.p) E K)) ≪≫
    (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).ι.mapIso
      ((pointFibreSizeLift E).asEquivalence.counitIso.app
        (pointFibreRationalLarge D l (Fact.out : l ≠ D.p) E K.obj))

/-- The raw rational pullback has the recorded integral object map, without adding
idempotents. Source: blueprint raw rational operations
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def rationalUnderlyingPullback {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : Y ⟶ X)
    (K : sfRationalConstructibleCategory l E X) :
    ((rationalDerivedPullback l E f).obj K).obj ≅
      (constructibleIntegralPullback l E f).obj K.obj :=
  eqToIso (congrArg (fun J : sfRationalConstructibleCategory l E Y ↦ J.obj)
    ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K))

/-- Comparison between the actual rational stalk fibre and the rationalization of its
integral representative, using only the recorded object equality and point counit.
Source: blueprint Local powers (b), rationalization paragraph
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def rationalNormalization [Fact (l ≠ D.p)] {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)] (v : Spec (.of D.k) ⟶ X)
    (K : sfRationalConstructibleCategory l E X) :
    (rationalFibre D l E v).obj K ≅
      (fieldTensor l E).obj ((integralFibre D l E v).obj K.obj) :=
  rationalPointNormalization D l E ((rationalDerivedPullback l E v).obj K) ≪≫
    (fieldTensor l E).mapIso ((pointFibreIntegralAmbient D l E).mapIso
      ((sfIntegralConstructible l E (Spec (.of D.k))).ι.mapIso
        (rationalUnderlyingPullback l E v K)))

/-- The rational comparison has exactly the rationalized integral components. This
specifies all components; naturality is asserted for every raw rational arrow.
Source: blueprint Local powers (b); Stacks 05V1, 099N
(blueprint: lem-trf-completed-stalk-reparametrization-coherence).
Proof: conjugate the image of the integral comparison by the recorded point counit
and pullback object equality. Integral naturality gives naturality on integral arrows.
The point fibre and rational pullback act on f tensor a by a times their integral
maps; hence naturality extends to pure tensors and then finite sums. Objectwise
invertibility gives a natural isomorphism. The component formula proves uniqueness. -/
theorem rationalComparison_existsUnique [Fact (l ≠ D.p)]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y) :
    ∃! c : rationalDerivedPullback l E f ⋙ rationalFibre D l E v ≅
        rationalFibre D l E (v ≫ f),
      ∀ K : sfRationalConstructibleCategory l E X, c.hom.app K =
        (rationalNormalization D l E v ((rationalDerivedPullback l E f).obj K)).hom ≫
          (fieldTensor l E).map ((integralFibre D l E v).map
            (rationalUnderlyingPullback l E f K).hom) ≫
          (fieldTensor l E).map (comparison D l E C f v K.obj).hom ≫
          (rationalNormalization D l E (v ≫ f) K).inv := by
  sorry

/-- The specified rationalized completed pullback comparison.
Source: blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def rationalComparison [Fact (l ≠ D.p)] (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y) :=
  (rationalComparison_existsUnique D l E C f v).exists.choose

/-- Rational source transport is the image of the specified integral whole-tower map,
with naturality for every rational morphism, not only localized integral arrows.
Source: blueprint Local powers (b); Stacks 05V1, 0941
(blueprint: lem-trf-completed-stalk-reparametrization-coherence).
Proof: apply fieldTensor to integral reparametrization, and conjugate by
rationalNormalization. Naturality on pure tensors follows by linearity of the
recorded rational pullback and point fibre. Additivity extends it to arbitrary
rational arrows. The inverse is the rationalized inverse; the formula specifies
every component and proves uniqueness. -/
theorem rationalReparam_existsUnique [Fact (l ≠ D.p)] {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    (v : Spec (.of D.k) ⟶ X) (α : D.k ≃+* D.k) :
    ∃! r : rationalFibre D l E v ≅ rationalFibre D l E ((sourceIso D α).hom ≫ v),
      ∀ K : sfRationalConstructibleCategory l E X, r.hom.app K =
        (rationalNormalization D l E v K).hom ≫
          (fieldTensor l E).map ((reparam D l E v α).hom.app K.obj) ≫
          (rationalNormalization D l E ((sourceIso D α).hom ≫ v) K).inv := by
  sorry

/-- The uniquely specified rational source transport.
Source: blueprint Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def rationalReparam [Fact (l ≠ D.p)] {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    (v : Spec (.of D.k) ⟶ X) (α : D.k ≃+* D.k) :=
  (rationalReparam_existsUnique D l E v α).exists.choose

/-- The rational compositor, with its integral representative and actual object transport.
Source: blueprint raw rational operations; Stacks 099N
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def rationalCompositor (C : IntegralComparisonSystem.{u} l) {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ Y) (f : Y ⟶ X) (K : sfRationalConstructibleCategory l E X) :
    (rationalDerivedPullback l E (h ≫ f)).obj K ≅
      (rationalDerivedPullback l E h).obj ((rationalDerivedPullback l E f).obj K) :=
  (sfRationalConstructibleLocalization l E Z).mapIso
    (rationalUnderlyingPullback l E (h ≫ f) K ≪≫
      ObjectProperty.isoMk (sfIntegralConstructible l E Z)
        (X := (constructibleIntegralPullback l E (h ≫ f)).obj K.obj)
        (Y := (constructibleIntegralPullback l E h).obj
          ((constructibleIntegralPullback l E f).obj K.obj))
        (integralComparisonComposition l E C h f K.obj) ≪≫
      (constructibleIntegralPullback l E h).mapIso (rationalUnderlyingPullback l E f K).symm ≪≫
      (rationalUnderlyingPullback l E h ((rationalDerivedPullback l E f).obj K)).symm)

/-- The rationalized specified identity-pullback comparison.
Source: blueprint raw rational operations; Stacks 099N
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def rationalUnit (C : IntegralComparisonSystem.{u} l) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfRationalConstructibleCategory l E X) :
    (rationalDerivedPullback l E (𝟙 X)).obj K ≅ K :=
  (sfRationalConstructibleLocalization l E X).mapIso
    (rationalUnderlyingPullback l E (𝟙 X) K ≪≫
      ObjectProperty.isoMk _ (integralComparisonUnit l E C X K.obj))


/-- Rational j is precisely the image of the specified integral restriction/insertion/kappa
map, conjugated by the recorded point and object identifications.
Source: blueprint Local powers (b), rationalization paragraph
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def rationalSectionMap [Fact (l ≠ D.p)] (α : D.k ≃+* D.k)
    (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (rationalPointFibre D l E).obj N ⟶
      (rationalPointFibre D l E).obj
        ((rationalDerivedPullback l E (sourceIso D α).hom).obj N) :=
  (rationalPointNormalization D l E N).hom ≫
    (fieldTensor l E).map (sectionMap D l E α N.obj) ≫
    (fieldTensor l E).map ((pointFibreIntegralAmbient D l E).map
      (((sfIntegralConstructible l E (Spec (.of D.k))).ι.mapIso
        (rationalUnderlyingPullback l E (sourceIso D α).hom N)).inv)) ≫
    (rationalPointNormalization D l E
      ((rationalDerivedPullback l E (sourceIso D α).hom).obj N)).inv

/-- The identity-point identification in the actual rational fibre.
Source: blueprint Local powers (b); Stacks 099N
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
def rationalIdentityFibre [Fact (l ≠ D.p)] (C : IntegralComparisonSystem.{u} l)
    (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :=
  (rationalPointFibre D l E).mapIso (rationalUnit l E C (Spec (.of D.k)) N)

/-- The same equations in raw rationalization. The natural isomorphisms above already
quantify over arbitrary rational morphisms, including sums of nonintegral pure tensors.
Source: blueprint Local powers (b); Stacks 05V1, 0F4F, 099N
(blueprint: lem-trf-completed-stalk-reparametrization-coherence). -/
structure RationalCoherent [Fact (l ≠ D.p)] (C : IntegralComparisonSystem.{u} l) : Prop where
  /-- Composition uses the rationalization of the very same integral chi. -/
  composition : ∀ {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (f : Y ⟶ X) (h : Z ⟶ Y) (w : Spec (.of D.k) ⟶ Z)
    (M : sfRationalConstructibleCategory l E X),
    HEq ((rationalComparison D l E C (h ≫ f) w).hom.app M)
      ((rationalFibre D l E w).map (rationalCompositor l E C h f M).hom ≫
        (rationalComparison D l E C h w).hom.app ((rationalDerivedPullback l E f).obj M) ≫
        (rationalComparison D l E C f (w ≫ h)).hom.app M)
  /-- The rational identity comparison is the image of the specified integral unit. -/
  identity : ∀ (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (v : Spec (.of D.k) ⟶ X) (M : sfRationalConstructibleCategory l E X),
    HEq ((rationalComparison D l E C (𝟙 X) v).hom.app M)
      ((rationalFibre D l E v).map (rationalUnit l E C X M).hom)
  /-- Source transport and pullback comparison commute for rational coefficients. -/
  mixed : ∀ {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y) (α : D.k ≃+* D.k)
    (M : sfRationalConstructibleCategory l E X),
    HEq ((rationalComparison D l E C f v).hom.app M ≫
        (rationalReparam D l E (v ≫ f) α).hom.app M)
      ((rationalReparam D l E v α).hom.app ((rationalDerivedPullback l E f).obj M) ≫
        (rationalComparison D l E C f ((sourceIso D α).hom ≫ v)).hom.app M)
  /-- The full automorphism action law, with beta after alpha on field elements. -/
  reparamComposition : ∀ (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (v : Spec (.of D.k) ⟶ X) (α β : D.k ≃+* D.k)
    (M : sfRationalConstructibleCategory l E X),
    HEq ((rationalReparam D l E v α).hom.app M ≫
        (rationalReparam D l E ((sourceIso D α).hom ≫ v) β).hom.app M)
      ((rationalReparam D l E v (α.trans β)).hom.app M)
  /-- The zero-length succession of source automorphisms is the identity. -/
  reparamIdentity : ∀ (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (v : Spec (.of D.k) ⟶ X) (M : sfRationalConstructibleCategory l E X),
    HEq ((rationalReparam D l E v (RingEquiv.refl D.k)).hom.app M)
      (𝟙 ((rationalFibre D l E v).obj M))
  /-- The specified section equation after rationalization. -/
  sections : ∀ (α : D.k ≃+* D.k)
    (N : sfRationalConstructibleCategory l E (Spec (.of D.k))),
    HEq (rationalSectionMap D l E α N ≫
        (rationalIdentityFibre D l E C
          ((rationalDerivedPullback l E (sourceIso D α).hom).obj N)).inv ≫
        (rationalComparison D l E C (sourceIso D α).hom (𝟙 (Spec (.of D.k)))).hom.app N)
      ((rationalIdentityFibre D l E C N).inv ≫
        (rationalReparam D l E (𝟙 (Spec (.of D.k))) α).hom.app N)

/-- Completed stalk comparisons and source reparametrization, integrally and in raw
rationalization, with the specified full strict-system maps and all coherence laws.
Source: Stacks sites.tex Tags 05V1 and 0F4F; proetale.tex Tags 0993 and 099N;
blueprint main-20261015, thm-trf-l-function-euler-product.proof.md, Local powers (b)
(blueprint: lem-trf-completed-stalk-reparametrization-coherence).

Proof (the complete DAG proof plan):

1. Write $R=\mathcal O_E$. Choose a flat-term K-flat representative $P\to M$ and its simultaneous
   quotient tower $P_n=P\otimes_{\widehat R_T}(A_n)_T$, with actual quotient transitions, by [lem-
   pc-kflat-resolution] and [def-pur-integral-derived-operations]. The reductions have cohomology
   in one interval $[a,b]$ by [def-weil-derived-complete-integral-detailed]. To apply the bounded-
   complex finite stalk theorem, use the functorial zigzag $P_\bullet\leftarrow\tau_{\le
   b}P_\bullet\to\tau_{\ge a}\tau_{\le b}P_\bullet=:B_\bullet$. Both arrows are levelwise quasi-
   isomorphisms: the first changes only cohomology above $b$, and the second only below $a$, all
   of which vanish. Here good truncation uses $\ker d^b$ at the upper endpoint and the quotient by
   $\operatorname{im}d^{a-1}$ at the lower endpoint (cohomology if $a=b$). These are simultaneous
   tower constructions because kernels and quotients are functorial. Finite pullback is exact by
   [prop-weil-pbc-proetale-constant-exact], so it preserves these truncations and quasi-
   isomorphisms. Thus finite comparisons on the bounded $B_n$ also specify them on $P_n$ through
   this zigzag. No boundedness of the terms of $P$ or finite Tor-amplitude of $M_n$ is assumed.

2. For an $A_n$-complex $H$ on $s$, identify its identity geometric stalk with $\Gamma(s,H)$:
   every pointed neighbourhood $(U,u)$ receives the unique pointed map
   $u:(s,\mathrm{id})\to(U,u)$, and $[U,u,a]\mapsto u^*a$ is inverse to
   $a\mapsto[s,\mathrm{id},a]$ in the colimit of [def-weil-proetale-geometric-stalk]. Apply [lem-
   trf-proetale-pullback-stalk-coherence] to $v$ and the identity point to obtain
   $e_{v,n}:\Gamma(s,v^*P_n)\xrightarrow{\sim}(P_n)_v$. These commute with quotient transitions: a
   reduction sends the representative section $a$ to its image $\bar a$, and both orders give
   $[U,u,\bar a]$. Exact point sections [lem-weil-point-proetale-sections-exact] commute with the
   cone model of [def-pur-integral-derived-operations]: sheaf products have sectionwise products,
   so evaluation carries $(x_n)\mapsto(x_n-t_nx_{n+1})$ to the identical formula on sections and
   carries its cone and shift to their module versions. Consequently $J_v(M)$ is canonically the
   realization of the strict module tower $(P_n)_v$, through these $e_{v,n}$. This is an
   identification of whole cone complexes. The strict derived-limit functor [lem-weil-pbc-ringed-
   strict-tower-homotopy-limit] transports the tower quasi-isomorphisms of Step 1, so the bounded
   replacement does not change this identification.

3. Let $\chi_{v,f}:L(fv)^*\to Lv^*Lf^*$ be the specified integral compositor of [lem-trf-integral-
   pullback-comparison-realization]. Define $c_{f,v,M}=\Gamma(s,\chi_{v,f,M}^{-1})$. The defining
   map $\eta_{v,f,M}$ of that node identifies $Lv^*Lf^*M$ with realization of the simultaneous
   tower $v^*f^*P_n$, and identifies this $c$ with the inverse of the finite composition map. More
   explicitly, in the finite stalk coordinates of Step 2 its map is
   $e_{fv,n}^{-1}\,c^{\mathrm{fin}}_{f,v,P_n}\,e_{v,f^*P_n}$. Indeed [lem-trf-proetale-pullback-
   stalk-coherence] applied to $v,f$ and the identity point gives
   $e_{fv,n}=c^{\mathrm{fin}}_{f,v,P_n}\,e_{v,f^*P_n}\,\Gamma(s,\chi_{v,f,P_n})$. All coefficient
   transitions commute with this equation by their representative formulas. The integral
   realization node explicitly uses the counit of the entire reduction tower for $\eta$, and gives
   independence and naturality of these identifications. Thus this is exactly the required
   specified comparison, represented on the simultaneous diagrams. All iterated pullbacks remain
   in $D^b_c$ by [lem-pur-integral-operations-preserve-constructible] (1), so every use of these
   integral identifications has its required domain.

4. For $\delta=\operatorname{Spec}(\alpha)$ define the tower map
   $R_{v,\alpha,n}:(P_n)_v\to(P_n)_{v\delta}$ by $[U,u,a]\mapsto[U,u\delta,a]$. The finite
   comparison node [lem-trf-proetale-pullback-stalk-coherence] supplies this natural $A_n$-linear
   isomorphism on bounded complexes. It is also a strict tower map: reducing the section before or
   after this operation gives $[U,u\delta,\bar a]$. Its inverse is the same construction with
   $\delta^{-1}$, and therefore is a strict inverse. Transport its realization through the Step 2
   identifications to define $r_{v,\alpha,M}$. Concretely a map $R_\bullet$ of towers gives the
   cone map $(b,a)\mapsto((\prod R_n)b,(\prod R_n)a)$; commuting with transitions makes this a
   chain map. Thus the construction specifies both coordinates of the cone, not just maps on
   reductions. Functoriality of strict derived limit [lem-weil-pbc-ringed-strict-tower-homotopy-
   limit] makes it an integral isomorphism.

5. The constructions are natural for every integral derived morphism, including ones not
   represented by a single map between the initially chosen resolutions. On chain maps the
   representative formulas for $e$, $c^{\mathrm{fin}}$ and $R$ are natural, and hence natural on
   the whole quotient diagram. The descent and resolution comparisons of [lem-pur-integral-
   operations-well-defined] identify the quotient-cone constructions from different K-flat
   representatives. Exact point sections preserve quasi-isomorphisms by [lem-weil-point-proetale-
   sections-exact]. Thus these chain functors invert the arrows used to represent derived
   morphisms. The localization universal property [lem-weil-pbc-localization-universal-property]
   (2) descends their natural transformations uniquely, preserving identities and composition;
   naturality for the inverse of a quasi-isomorphism follows by multiplying its naturality square
   by its inverses. This proves resolution independence of $r$ as well as naturality for roofs.
   For $c$ it agrees with the already natural, resolution-independent $\eta$-construction of [lem-
   trf-integral-pullback-comparison-realization].

6. For $w:s\to Z$ use the same $P_\bullet$ on $X$ for every factor. On each finite level [lem-trf-
   proetale-pullback-stalk-coherence] gives $c^{\mathrm{fin}}_{fh,w}=c^{\mathrm{fin}}_{f,hw}\,c^{\
   mathrm{fin}}_{h,w}\,(\chi^{\mathrm{fin}}_{h,f})_w$. The quotient formulas make this an equation
   of tower maps, as in Step 3. The associativity clause and the entire-tower counit normalization
   in [lem-trf-integral-pullback-comparison-realization] identify all occurrences of the nested
   pullbacks with these simultaneous diagrams, including $J_w(\chi_{h,f,M})$. Applying the strict
   derived-limit functor and exact sections therefore gives precisely $c_{fh,w,M}=c_{f,hw,M}\circ
   c_{h,w,Lf^*M}\circ J_w(\chi_{h,f,M})$. At the identity morphism the finite comparison is the
   identity; the unit clause of the integral realization node gives $c_{\mathrm{id},v,M}=1$ under
   its specified identity identification. This also supplies
   $J_{\mathrm{id}}(N)=\operatorname{Fib}_sN$.

7. The finite mixed equation is the one in [lem-trf-proetale-pullback-stalk-coherence]. Its
   representative calculation is explicit: the pullback germ given by $(U,u',V,\theta,a)$ first
   maps to $[V,\operatorname{pr}_V\theta u',a]$; reparametrization then gives
   $[V,\operatorname{pr}_V\theta u'\delta,a]$. Reparametrizing $u'$ first and then applying the
   comparison gives exactly the same representative. Quotient reduction changes only $a$, so the
   equation holds on the entire strict tower. Under the identifications of [lem-trf-integral-
   pullback-comparison-realization], these are the maps of Steps 3--4. Functoriality of strict
   realization therefore gives $r_{fv,\alpha,M}\circ c_{f,v,M}=c_{f,v\delta,M}\circ
   r_{v,\alpha,Lf^*M}$, as equality of the specified integral maps.

8. The action law is an equality on representatives in [def-weil-proetale-geometric-stalk]:
   successive reparametrizations send $[U,u,a]$ to $[U,u\delta,a]$ and then
   $[U,u\delta\epsilon,a]$, while a single reparametrization by $\delta\epsilon$ gives that same
   representative. Also $\operatorname{Spec}(\alpha)\circ\operatorname{Spec}(\beta)=\operatorname{
   Spec}(\beta\circ\alpha)$, because affine spectrum reverses ring-map composition. Identity
   reparametrization fixes every representative. These are strict tower equations, and the product
   maps on both cone coordinates obey the same composition law. Hence $r_{v\delta,\beta,M}\circ
   r_{v,\alpha,M}=r_{v,\beta\circ\alpha,M}$ and $r_{v,1,M}=1$. Induction on the number of
   automorphisms proves the finite-succession assertion: appending one automorphism uses this two-
   factor identity, with the zero-length succession the identity.

9. For a complex $N$ on $s$, let $\rho_{\delta,N}:\Gamma(s,N)\to\Gamma(s,\delta^{-1}N)$ be
   restriction along $\delta$, followed by inverse-image insertion. The site-equivalence formula
   of [lem-weil-proetale-isomorphism-inverse-image] identifies the target with sections of $N$
   over $(s\xrightarrow{\delta}s)$; restriction along the isomorphism $\delta$ has inverse
   restriction along $\delta^{-1}$, so $\rho$ is an isomorphism. The specified map of the question
   is $j_{\delta,N}=\Gamma(s,\kappa^\delta_N)\rho_{\delta,N}$. For integral constructible $N$,
   [lem-weil-isomorphism-derived-pullback-comparison-normalization] says this SPECIFIED $\kappa$
   is natural and invertible and is the quotient-cone map with zero shifted coordinate. Its
   hypothesis holds since $N\in D^b_c(s,R)$ is derived complete. For a finite-coefficient sheaf, a
   section $a\in N(s)$ under restriction, insertion and $\kappa$ is the pullback-unit germ with
   source lift $\mathrm{id}_s$ and target lift $\delta$. The finite comparison formula sends it to
   $[s,\delta,a]$. This is also $r^{\mathrm{fin}}_{\mathrm{id},\alpha}([s,\mathrm{id},a])$. This
   proves the section equation at finite level directly from the normalizations.

10. Use one flat-term K-flat $Q\xrightarrow{q}N$ and $Q_n$ for all factors. Let $\mathcal
   H_v=\operatorname{Cone}(1-s:\prod_n(Q_n)_v\to\prod_n(Q_n)_v)[-1]$, and let
   $e_v:J_v(N)\xrightarrow{\sim}\mathcal H_v$ be the whole-cone identification of Step 2. For
   $v=\mathrm{id}$ its source is $\Gamma(s,N)$ via Step 6. The normalization theorem [lem-weil-
   isomorphism-derived-pullback-comparison-normalization], with $g=\mathrm{id}$, identifies
   $e_{\mathrm{id}}$ with sections of the actual completion unit, followed by the identity-stalk
   identifications; this unit is invertible on the derived-complete domain. Thus
   $e_{\mathrm{id}}\Gamma(q)$ sends $z$ to $(0,([s,\mathrm{id},\bar z_n])_n)$. By [def-weil-
   inverse-image-pullback-comparison], $j_{\delta,N}\Gamma(q)$ uses these same reductions,
   restricted along $\delta$, with zero shifted coordinate. Step 9 and the specified compositor
   realization [lem-trf-integral-pullback-comparison-realization] therefore give $$e_\delta
   c_{\delta,\mathrm{id},N}j_{\delta,N}\Gamma(q)(z)=(0,([s,\delta,\bar
   z_n])_n)=\operatorname{Cone}(R_{\mathrm{id},\alpha,\bullet})e_{\mathrm{id}}\Gamma(q)(z).$$
   These are equal chain maps on $\Gamma(s,Q)$, including the shifted coordinate. Exact sections
   [lem-weil-point-proetale-sections-exact] make $\Gamma(q)$ an isomorphism after localization.
   Cancel it and $e_\delta$; the definition of $r$ in Step 4 now gives
   $c_{\delta,\mathrm{id},N}j_{\delta,N}=r_{\mathrm{id},\alpha,N}$. This proves equality of the
   specified maps without using detection by reduction projections.

11. Apply Step 10 to $N=Lv^*M$, which is constructible by [lem-pur-integral-operations-preserve-
   constructible] (1). The mixed equation of Step 7 and the compositor identity of Step 6 allow
   each occurrence of a source automorphism to pass through $c_{f,v}$ with exactly the displayed
   reparametrized point. For successive automorphisms, replace each
   $c_{\delta,\mathrm{id}}j_\delta$ by $r$ using Step 10, then combine adjacent $r$'s by Step 8.
   This proves compatibility with any finite succession and with the comparison for any $v$. All
   constructions are $R$-linear, since the finite maps preserve scalar multiplication and
   products, cones and sections carry the induced $R$-action. Finally use [def-weil-
   rationalization-karoubi] and [def-weil-finite-coefficient-point]: on objects rationalization
   uses the same integral representatives, and on morphisms $f\otimes a$ the fiber map is
   $a(\Gamma(s,f)\otimes E)$. Send the integral comparison families and their equalities through
   these functors. Naturality for arbitrary rational morphisms follows by this formula and
   linearity, first for a simple tensor and then for a finite sum. Inverses remain inverses. This
   gives all assertions for $E$, with no Weil datum or integrality assumption on the morphisms.

The binary action and unit laws imply the finite-succession assertion by induction;
the mixed and section equations give its compatibility with every v. All equalities
are of the specified whole-cone maps. The rational equations are their images under
the displayed normalized scalar-extension functor. -/
theorem coherence [Fact (l ≠ D.p)] :
    ∃ C : IntegralComparisonSystem.{u} l,
      IntegralComparisonRealizationCoherence l E E (AlgHom.id ℚ_[l] E) C ∧
        IntegralCoherent D l E C ∧ RationalCoherent D l E C := by
  sorry

end WeilConjectures.CompletedStalk
