module

public import Sheaf.AlgebraicGeometry.FieldActionScalarTransportData
public import Sheaf.AlgebraicGeometry.FieldActionInternalPureTensor
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.CategoryTheory.InternalActionSitePresentation
import Sheaf.CategoryTheory.ActionToposGeometricRestriction
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
public import Sheaf.AlgebraicGeometry.GeometricSectionFunctors
public import Sheaf.AlgebraicGeometry.FieldActionToposNormalization
import Sheaf.CategoryTheory.RingedPresentationTransport
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Paper.KFlatRingedToposPullback

/-! # Normalized scalar adjunctions in the geometric field presentation

Source: Bhatt--Scholze Example 4.1.10 (geometric context); Stacks Project,
Modules on Sites 03CU, 03CZ, 03EL; Cohomology on Sites 06YN, 06YY, 07A6, 0D6E;
current blueprint direct-images paragraph (3), coefficient normalization
(blueprint: lem-sfb-field-ringed-scalar-adjunction-transport).

The helper specifications retain balanced generators, acyclic tests and the actual
total-derived computation maps. They make no choice of unspecified equivalence data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FieldActionTransport
open CondensedGalois CategoryTheory.InternalAbelianSheafModule

attribute [instance] GeometricData.additive fieldFunctor_additive coefficientPushAdditive
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

/-- Expose commutativity of the existing pulled-back condensed coefficient object.
Source: coefficientRing_X and isCommMonObj_condensedRingObj
(blueprint: lem-sfb-field-ringed-scalar-adjunction-transport). -/
instance fieldScalarCoefficientComm (R : Coefficients.{u}) (Y : Scheme.{u}) :
    IsCommMonObj (coefficientRing Y R.toMon).X :=
  isCommMonObj_condensedRingObj R.X Y

/-- Additivity of the actual module direct image at the common localization universes.
Source: the existing module pushforward
(blueprint: lem-sfb-field-ringed-scalar-adjunction-transport). -/
instance fieldScalarPushAdditive (R : Coefficients.{u}) {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    Functor.Additive.{u + 1, u + 2, u + 1, u + 2} (CondensedRing.lowerStar.{u} R.X f) :=
  CondensedRing.lowerStar_additive R.X f

variable (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]

local instance fieldActionSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The K-flat acyclic test in the action category. The tensor is computed after exact
conservative forgetting: its underlying complex is precisely the total tensor of the
underlying internal modules, with the diagonal action. Quantifying over all acyclic
action complexes therefore tests the actual action tensor, without choosing a new one.
Source: Stacks 06YN (blueprint: lem-sfb-field-ringed-scalar-adjunction-transport). -/
def IsActionTensorKFlat (R : Coefficients.{u})
    [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)]
    (P : CochainComplex (CategoryTheory.CondensedBar.Equivariant R (ks ≃ₐ[k] ks)) ℤ) :
    Prop :=
  ∀ A : CochainComplex (CategoryTheory.CondensedBar.Equivariant R (ks ≃ₐ[k] ks)) ℤ,
    A.Acyclic → (CochainComplex.mapBifunctor
      ((CategoryTheory.CondensedBar.forgetAction.mapHomologicalComplex (.up ℤ)).obj A)
      ((CategoryTheory.CondensedBar.forgetAction.mapHomologicalComplex (.up ℤ)).obj P)
      (curriedTensor (Profinite.CondensedAction.Modules R.toMon))).Acyclic

/-- The canonical balanced tensor comparison in geometric section coordinates.
Naturality and the pure tensor equation specify the comparison on the sheafified
relative tensor. The regular-module comparison sends one to one, hence is identity
in the normalized coefficient coordinates by linearity.
Source: Stacks 03EL (blueprint: lem-sfb-field-ringed-scalar-adjunction-transport). -/
structure FieldBalancedTensor (R : Coefficients.{u})
    [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)] (e : FieldData k ks R) where
  /-- The tensor comparison, with the G-action retained by its section normalization. -/
  tensor : ∀ M N : Modules R.toMon (Spec (.of k)),
    ((fieldFunctor k ks e).obj (M ⊗ N)).module ≅
      ((fieldFunctor k ks e).obj M).module ⊗ ((fieldFunctor k ks e).obj N).module
  /-- Naturality in both original modules. -/
  naturality : ∀ (M M' N N' : Modules R.toMon (Spec (.of k)))
      (f : M ⟶ M') (g : N ⟶ N'),
    ((fieldFunctor k ks e).map (f ⊗ₘ g)).val ≫ (tensor M' N').hom =
      (tensor M N).hom ≫ (((fieldFunctor k ks e).map f).val ⊗ₘ
        ((fieldFunctor k ks e).map g).val)
  /-- Pure tensors are unchanged on every geometric test, including after sheafification. -/
  pure : ∀ (M N : Modules R.toMon (Spec (.of k))) (P : Profinite.{u})
      (x : ((fieldFunctor k ks e).obj M).module.X.obj.obj (op P))
      (y : ((fieldFunctor k ks e).obj N).module.X.obj.obj (op P)),
    (((e.geometric.sections.hom.app (M ⊗ N)).app (op P)).hom)
      (((tensor M N).inv.hom.hom.app (op P)).hom
        (fieldActionInternalPureTensor (coherentTopology Profinite.{u}) R.X
          ((fieldFunctor k ks e).obj M).module ((fieldFunctor k ks e).obj N).module
          (op P) x y)) =
      fieldActionInternalPureTensor.{u + 1, u + 1, u} (Scheme.ProEt.topology (Spec (.of k)))
        (coefficientRing (Spec (.of k)) R.toMon).X M N
        (op (test k ks (Spec (.of k)) (𝟙 _) P))
        (((e.geometric.sections.hom.app M).app (op P)).hom x)
        (((e.geometric.sections.hom.app N).app (op P)).hom y)
  /-- The comparison on the regular module. -/
  regular : ((fieldFunctor k ks e).obj
    (Mod.regular (coefficientRing (Spec (.of k)) R.toMon).X)).module ≅ Mod.regular R.X
  /-- Its coefficient normalization; linearity gives the equation for every scalar. -/
  regular_one : ∀ P : Profinite.{u},
    (((e.geometric.sections.hom.app
      (Mod.regular (coefficientRing (Spec (.of k)) R.toMon).X)).app (op P)).hom)
      (((regular.inv.hom.hom.app (op P)).hom)
        (1 : (sectionRings (coherentTopology Profinite.{u}) R.X).obj (op P))) =
      (1 : (sectionRings (Scheme.ProEt.topology (Spec (.of k)))
        (coefficientRing (Spec (.of k)) R.toMon).X).obj
          (op (test k ks (Spec (.of k)) (𝟙 _) P)))

set_option synthInstance.maxHeartbeats 100000 in
-- The derived tensor typeclass search needs a larger local heartbeat budget.
/-- Scalar extension's field comparison uses the very same balanced comparison on
K-flat representatives. This is the square of total-left-derived computation counits,
not a choice of isomorphisms between derived objects.
Source: Stacks 06YY, 07A6 (blueprint: lem-sfb-field-ringed-scalar-adjunction-transport). -/
def ScalarRepresentativeNormalization {R R' : Coefficients.{u}} (φ : R ⟶ R')
    [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)]
    [CategoryTheory.CondensedBar.ActionAbelian R' (ks ≃ₐ[k] ks)]
    [ForgetData k ks R] [ForgetData k ks R']
    (e : FieldData k ks R) (e' : FieldData k ks R')
    (c : ScalarTransport k ks φ e e') : Prop := by
  letI : (fieldFunctor k ks e').Additive := e'.geometric.additive
  letI : (fieldFunctor k ks e).Additive := e.geometric.additive
  letI : c.extension.Additive := c.additive
  exact ∀ P : CochainComplex (Modules R.toMon (Spec (.of k))) ℤ,
    (∀ A : CochainComplex (Modules R.toMon (Spec (.of k))) ℤ,
      A.Acyclic → (CochainComplex.mapBifunctor A P (curriedTensor _)).Acyclic) →
    c.derived.extension.hom.app (DerivedCategory.Q.obj P) ≫
        c.derivedExtension.map ((fieldFunctor k ks e).mapDerivedCategoryFactors.hom.app P) ≫
        c.derivedCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((fieldFunctor k ks e).mapHomologicalComplex (.up ℤ)).obj P)) =
      (fieldFunctor k ks e').mapDerivedCategory.map
        ((extend φ (Spec (.of k))).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (fieldFunctor k ks e').mapDerivedCategoryFactors.hom.app
          (((extend φ (Spec (.of k))).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso c.ordinary.extension (.up ℤ)).hom.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The direct-image composition comparison for coefficient restriction. Its unit
normalization fixes the derived comparison uniquely; the ordinary map is identity.
Source: Stacks 0D6E (blueprint: lem-sfb-field-ringed-scalar-adjunction-transport). -/
structure DirectImageScalarComparison {R R' : Coefficients.{u}} (φ : R ⟶ R')
    {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [addPush : Functor.Additive.{u + 1, u + 2, u + 1, u + 2}
      (CondensedRing.lowerStar.{u} R.X f)]
    [addPush' : Functor.Additive.{u + 1, u + 2, u + 1, u + 2}
      (CondensedRing.lowerStar.{u} R'.X f)] where
  /-- The existing total-derived comparison, with its universal unit equation. -/
  comparison : @CoefficientComparison.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (restrictX φ Y) _ _ _ (restrictX φ Z) _ _ _
    (CondensedRing.lowerStar.{u} R.X f) addPush
    (CondensedRing.lowerStar.{u} R'.X f) addPush'
  /-- The actual underlying sheaf map is identity, hence identity on every section. -/
  identity : ∀ M : Modules R'.toMon Y, (comparison.ordinary.hom.app M).hom = 𝟙 _

/-- Read the ordinary comparison at its specified additive structures.
Source: Stacks 0D6E (blueprint: lem-sfb-field-ringed-scalar-adjunction-transport). -/
def DirectImageScalarComparison.ordinary {R R' : Coefficients.{u}} (φ : R ⟶ R')
    {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [addPush : Functor.Additive.{u + 1, u + 2, u + 1, u + 2}
      (CondensedRing.lowerStar.{u} R.X f)]
    [addPush' : Functor.Additive.{u + 1, u + 2, u + 1, u + 2}
      (CondensedRing.lowerStar.{u} R'.X f)]
    (ρ : DirectImageScalarComparison φ f) :
    restrictX φ Y ⋙ CondensedRing.lowerStar.{u} R.X f ≅
      CondensedRing.lowerStar.{u} R'.X f ⋙ restrictX φ Z :=
  ρ.comparison.ordinary

/-- Scalar restriction on geometric sections is the transported direct-image comparison.
The ordinary square is fixed on every section, and the total-derived-unit equation
in CoefficientComparison uniquely fixes its derived map, also for nonflat scalars.
Source: Stacks 0D6E (blueprint: lem-sfb-field-ringed-scalar-adjunction-transport). -/
structure GeometricScalarComparison {R R' : Coefficients.{u}} (φ : R ⟶ R')
    [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)]
    [CategoryTheory.CondensedBar.ActionAbelian R' (ks ≃ₐ[k] ks)]
    [ForgetData k ks R] [ForgetData k ks R']
    (e : FieldData k ks R) (e' : FieldData k ks R')
    (c : ScalarTransport k ks φ e e') (X : Scheme.{u}) (a : X ⟶ Spec (.of k))
    [addPush : Functor.Additive.{u + 1, u + 2, u + 1, u + 2}
      (CondensedRing.lowerStar.{u} R.X a)]
    [addPush' : Functor.Additive.{u + 1, u + 2, u + 1, u + 2}
      (CondensedRing.lowerStar.{u} R'.X a)]
    (d : GeometricData k ks X a R.toMon) (d' : GeometricData k ks X a R'.toMon)
    (ρ : DirectImageScalarComparison φ a) where
  /-- The actual geometric coefficient comparison. -/
  comparison : @CoefficientComparison.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (restrictX φ X) inferInstance inferInstance inferInstance
    c.restriction.functor inferInstance inferInstance inferInstance
    d.functor d.additive d'.functor d'.additive
  /-- Its ordinary comparison is identity in the original geometric section coordinates. -/
  sections : ∀ (M : Modules R'.toMon X) (P : Profinite.{u})
      (x : Profinite.CondensedAction.sectionModule R.toMon
        (d.functor.obj ((restrictX φ X).obj M)).module P),
    ((d'.sections.hom.app M).app (op P)).hom
      (((c.restriction.underlying.hom.app (d'.functor.obj M)).hom.hom.app (op P)).hom
        ((((comparison.ordinary.hom.app M).val).hom.hom.app (op P)).hom x)) =
      ((d.sections.hom.app ((restrictX φ X).obj M)).app (op P)).hom x
  /-- Field identification of the original geometric section functor. -/
  field : CondensedRing.lowerStar.{u} R.X a ⋙ fieldFunctor k ks e ≅ d.functor
  /-- The same field identification for the target coefficient ring. -/
  field' : CondensedRing.lowerStar.{u} R'.X a ⋙ fieldFunctor k ks e' ≅ d'.functor
  /-- The ordinary restriction comparison is the transport of the same rho. -/
  transport : ∀ M : Modules R'.toMon X,
    (field.hom.app ((restrictX φ X).obj M)).val ≫
        (comparison.ordinary.hom.app M).val =
      ((fieldFunctor k ks e).map ((DirectImageScalarComparison.ordinary φ a
        ρ).hom.app M)).val ≫
        (c.fieldComparison.ordinary.hom.app ((CondensedRing.lowerStar.{u} R'.X a).obj M)).val ≫
          (c.restriction.functor.map (field'.hom.app M)).val

/-- A normalized ringed field presentation transports ordinary and unbounded derived
scalar adjunctions and geometric restriction for every coefficient map.

Source: Bhatt--Scholze Example 4.1.10; Stacks 03CU, 03CZ, 03EL, 06YN, 06YY, 07A6,
0FPI and 0D6E; blueprint direct-images paragraph (3)
(blueprint: lem-sfb-field-ringed-scalar-adjunction-transport).

Proof:
1. Use lem-sfb-internal-action-site-presentation and
   lem-sfb-internal-section-scalar-adjunction. In normalized coordinates restriction
   changes only the scalar action, so its comparison is identity on every section.
   Action forgetting is the exact inverse image of lem-sfb-action-topos-geometric-restriction.
2. Ordinary transposition is h to h(1 tensor -), and evaluation is r' tensor m to r'f(m).
   Balancing and module sheafification preserve these inverse formulas. Apply
   lem-weil-pbc-ringed-topoi-module-pullback-tensor and
   lem-sfb-kflat-scalar-comparison-normalization to the equivalence: its tensor map
   preserves pure tensors and its unit is identity on the regular module. The scalar
   adjunction squares have identical Hom transposes, fixing units and counits.
3. Tensor comparisons extend to direct-sum total complexes. The exact inverse
   carries every acyclic test back to an acyclic test, proving K-flat preservation
   in both directions, with no boundedness or coefficient-flatness hypothesis.
4. Apply lem-pur-sheaf-ring-derived-coefficient-adjunction and the same K-flat scalar
   comparison to the identity-topos coefficient morphisms. The derived comparison
   is localization of the ordinary one, with exactly its computation-counit square.
5. Apply the same theorem to action forgetting. Its restriction comparison is the
   original underlying-module comparison. Hom transposes fix derived units and
   counits; signed termwise restriction commutes with shifts, hence so do its mates.
6. Regard restriction as identity-topos direct image. The two composites coincide.
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition gives rho with its
   K-injective computation formula and total-right-derived-unit equation; no
   preservation of K-injectives by restriction is assumed.
7. Identify E_R a_* with the geometric section functor on X^s[P]. Exact equivalence
   preserves K-injectives. Conjugating rho by these identifications and the field
   scalar comparison gives geometric restriction. All ordinary factors are identity
   on geometric sections, and composition of the unit equations fixes the derived map.
-/
theorem field_ringed_scalar_adjunction_transport
    {R R' : Coefficients.{u}} (φ : R ⟶ R')
    [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)]
    [CategoryTheory.CondensedBar.ActionAbelian R' (ks ≃ₐ[k] ks)]
    [ForgetData k ks R] [ForgetData k ks R']
    (e : FieldData k ks R) (e' : FieldData k ks R')
    (h : FieldActionToposNormalization k ks)
    (over : fieldFunctor k ks e ⋙ fieldActionActionSets k ks R ≅
      fieldActionFieldSets k R ⋙ h.equivalence.functor ⋙
        fieldActionActionUnderlying k ks)
    (over' : fieldFunctor k ks e' ⋙ fieldActionActionSets k ks R' ≅
      fieldActionFieldSets k R' ⋙ h.equivalence.functor ⋙
        fieldActionActionUnderlying k ks) :
    Nonempty (FieldBalancedTensor k ks R e) ∧ Nonempty (FieldBalancedTensor k ks R' e') ∧
    (∀ P : CochainComplex (Modules R.toMon (Spec (.of k))) ℤ,
      (∀ A : CochainComplex (Modules R.toMon (Spec (.of k))) ℤ,
        A.Acyclic → (CochainComplex.mapBifunctor A P (curriedTensor _)).Acyclic) ↔
      IsActionTensorKFlat k ks R
        (((fieldFunctor k ks e).mapHomologicalComplex (.up ℤ)).obj P)) ∧
    (∀ P : CochainComplex (Modules R'.toMon (Spec (.of k))) ℤ,
      (∀ A : CochainComplex (Modules R'.toMon (Spec (.of k))) ℤ,
        A.Acyclic → (CochainComplex.mapBifunctor A P (curriedTensor _)).Acyclic) ↔
      IsActionTensorKFlat k ks R'
        (((fieldFunctor k ks e').mapHomologicalComplex (.up ℤ)).obj P)) ∧
    ∃ c : ScalarTransport k ks φ e e', ScalarRepresentativeNormalization k ks φ e e' c ∧
      ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
        (a : X ⟶ Spec (.of k))
        (d : GeometricData k ks X a R.toMon) (d' : GeometricData k ks X a R'.toMon),
      ∃ ρ : DirectImageScalarComparison φ a,
        Nonempty (GeometricScalarComparison k ks φ e e' c X a d d' ρ) := by
  sorry

end AlgebraicGeometry.ProEtale.FieldActionTransport
