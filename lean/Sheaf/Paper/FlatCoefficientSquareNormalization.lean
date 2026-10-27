/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Sheaf.Paper.InternalScalarPullbackNormalization
public import Sheaf.Paper.InternalScalarMateProjection
public import Sheaf.Paper.ModuleRingedToposDerivedComparison
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Paper.FlatScalarUnitNormalization
import Sheaf.Paper.FlatScalarGeometricCoherence
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact

/-! # The flat coefficient square in its scalar tensor presentation

Source: blueprint, rational proper-base-change proof, paragraph (1), canonical scalar
comparison; Stacks Project, Tags 015F, 0FND, 0D6E, 07A6, 07A4 and 0B65
(blueprint: lem-sfb-flat-coefficient-square-normalization).

The scalar and geometric functors, their adjunctions, and the tensor presentations
are the recorded unbounded internal-module constructions. The section comparison is
specified on K-injectives by the identity ordinary restriction/direct-image square.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.QuotientChange

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CondensedRing.derivedPullIso CondensedRing.derivedComapLowerStarIso
  CondensedRing.derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction CondensedRing.upperStar

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]

/-- Linearity of the coefficient homomorphism between regular modules.
Source: Stacks 03EK; blueprint rational proper-base-change proof (1)
(blueprint: lem-sfb-flat-coefficient-square-normalization).
Proof: multiplication preservation for coefficientMap says a(rx)=a(r)a(x).
Expand the tensor morphism as the two whiskerings to obtain the displayed equation. -/
theorem flatScalarCoefficientMap_linear (a : R ⟶ S) [IsMonHom a] (T : Scheme.{u}) :
    μ[condensedRingObj R T] ≫ coefficientMap a T =
      condensedRingObj R T ◁ coefficientMap a T ≫
        (coefficientMap a T ▷ condensedRingObj S T) ≫ μ[condensedRingObj S T] := by
  have hR : IsCommMonObj R := inferInstance
  have hS : IsCommMonObj S := inferInstance
  simpa only [tensorHom_def', Category.assoc] using
    (IsMonHom.mul_hom (coefficientMap a T))

/-- The actual ring map, regarded as a morphism of regular modules.
Source: Stacks 03EK; blueprint rational proper-base-change proof (1)
(blueprint: lem-sfb-flat-coefficient-square-normalization). -/
def flatScalarCoefficientMap (a : R ⟶ S) [IsMonHom a] (T : Scheme.{u}) :
    Mod.regular (condensedRingObj R T) ⟶ B₀ a T :=
  Mod.Hom.mk' (coefficientMap a T) (flatScalarCoefficientMap_linear a T)

/-- The same coefficient homomorphism placed in degree zero and localized.
Source: Stacks 06YY; blueprint rational proper-base-change proof (1)
(blueprint: lem-sfb-flat-coefficient-square-normalization). -/
def flatScalarDerivedCoefficientMap (a : R ⟶ S) [IsMonHom a] (T : Scheme.{u}) :
    𝟙_ (DerivedCategory (Modules R T)) ⟶ B a T :=
  DerivedCategory.Q.map
    ((CochainComplex.singleFunctor (Modules R T) 0).map (flatScalarCoefficientMap a T))

variable (a : R ⟶ S) [IsMonHom a]
  [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T))]

/-- The actual inverse derivedPullIso, with the existing scalar interfaces exposed.
Source: blueprint coefficient comparisons; Stacks 0B65
(blueprint: lem-sfb-flat-coefficient-square-normalization). -/
def flatScalarTheta {X Y : Scheme.{u}} (f : X ⟶ Y) :
    D a Y ⋙ L S f ≅ L R f ⋙ D a X := by
  unfold D L CondensedRing.moduleObjectDerivedPullback
  exact (CondensedRing.derivedPullIso a f).symm

/-- The actual derivedComapLowerStarIso, with the existing scalar interfaces exposed.
Source: blueprint coefficient comparisons; Stacks 0D6E
(blueprint: lem-sfb-flat-coefficient-square-normalization). -/
def flatScalarDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    F S f ⋙ V a Y ≅ V a X ⋙ F R f := by
  unfold F CondensedRing.moduleObjectDerivedPushforward
  exact CondensedRing.derivedComapLowerStarIso a f

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)]

/-- A ring-sheaf direct-image comparison is the one induced by the identical ordinary
restriction/direct-image composites: its ordinary components fix every section, and
its derived components satisfy the computation-unit equation on K-injectives.
This characterizes the canonical d of the ring-sheaf-change adjunction, in the recorded
section-module realization, without choosing an arbitrary derived isomorphism.
Source: Stacks 0D6E and 07A6; blueprint rational proper-base-change proof (1)
(blueprint: lem-sfb-flat-coefficient-square-normalization). -/
def FlatSectionDirectImageNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : ModuleRingedComparison.derivedPushforward S f ⋙
        SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology Y) (coefficientMap a Y)) ≅
      SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) (coefficientMap a X)) ⋙
        ModuleRingedComparison.derivedPushforward R f) : Prop :=
  ∃ r : ModuleRingedComparison.pushforward S f ⋙
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
        (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) (coefficientMap a Y)) ≅
    SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
        (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (coefficientMap a X)) ⋙
      ModuleRingedComparison.pushforward R f,
  (∀ (N : ModuleRingedComparison.modules S X) (W : Y.ProEtᵒᵖ)
    (x : ((ModuleRingedComparison.pushforward S f).obj N).val.obj W),
    (r.hom.app N).val.app W x = x) ∧
  ∀ (I : CochainComplex (ModuleRingedComparison.modules S X) ℤ), I.IsKInjective →
    (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
      (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) (coefficientMap a Y))).map
        ((ModuleRingedComparison.pushforward S f).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) ≫
      d.hom.app (DerivedCategory.Q.obj I) ≫
      (ModuleRingedComparison.derivedPushforward R f).map
        (((SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X)
              (coefficientMap a X))).mapHomologicalComplexUpToQuasiIsoFactorsh
              (.up ℤ)).hom.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) =
    ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) (coefficientMap a Y))).mapHomologicalComplexUpToQuasiIsoFactorsh
              (.up ℤ)).hom.app
          (((ModuleRingedComparison.pushforward S f).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso r (.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) ≫
      (ModuleRingedComparison.pushforward R f).rightDerivedFunctorUnit.app
        (((SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) (coefficientMap a X))).mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ (.up ℤ)).obj I))

attribute [local irreducible] scalarAdj sectionScalarRestriction scalarRestrictionPull
  scalarRestrictionPush scalarCoefficientPull
  ModuleRingedComparison.derivedPushforward
  scalarSectionPushComparison

set_option maxHeartbeats 1600000 in
-- The full conjunction elaborates the specified scalar, tensor and geometric comparisons.
/-- The flat scalar square is the specified tensor-pullback square, including its units
and the equality with the ring-sheaf direct-image comparison.

Source: blueprint, rational proper-base-change proof, paragraph (1), canonical scalar
comparison; Stacks Tags 015F, 0FND, 0D6E, 07A6, 07A4 and 0B65
(blueprint: lem-sfb-flat-coefficient-square-normalization).

Proof:
1. Exact extension followed by exact restriction is tensor with the restricted regular
coefficient, by the balanced presentation and symmetry. Hence B and C are flat.
Coefficient pullback maps are isomorphisms, so both geometric pullbacks are exact.
2. The ordinary scalar unit inserts 1. The internal/section balanced-generator comparison
preserves that unit. Exact-derived factorization and the pre-derived adjunction formula
identify the specified derived units with these ordinary units after localization.
3. On a K-injective S-complex, restriction is K-injective since extension is exact.
Every factor defining actual derivedComapLowerStarIso is therefore the localization
of the same ordinary identity restriction/direct-image comparison. This is exactly
the computation-unit normalization defining the ring-sheaf comparison. Naturality and
K-injective resolutions extend equality to all objects and all morphisms.
4. Transpose the inverse actual theta under the composite scalar/geometric adjunctions.
Conjugacy to d and the ring-sheaf Hom identity give b inverse followed by L of the scalar
unit as its scalar transpose. All units are the specified ones, by step 2.
5. The normalized balancing lambda has the same scalar transpose: both maps send the
inverse image of m to the inverse image of m tensor 1. The balanced coprojection and
sheafification universal properties prove equality of ordinary maps. Exact localization
extends it to unbounded complexes. Injectivity of the scalar Hom bijection gives lambda
= theta, and therefore PullNormalized and SectionPullNormalized for actual theta.
6. Apply lem-sfb-internal-scalar-mate-projection to these normalized maps. Its first
equation, composed with L(eY inverse), is exactly the final displayed equation below.
The internal/section tensor comparison carries scalarTensorPull to the specified
ringed tensor comparison. Its flat-term K-flat computation is the pure-tensor map
f inverse (m tensor s) mapping to f inverse m tensor f inverse s, followed by rho. -/
theorem flat_coefficient_square_normalization
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    {X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (eX : TensorNormalization a X.left) (eY : TensorNormalization a Y.left)
    (_heX : TensorNormalized a X.left eX) (_heY : TensorNormalized a Y.left eY) :
    exactFunctor _ _ (tensorRight (B₀ a X.left)) ∧
    exactFunctor _ _ (tensorRight (B₀ a Y.left)) ∧
    exactFunctor _ _ (CondensedRing.upperStar R f.left) ∧
    exactFunctor _ _ (CondensedRing.upperStar S f.left) ∧
    (∀ M : DerivedCategory (Modules R X.left),
      (scalarAdj a X.left).unit.app M ≫ eX.derived.hom.app M =
        (ρ_ M).inv ≫ (M ◁ flatScalarDerivedCoefficientMap a X.left)) ∧
    (∀ M : DerivedCategory (Modules R Y.left),
      (scalarAdj a Y.left).unit.app M ≫ eY.derived.hom.app M =
        (ρ_ M).inv ≫ (M ◁ flatScalarDerivedCoefficientMap a Y.left)) ∧
    (flatScalarDirectImage a f.left).hom = scalarRestrictionPush a f.left ∧
    PullNormalized a f.left (flatScalarTheta a f.left) ∧
    (∃ (sX : SectionScalarComparison a X.left) (sY : SectionScalarComparison a Y.left),
      SectionScalarNormalized a X.left sX ∧ SectionScalarNormalized a Y.left sY ∧
      SectionTensorNormalized a X.left sX eX ∧ SectionTensorNormalized a Y.left sY eY ∧
      SectionPullNormalized a f.left sX sY (flatScalarTheta a f.left) ∧
      (∀ M : DerivedCategory (Modules R X.left),
        (ModuleRingedComparison.derivedEquivalence R X.left).functor.map
            ((scalarAdj a X.left).unit.app M) ≫
          (sectionScalarRestriction a X.left sX).hom.app ((D a X.left).obj M) ≫
          (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
            (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology X.left) (coefficientMap a X.left))).map
                (sX.derived.hom.app M) =
        sX.pair.adjunction.unit.app
          ((ModuleRingedComparison.derivedEquivalence R X.left).functor.obj M)) ∧
      (∀ M : DerivedCategory (Modules R Y.left),
        (ModuleRingedComparison.derivedEquivalence R Y.left).functor.map
            ((scalarAdj a Y.left).unit.app M) ≫
          (sectionScalarRestriction a Y.left sY).hom.app ((D a Y.left).obj M) ≫
          (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
            (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology Y.left) (coefficientMap a Y.left))).map
                (sY.derived.hom.app M) =
        sY.pair.adjunction.unit.app
          ((ModuleRingedComparison.derivedEquivalence R Y.left).functor.obj M)) ∧
      ∃ d : ModuleRingedComparison.derivedPushforward S f.left ⋙
          SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
            (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology Y.left) (coefficientMap a Y.left)) ≅
        SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
            (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology X.left) (coefficientMap a X.left)) ⋙
          ModuleRingedComparison.derivedPushforward R f.left,
      FlatSectionDirectImageNormalized a f.left d ∧
      ∀ N : DerivedCategory (Modules S X.left),
        (ModuleRingedComparison.derivedEquivalence R Y.left).functor.map
            ((flatScalarDirectImage a f.left).hom.app N) ≫
          (scalarSectionPushComparison R f.left).hom.app ((V a X.left).obj N) ≫
          (ModuleRingedComparison.derivedPushforward R f.left).map
            ((sectionScalarRestriction a X.left sX).hom.app N) =
        (sectionScalarRestriction a Y.left sY).hom.app ((F S f.left).obj N) ≫
          (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
            (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology Y.left) (coefficientMap a Y.left))).map
                ((scalarSectionPushComparison S f.left).hom.app N) ≫
          d.hom.app ((ModuleRingedComparison.derivedEquivalence S X.left).functor.obj N)) ∧
    ∀ M : DerivedCategory (Modules R Y.left),
      (L R f.left).map (eY.derived.inv.app M) ≫
        (scalarRestrictionPull a f.left).inv.app ((D a Y.left).obj M) ≫
        (V a X.left).map ((flatScalarTheta a f.left).hom.app M) ≫
        eX.derived.hom.app ((L R f.left).obj M) =
      scalarTensorPull f.left M (B a Y.left) ≫
        ((L R f.left).obj M ◁ (scalarCoefficientPull a f.left).hom) := by
  have flatTensor (T : Scheme.{u}) (e : TensorNormalization a T) :
      exactFunctor _ _ (tensorRight (B₀ a T)) := by
    have : PreservesFiniteLimits (extension a T ⋙ V₀ a T) := inferInstance
    have : PreservesFiniteColimits (extension a T ⋙ V₀ a T) := inferInstance
    exact ⟨preservesFiniteLimits_of_natIso e.ordinary,
      preservesFiniteColimits_of_natIso e.ordinary⟩
  refine And.intro (flatTensor X.left eX) ?_
  refine And.intro (flatTensor Y.left eY) ?_
  refine And.intro ((exactFunctor_iff _).2
    ⟨(CondensedRing.module_pullback_additive_exact R f.left).2.1,
      (CondensedRing.module_pullback_additive_exact R f.left).2.2.1⟩) ?_
  refine And.intro ((exactFunctor_iff _).2
    ⟨(CondensedRing.module_pullback_additive_exact S f.left).2.1,
      (CondensedRing.module_pullback_additive_exact S f.left).2.2.1⟩) ?_
  obtain ⟨huX, sX, hsX, htX, hsuX⟩ := flat_scalar_unit_normalization a X.left eX _heX
    (flatScalarCoefficientMap a X.left) rfl
  obtain ⟨huY, sY, hsY, htY, hsuY⟩ := flat_scalar_unit_normalization a Y.left eY _heY
    (flatScalarCoefficientMap a Y.left) rfl
  refine And.intro huX ?_
  refine And.intro huY ?_
  obtain ⟨hd, hpull, hsp, d, hr, hc⟩ :=
    flat_scalar_geometric_coherence a f.left sX sY hsX hsY
      (flatScalarTheta a f.left) (flatScalarDirectImage a f.left) rfl rfl
  refine And.intro hd ?_
  refine And.intro hpull ?_
  refine And.intro ?_ ?_
  · exact ⟨sX, sY, hsX, hsY, htX, htY, hsp, hsuX, hsuY, d, hr, hc⟩
  intro M
  have h := (internal_scalar_mate_projection a f.left eX eY
    (flatScalarTheta a f.left) _heX _heY hpull).2.1 M
  unfold scalarPullLeft scalarPullRight at h
  calc
    _ = (L R f.left).map (eY.derived.inv.app M) ≫
        ((L R f.left).map (eY.derived.hom.app M) ≫
          scalarTensorPull f.left M (B a Y.left) ≫
          ((L R f.left).obj M ◁ (scalarCoefficientPull a f.left).hom)) := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ (L R f.left).map (eY.derived.inv.app M) ≫ z) h
    _ = _ := by
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp,
        Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry.ProEtale.QuotientChange
