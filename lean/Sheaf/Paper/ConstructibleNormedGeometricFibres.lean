/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.NormContinuousMonodromyData
public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
public import Sheaf.Paper.CondensedQbarCoefficientConstruction
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.TotallyDisconnectedCoefficientRealization
import Sheaf.Paper.ContinuousRingUniverseRealization
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.ProEtale.WContractible
import Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.AlgebraicGeometry.ProEtale.WContractibleClopenPartition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.Refinement
import Sheaf.Topology.NoetherianGoodStratificationRefinement
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.InternalExtensionInverseImage

/-! # Constructible geometric fibres for totally disconnected normed fields

Source: Hemo--Richarz--Scholbach, Section 3 and Lemma 4.1
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open Opposite
namespace AlgebraicGeometry.ProEtale

/-- Final-object sections on the geometric-point site.
Source: HRS Section 3 and Lemma 4.1
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def normedPointSections (κ : Type u) [Field κ] :
    Sheaf (Scheme.ProEt.topology (Spec (.of κ))) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  sheafToPresheaf (Scheme.ProEt.topology (Spec (.of κ))) Ab.{u + 1} ⋙
    (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of κ)))))

/-- The usual sectionwise tensor comparison.
Source: HRS Lemma 4.1, tensor computation
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
instance normedPointSections_laxMonoidal (κ : Type u) [Field κ] :
    (normedPointSections κ).LaxMonoidal := by
  let E := (evaluation (Spec (.of κ)).ProEtᵒᵖ Ab.{u + 1}).obj
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of κ)))))
  let : E.Monoidal := Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }
  exact inferInstanceAs
    (sheafToPresheaf (Scheme.ProEt.topology (Spec (.of κ))) Ab.{u + 1} ⋙ E).LaxMonoidal

/-- Constants followed by the inverse of the canonical continuous coefficient realization.
Source: HRS Example 3.1, constant sections
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def normedPointScalar (F : Type u) [NormedField F] [TotallyDisconnectedSpace F]
    (κ : Type u) [Field κ] :
    AddCommGrpCat.of (ULift.{u + 1} F) ⟶
      (normedPointSections κ).obj (condensedRingObj (normContinuousRing F).X (Spec (.of κ))) :=
  AddCommGrpCat.ofHom
    { toFun := fun a ↦ ULift.up (ContinuousMap.const (Spec (.of κ)) a.down)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl } ≫
    (normedPointSections κ).map (condensedFieldContinuousMapIso F (Spec (.of κ))).inv.hom

/-- Constants preserve unit and multiplication for the sectionwise lax tensor structure.
Source: HRS Example 3.1 and Lemma 4.1, proof step 1
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: evaluate both diagrams on pure tensors. Multiplication of constant functions is
constant multiplication; the coefficient realization is a ring-object isomorphism. -/
theorem normedPointScalar_isMonHom (F : Type u) [NormedField F]
    [TotallyDisconnectedSpace F] (κ : Type u) [Field κ] :
    IsMonHom (normedPointScalar F κ) := by sorry

attribute [instance] normedPointScalar_isMonHom

/-- The exact inverse-image encoding with the canonical pulled-back coefficient isomorphism.
Source: HRS Section 3, exact module inverse image
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def normedModuleInverseImage
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y) ⋙
    Mod.comap (inv (condensedPullbackHom Λ f))

/-- Identification of the concrete inverse-image encoding with the recorded module pullback.
Source: HRS Section 3, module inverse image
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def normedModuleInverseImageIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    normedModuleInverseImage Λ f ≅ CondensedRing.upperStar Λ f :=
  Functor.isoWhiskerLeft ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).symm

/-- Pullback followed by final-object sections, with the constant-section scalar action.
Source: HRS Section 3 and Lemma 4.1
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def normedGeometricFibre (F : Type u) [NormedField F] [TotallyDisconnectedSpace F]
    {Z : Scheme.{u}} (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ Z) :
    Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (normContinuousRing F).X Z) ⥤ ModuleCat.{u + 1} F :=
  normedModuleInverseImage (normContinuousRing F).X x ⋙
    (normedPointSections κ).mapMod
      (condensedRingObj (normContinuousRing F).X (Spec (.of κ))) ⋙
    Mod.comap (normedPointScalar F κ) ⋙
    CondensedQbarGeometricEvaluation.ordinary (ULift.{u + 1} F) ⋙
    ModuleCat.restrictScalars ULift.ringEquiv.symm.toRingHom

/-- The geometric fibre is additive and exact for every module, without constructibility.
Source: HRS Section 3 and Lemma 4.1, proof steps 1--2
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: Spec κ is strictly henselian and has one extremally disconnected component,
hence is w-contractible. Final-object sections are exact. Module inverse image is exact;
the constant-section action only changes the encoding of the resulting vector space. -/
theorem normedGeometricFibre_exact (F : Type u) [NormedField F]
    [TotallyDisconnectedSpace F] {Z : Scheme.{u}} (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ Z) :
    (normedGeometricFibre F κ x).Additive ∧
      PreservesFiniteLimits (normedGeometricFibre F κ x) ∧
      PreservesFiniteColimits (normedGeometricFibre F κ x) := by sorry


/-- Additivity of the concrete fibre.
Source: HRS Lemma 4.1, proof step 2
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: take the additive clause of normedGeometricFibre_exact. -/
theorem normedGeometricFibre_additive (F : Type u) [NormedField F]
    [TotallyDisconnectedSpace F] {Z : Scheme.{u}} (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ Z) : (normedGeometricFibre F κ x).Additive := by sorry

/-- Left exactness of the concrete fibre.
Source: HRS Lemma 4.1, proof step 2
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: take the finite-limit clause of normedGeometricFibre_exact. -/
theorem normedGeometricFibre_limits (F : Type u) [NormedField F]
    [TotallyDisconnectedSpace F] {Z : Scheme.{u}} (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ Z) : PreservesFiniteLimits (normedGeometricFibre F κ x) := by sorry

/-- Right exactness of the concrete fibre.
Source: HRS Lemma 4.1, proof step 2
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: take the finite-colimit clause of normedGeometricFibre_exact. -/
theorem normedGeometricFibre_colimits (F : Type u) [NormedField F]
    [TotallyDisconnectedSpace F] {Z : Scheme.{u}} (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ Z) : PreservesFiniteColimits (normedGeometricFibre F κ x) := by sorry

attribute [instance] normedGeometricFibre_additive normedGeometricFibre_limits
  normedGeometricFibre_colimits

/-- The fibre is symmetric monoidal and takes the coefficient module to the field.
Source: HRS Lemma 4.1, proof steps 1--3
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: terminal sections commute with sheafification on Spec κ. The sheafified balanced
tensor therefore evaluates to the algebraic tensor over F. Inverse image preserves tensor;
the tensorator is the pure-tensor map. Associativity, unit and symmetry follow on pure
tensors. Constants identify sections of the coefficient ring with F. -/
theorem normedGeometricFibre_symmetricMonoidal (F : Type u) [NormedField F]
    [TotallyDisconnectedSpace F] {Z : Scheme.{u}} (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ Z) :
    Nonempty (normedGeometricFibre F κ x ⋙ ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv.toRingHom : ULift.{u + 1} F →+* F)).Braided ∧
      Nonempty ((normedGeometricFibre F κ x).obj
        (Mod.regular (condensedRingObj (normContinuousRing F).X Z)) ≅
        ModuleCat.of F (ULift.{u + 1} F)) := by sorry

/-- Termwise application, localized at quasi-isomorphisms, on the ordinary unbounded D.
Source: HRS Section 3, proof step 4
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def normedDerivedGeometricFibre (F : Type u) [NormedField F] [TotallyDisconnectedSpace F]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} F)]
    {Z : Scheme.{u}} (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ Z) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (normContinuousRing F).X Z)) ⥤
    DerivedCategory (ModuleCat.{u + 1} F) :=
  (normedGeometricFibre F κ x).mapDerivedCategory

/-- The derived fibre is t-exact for the standard t-structures.
Source: HRS Section 3, proof step 4
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: exactness commutes with kernels, images and cokernels, hence with H^q in every
integer degree. It preserves the two standard cohomological vanishing conditions. -/
theorem normedDerivedGeometricFibre_tExact (F : Type u) [NormedField F]
    [TotallyDisconnectedSpace F] [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} F)]
    {Z : Scheme.{u}} (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ Z) :
    (normedDerivedGeometricFibre F κ x).IsTExact
      DerivedCategory.TStructure.t DerivedCategory.TStructure.t := by sorry

/-- Finite constant local models on the strata have finite-dimensional geometric fibres.
Source: HRS Section 3 and Lemma 4.1, proof step 5
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: factor the field-valued point through its stratum. Pull a local-model cover to
Spec κ; w-contractibility and the one-point clopen partition split a member. A finitely
presented F-module is finite free. Pulling back its model and evaluating gives F^r,
including rank zero. -/
theorem normedGeometricFibre_finiteDimensional (F : Type u) [NormedField F]
    [TotallyDisconnectedSpace F] (Z : Scheme.{u}) [CompactSpace Z] [IsLocallyNoetherian Z]
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (normContinuousRing F).X Z))
    (S : Scheme.FiniteLocallyClosedStratification Z)
    (_hS : ∀ i, Topology.IsConstructible (S.stratum i))
    (_hM : ∀ i, HasFiniteConstantLocalModel (normContinuousRing F).X (S.domain i)
      ((CondensedRing.upperStar (normContinuousRing F).X (S.immersion i)).obj M))
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ Z) :
    FiniteDimensional F ((normedGeometricFibre F κ x).obj M) := by sorry

/-- Constructible sheaf morphisms are detected by these fibres.
Source: HRS Section 3, matrix and strata argument, proof steps 6--7
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: refine the source and target stratifications by intersections. On a common cover
of each stratum the morphism is a finite matrix of continuous functions. Its values at
geometric points are invertible; its determinant never vanishes, and adjugate divided by
the determinant is a continuous inverse. Cover restriction detects isomorphisms. Refine
to a finite good stratification and induct through initial open unions using the
quasi-compact open--closed short exact sequence on kernels and cokernels. Empty charts
and the empty scheme require no point. -/
theorem normedGeometricFibre_reflectsIso (F : Type u) [NormedField F]
    [TotallyDisconnectedSpace F] (Z : Scheme.{u}) [CompactSpace Z] [IsLocallyNoetherian Z]
    {M N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (normContinuousRing F).X Z)}
    (_hM : IsFiniteConstantStratified (normContinuousRing F).X Z M)
    (_hN : IsFiniteConstantStratified (normContinuousRing F).X Z N) (f : M ⟶ N)
    (_hf : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ Z),
      IsIso ((normedGeometricFibre F κ x).map f)) : IsIso f := by sorry

/-- The fibres jointly reflect isomorphisms between bounded constructible complexes.
Source: HRS Section 3, proof step 8
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: t-exactness identifies every cohomology fibre map with the fibre of H^q(f).
The preceding sheaf detection gives invertibility of each H^q(f), so the cone is acyclic
and f is invertible in the ordinary unbounded derived category. No constructibility
of the cone is assumed. -/
theorem normedDerivedGeometricFibre_reflectsIso (F : Type u) [NormedField F]
    [TotallyDisconnectedSpace F] [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} F)]
    (Z : Scheme.{u}) [CompactSpace Z] [IsLocallyNoetherian Z]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (normContinuousRing F).X Z))}
    (_hK : constantModelBoundedConstructible (normContinuousRing F).X Z K)
    (_hL : constantModelBoundedConstructible (normContinuousRing F).X Z L) (f : K ⟶ L)
    (_hf : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ Z),
      IsIso ((normedDerivedGeometricFibre F κ x).map f)) : IsIso f := by sorry


section Scalars
variable {F F' : Type u} [NormedField F] [NormedField F']
  [TotallyDisconnectedSpace F] [TotallyDisconnectedSpace F']
  (i : F →+* F') (hi : Continuous i)
  {Z : Scheme.{u}} (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ Z)

/-- Both restriction routes have the same underlying abelian group of sections.
Source: HRS Section 3, proof step 9
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: inverse image and final-object sections are identical on the underlying sheaf;
restriction only precomposes its scalar action, leaving its group and maps unchanged. -/
theorem normedFibreRestrictionUnderlying_eq
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (normContinuousRing F').X Z)) :
    (forget₂ (ModuleCat.{u + 1} F) Ab.{u + 1}).obj
        ((Mod.comap (normContinuousCoefficientMap Z i hi) ⋙
          normedGeometricFibre F κ x).obj M) =
      (forget₂ (ModuleCat.{u + 1} F) Ab.{u + 1}).obj
        ((normedGeometricFibre F' κ x ⋙ ModuleCat.restrictScalars.{u + 1} i).obj M) := by sorry

/-- The exact fibre/restriction comparison is uniquely fixed by its identity additive map.
Source: HRS Section 3, proof step 9
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: restriction retains the underlying abelian sheaf. Both composites apply abelian
inverse image and terminal sections. Naturality of continuous coefficient realization
identifies their actions, so the identity additive map is F-linear and natural. Faithful
forgetting of module maps gives uniqueness. This holds on all module objects. -/
theorem normedFibreRestriction_existsUnique :
    ∃! e : Mod.comap (normContinuousCoefficientMap Z i hi) ⋙ normedGeometricFibre F κ x ≅
        normedGeometricFibre F' κ x ⋙ ModuleCat.restrictScalars.{u + 1} i,
      ∀ M, (forget₂ (ModuleCat.{u + 1} F) Ab.{u + 1}).map (e.hom.app M) =
        eqToHom (normedFibreRestrictionUnderlying_eq i hi κ x M) := by sorry

/-- The canonical restriction comparison; its identity-map specification determines it.
Source: HRS Section 3, proof step 9
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def normedFibreRestrictionIso :
    Mod.comap (normContinuousCoefficientMap Z i hi) ⋙ normedGeometricFibre F κ x ≅
      normedGeometricFibre F' κ x ⋙ ModuleCat.restrictScalars.{u + 1} i :=
  (normedFibreRestriction_existsUnique i hi κ x).exists.choose

/-- The ordinary balanced scalar comparison is the adjunct of the insertion-of-one map.
Source: HRS Section 3, proof steps 10--11
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def normedFibreScalarComparison
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (normContinuousRing F).X Z)) :
    (ModuleCat.extendScalars.{u, u, u + 1} i).obj ((normedGeometricFibre F κ x).obj M) ⟶
      (normedGeometricFibre F' κ x).obj ((normContinuousExtension Z i hi).obj M) :=
  ((ModuleCat.extendRestrictScalarsAdj.{u + 1} i).homEquiv _ _).symm
    ((normedGeometricFibre F κ x).map
      ((Mod.extendRestrictAdjunction (normContinuousCoefficientMap Z i hi)).unit.app M) ≫
      (normedFibreRestrictionIso i hi κ x).hom.app ((normContinuousExtension Z i hi).obj M))

/-- Additivity of the actual internal extension of scalars.
Source: HRS Section 3, proof step 10
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: the extension/restriction adjunction has additive restriction, so its left
adjoint is additive; equivalently use bilinearity of the balanced tensor construction. -/
theorem normedInternalScalarExtension_additive : (normContinuousExtension Z i hi).Additive :=
  by sorry

attribute [instance] normedInternalScalarExtension_additive

/-- Naturality of the balanced map, including arbitrary modules.
Source: HRS Section 3, proof steps 10--11
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: insertion of one is the extension/restriction adjunction unit, hence natural.
The restriction comparison is natural; taking the adjoint gives the claimed equation. -/
theorem normedFibreScalarComparison_naturality
    {M N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (normContinuousRing F).X Z)} (f : M ⟶ N) :
    (ModuleCat.extendScalars.{u, u, u + 1} i).map ((normedGeometricFibre F κ x).map f) ≫
        normedFibreScalarComparison i hi κ x N =
      normedFibreScalarComparison i hi κ x M ≫
        (normedGeometricFibre F' κ x).map ((normContinuousExtension Z i hi).map f) := by sorry

/-- The actual balanced scalar comparison as a natural transformation.
Source: HRS Section 3, proof steps 10--11
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def normedFibreScalarTransformation :
    normedGeometricFibre F κ x ⋙ ModuleCat.extendScalars.{u, u, u + 1} i ⟶
      normContinuousExtension Z i hi ⋙ normedGeometricFibre F' κ x where
  app := normedFibreScalarComparison i hi κ x
  naturality _ _ f := normedFibreScalarComparison_naturality i hi κ x f

/-- Additivity of ordinary vector-space scalar extension in the ambient module universe.
Source: HRS Section 3, proof step 10
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: extension is left adjoint to the additive restriction functor; the induced linear
map sends pure tensors to pure tensors, and hence preserves sums of morphisms. -/
theorem normedVectorScalarExtension_additive :
    (ModuleCat.extendScalars.{u, u, u + 1} i).Additive := by sorry

/-- Right exactness of ordinary vector-space scalar extension.
Source: HRS Section 3, proof step 10
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: the explicit extension/restriction adjunction shows that extension preserves
colimits, in particular finite colimits. -/
theorem normedVectorScalarExtension_colimits :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1} i) := by sorry

attribute [instance] normedVectorScalarExtension_additive normedVectorScalarExtension_colimits

/-- Exact algebraic scalar extension between vector spaces.
Source: HRS Section 3, proof step 10; Stacks field scalar extension
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: every module over the abstract field F is free, hence flat. Tensoring with F'
is exact, independently of the topology or flatness of the condensed coefficient map. -/
theorem normedVectorScalarExtension_limits :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1} i) := by sorry

attribute [instance] normedVectorScalarExtension_limits

/-- Insertion of one is preserved by the specified ordinary balanced comparison.
Source: HRS Section 3, proof step 11
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: the comparison was defined as the adjunct of the module insertion-of-one unit
followed by the identity-map restriction comparison. Apply the adjunction equation. -/
theorem normedFibreScalarComparison_unit
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (normContinuousRing F).X Z)) :
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} i).unit.app
        ((normedGeometricFibre F κ x).obj M) ≫
      (ModuleCat.restrictScalars.{u + 1} i).map
        (normedFibreScalarComparison i hi κ x M) =
    (normedGeometricFibre F κ x).map
        ((Mod.extendRestrictAdjunction (normContinuousCoefficientMap Z i hi)).unit.app M) ≫
      (normedFibreRestrictionIso i hi κ x).hom.app
        ((normContinuousExtension Z i hi).obj M) := by sorry

variable [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} F)]
  [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} F')]

/-- The exact restriction comparison also holds termwise on the unbounded derived categories.
Source: HRS Section 3, proof step 9
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: apply the ordinary identity-map restriction comparison in each degree. Both
restriction functors and both fibres are exact, hence preserve quasi-isomorphisms;
localization gives this natural isomorphism without boundedness assumptions. -/
theorem normedDerivedFibreRestriction :
    Nonempty ((Mod.comap (normContinuousCoefficientMap Z i hi)).mapDerivedCategory ⋙
      normedDerivedGeometricFibre F κ x ≅
      normedDerivedGeometricFibre F' κ x ⋙
        (ModuleCat.restrictScalars.{u + 1} i).mapDerivedCategory) := by sorry

/-- The exact termwise scalar extension of the fibre, representing F' tensor^L_F Phi.
Source: HRS Section 3, proof step 10
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def normedFibreScalarDerivedSource :=
  (normedGeometricFibre F κ x ⋙ ModuleCat.extendScalars.{u, u, u + 1} i).mapDerivedCategory

/-- The fibre of the ordinary unbounded total derived internal scalar extension.
Source: HRS Section 3, proof step 10
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def normedFibreScalarDerivedTarget :=
  (normContinuousExtension Z i hi).leftDerivedFunctor ⋙ normedDerivedGeometricFibre F' κ x

/-- Additivity of scalar extension followed by the target fibre.
Source: HRS Section 3, proof step 10
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: compose additivity of internal extension with additivity of the geometric fibre. -/
theorem normedFibreScalarTarget_additive :
    (normContinuousExtension Z i hi ⋙ normedGeometricFibre F' κ x).Additive := by sorry

attribute [instance] normedFibreScalarTarget_additive

/-- The K-flat representative square specifies the balanced derived comparison, including
its insertion-of-one normalization through the specified ordinary transformation.
Source: HRS Section 3, proof steps 10--11
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def NormedFibreScalarDerivedNormalized
    (δ : normedFibreScalarDerivedSource i κ x ≅ normedFibreScalarDerivedTarget i hi κ x) :
    Prop :=
  ∀ P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (normContinuousRing F).X Z)) ℤ,
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    δ.hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (normedDerivedGeometricFibre F' κ x).map
        ((normContinuousExtension Z i hi).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (normedGeometricFibre F' κ x).mapDerivedCategoryFactorsh.hom.app
        (((normContinuousExtension Z i hi).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
    (normedGeometricFibre F κ x ⋙
        ModuleCat.extendScalars.{u, u, u + 1} i).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        ((@NatTrans.mapHomotopyCategory ℤ _ _ _ _ _ _
          (normedGeometricFibre F κ x ⋙ ModuleCat.extendScalars.{u, u, u + 1} i)
          (normContinuousExtension Z i hi ⋙ normedGeometricFibre F' κ x)
          inferInstance (normedFibreScalarTarget_additive i hi κ x)
          (normedFibreScalarTransformation i hi κ x) (.up ℤ)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
        (@Functor.mapHomotopyCategoryCompIso ℤ _ _ _ _ _ _ _ _ _
          (normContinuousExtension Z i hi) (normedGeometricFibre F' κ x)
          (normContinuousExtension Z i hi ⋙ normedGeometricFibre F' κ x) (Iso.refl _)
          (normedInternalScalarExtension_additive i hi (Z := Z))
          (normedGeometricFibre_additive F' κ x)
          (normedFibreScalarTarget_additive i hi κ x) (.up ℤ)).inv.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The canonical derived scalar comparison is an isomorphism for every unbounded complex.
Source: HRS Section 3, proof steps 9--11
(blueprint: lem-sfb-constructible-normed-geometric-fibres).
Proof: resolve by a K-flat P over F_Z. Internal extension of P computes its total left
derived extension. Pullback commutes with extension, and final-object sections over
Spec κ are unchanged by sheafification. Thus the ordinary balanced map evaluates in
each degree to F' tensor_F Phi(P), sending a tensor m to a tensor m. Abstract field
extension is exact, so this represents the derived tensor of Phi(K), for unbounded K
as well. These maps commute with differentials and replacement maps, giving the
normalized derived isomorphism. K-flat resolutions determine transformations on D,
so the square gives uniqueness. At m maps to 1 tensor m both routes agree by the
ordinary unit equation. No completeness or condensed flatness is used. -/
theorem normedFibreScalarDerived_existsUnique :
    ∃! δ : normedFibreScalarDerivedSource i κ x ≅ normedFibreScalarDerivedTarget i hi κ x,
      NormedFibreScalarDerivedNormalized i hi κ x δ := by sorry

/-- The specified comparison selected from its unique K-flat representative specification.
Source: HRS Section 3, proof steps 10--11
(blueprint: lem-sfb-constructible-normed-geometric-fibres). -/
def normedFibreScalarDerivedIso :
    normedFibreScalarDerivedSource i κ x ≅ normedFibreScalarDerivedTarget i hi κ x :=
  (normedFibreScalarDerived_existsUnique i hi κ x).exists.choose

end Scalars
end AlgebraicGeometry.ProEtale
