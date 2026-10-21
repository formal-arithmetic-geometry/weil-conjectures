/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Sheaf.Algebra.Homology.ScalarInternalHomData
public import Sheaf.CategoryTheory.SheafTensorStructure
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SheafRingDerivedHomComparison
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-! # Scalar adjunctions under section reconstruction

Source: Stacks Project, Modules on Sites, Tags 03EK and 0GMW; Cohomology on Sites,
Tags 06YS, 06YY and 07A6; Derived Categories, Tag 09T5; blueprint main-20261015,
det-prop-scalar-six-pullback.proof.md, (1), first paragraph
(blueprint: lem-sfb-internal-section-scalar-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u c v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings
attribute [instance] SheafOfModules.ScalarDerivedPair.extension_additive

namespace CategoryTheory.InternalAbelianSheafModule

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max c v, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]

/-- The section-ring map reconstructed from the specified internal ring map.
Source: Stacks 03EK (blueprint: lem-sfb-internal-section-scalar-adjunction). -/
def sectionScalarMap {R S : Sheaf J AddCommGrpCat.{u}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] : sectionRingSheaf J R ⟶ sectionRingSheaf J S :=
  ⟨Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence Cᵒᵖ AddCommGrpCat.{u}).functor.map
      ((sheafToPresheaf J AddCommGrpCat.{u}).mapCommMon.map
        (CommMon.homMk (A := CommMon.mk R) (B := CommMon.mk S) (Mon.Hom.mk' a)))) commMonToRing⟩

variable {R S : Sheaf J AddCommGrpCat.{u}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]

/-- The balanced generator in internal coequalizer extension.
Source: Stacks 03EK (blueprint: lem-sfb-internal-section-scalar-adjunction). -/
def internalScalarGenerator (M : Mod (Sheaf J AddCommGrpCat.{u}) R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (m : M.X.obj.obj U) :
    ((Mod.extendScalars a).obj M).X.obj.obj U :=
  ((Mod.extendπ a M).hom.app U)
    (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) S M.X).app U)
      (s ⊗ₜ[ℤ] m))

/-- Internal modules for the scalar comparison; this is the recorded module category.
Source: Stacks 03EK (blueprint: lem-sfb-internal-section-scalar-adjunction). -/
abbrev scalarInternalModules (T : Sheaf J AddCommGrpCat.{u}) [MonObj T] :=
  Mod (Sheaf J AddCommGrpCat.{u}) T

variable [HasDerivedCategory.{w} (scalarInternalModules J R)]
  [HasDerivedCategory.{w} (scalarInternalModules J S)]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J R))]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J S))]

/-- The complete normalized comparison, using the actual internal coequalizer extension,
actual sectionwise sheafification, and universal unbounded derived pairs. This proposition
asserts existence of the comparison data with all their normalization properties.
Source: Stacks 03EK, 0GMW, 06YS, 06YY, 07A6 and 09T5
(blueprint: lem-sfb-internal-section-scalar-adjunction). -/
def InternalSectionScalarAdjunction : Prop :=
  -- The recorded normalized sectionwise extension and its derived adjunction.
  ∃ sectionPair : (SheafOfModules.ScalarDerivedPair (sectionScalarMap J a)),
  -- Restriction commutes with reconstruction.
  ∃ restriction : (Mod.comap a ⋙ (sectionModuleEquivalence J R).functor ≅
    (sectionModuleEquivalence J S).functor ⋙
      SheafOfModules.scalarRestriction (sectionScalarMap J a)),
  -- The restriction identification is the identity on underlying sections.
  (∀ (N : scalarInternalModules J S) (U : Cᵒᵖ)
    (x : N.X.obj.obj U), (restriction.hom.app N).val.app U x = x) ∧
  -- Extension commutes with reconstruction.
  ∃ extension : (Mod.extendScalars a ⋙ (sectionModuleEquivalence J S).functor ≅
    (sectionModuleEquivalence J R).functor ⋙ sectionPair.extension),
  -- The comparison preserves every balanced generator, with no scalar twist.
  (∀ (M : scalarInternalModules J R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (m : M.X.obj.obj U),
    ((eqToHom
      (sectionPair.extension_obj ((sectionModuleEquivalence J R).functor.obj M))).val.app U)
        ((extension.hom.app M).val.app U (internalScalarGenerator J a M U s m)) =
      (toSheafify J (SheafOfModules.changeOfRingsPresheaf (sectionScalarMap J a)
        ((sectionModuleEquivalence J R).functor.obj M)).presheaf).app U
          (s ⊗ₜ[(sectionRingSheaf J R).obj.obj U, ((sectionScalarMap J a).hom.app U).hom] m)) ∧
  -- The specified ordinary Hom adjunctions agree, hence so do unit and counit.
  (∀ (M : scalarInternalModules J R) (N : scalarInternalModules J S)
    (f : (Mod.extendScalars a).obj M ⟶ N),
    (sectionModuleEquivalence J R).functor.map
        ((Mod.extendRestrictAdjunction a).homEquiv M N f) ≫ restriction.hom.app N =
      sectionPair.ordinaryAdjunction.homEquiv _ _
        (extension.inv.app M ≫ (sectionModuleEquivalence J S).functor.map f)) ∧
  -- The internal unbounded derived scalar extension.
  ∃ internalDerived : (DerivedCategory (scalarInternalModules J R) ⥤
    DerivedCategory (scalarInternalModules J S)),
  -- Its comparison on the actual complexes.
  ∃ internalCounit : (DerivedCategory.Q ⋙ internalDerived ⟶
    (Mod.extendScalars a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
  -- This is the universal left derived functor, not an arbitrary left adjoint.
  (internalDerived.IsLeftDerivedFunctor internalCounit
    (HomologicalComplex.quasiIso (scalarInternalModules J R) (.up ℤ))) ∧
  -- K-flat complexes compute the internal universal pair. K-flatness is transported
  -- by the recorded equivalence, as in internal_section_tensor_comparison.
  (∀ (P : CochainComplex (scalarInternalModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := sectionRingSheaf J R)
      (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj P) →
        IsIso (internalCounit.app P)) ∧
  -- The specified internal derived extension/exact restriction adjunction.
  ∃ internalAdjunction : (internalDerived ⊣ (Mod.comap a).mapDerivedCategory),
  -- The internal derived unit is induced by the specified ordinary internal unit.
  -- This pins the derived adjunction independently of section reconstruction.
  (∀ (P : CochainComplex (scalarInternalModules J R) ℤ),
    internalAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (Mod.comap a).mapDerivedCategory.map (internalCounit.app P) ≫
        (Mod.comap a).mapDerivedCategoryFactors.hom.app
          (((Mod.extendScalars a).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((Mod.extendRestrictAdjunction a).mapHomologicalComplex (.up ℤ)).unit.app P)) ∧
  -- The termwise equivalences identify derived restrictions.
  ∃ derivedRestriction : ((Mod.comap a).mapDerivedCategory ⋙
      (sectionModuleEquivalence J R).functor.mapDerivedCategory ≅
    (sectionModuleEquivalence J S).functor.mapDerivedCategory ⋙
      SheafOfModules.scalarDerivedRestriction (sectionScalarMap J a)),
  -- Restriction comparison is precisely localization of the ordinary one.
  (derivedRestriction =
    (Functor.mapDerivedCategoryCompIso (Mod.comap a)
      (sectionModuleEquivalence J R).functor).symm ≪≫
    Functor.mapDerivedCategoryNatIso restriction ≪≫
    Functor.mapDerivedCategoryCompIso (sectionModuleEquivalence J S).functor
      (SheafOfModules.scalarRestriction (sectionScalarMap J a))) ∧
  -- The comparison of the universal derived extensions.
  ∃ derivedExtension : (internalDerived ⋙
      (sectionModuleEquivalence J S).functor.mapDerivedCategory ≅
    (sectionModuleEquivalence J R).functor.mapDerivedCategory ⋙ sectionPair.derived),
  -- On flat-term K-flat representatives, this is the localized termwise comparison.
  (∀ (P : CochainComplex (scalarInternalModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := sectionRingSheaf J R)
      (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj P) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := sectionRingSheaf J R)
      ((sectionModuleEquivalence J R).functor.obj (P.X n))) →
    (sectionModuleEquivalence J S).functor.mapDerivedCategory.map (internalCounit.app P) ≫
        (sectionModuleEquivalence J S).functor.mapDerivedCategoryFactors.hom.app
          (((Mod.extendScalars a).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex extension (.up ℤ)).hom.app P) =
      derivedExtension.hom.app (DerivedCategory.Q.obj P) ≫
        sectionPair.derived.map
          ((sectionModuleEquivalence J R).functor.mapDerivedCategoryFactors.hom.app P) ≫
        SheafOfModules.scalarPairComplexComparison sectionPair.extension
          sectionPair.extension_additive sectionPair.derived sectionPair.counit
          (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj P)) ∧
  -- Agreement of the specified derived transposes includes derived units and counits.
  ∀ (M : DerivedCategory (scalarInternalModules J R))
      (N : DerivedCategory (scalarInternalModules J S)) (f : internalDerived.obj M ⟶ N),
      (sectionModuleEquivalence J R).functor.mapDerivedCategory.map
          (internalAdjunction.homEquiv M N f) ≫ derivedRestriction.hom.app N =
        sectionPair.adjunction.homEquiv _ _ (derivedExtension.inv.app M ≫
          (sectionModuleEquivalence J S).functor.mapDerivedCategory.map f)

/-- Scalar reconstruction preserves restriction, balanced extension and their specified
ordinary and unbounded derived adjunctions, with no flatness hypothesis on the ring map.
Source: Stacks 03EK, 0GMW, 06YS, 06YY, 07A6 and 09T5; blueprint
main-20261015, det-prop-scalar-six-pullback.proof.md, (1), first paragraph
(blueprint: lem-sfb-internal-section-scalar-adjunction).

Proof:
1. Internal restriction acts on each section by a(r)n. Reconstruction leaves the
underlying sheaf and every morphism fixed, giving the identity restriction comparison.
2. Apply lem-pe-internal-section-tensor-comparison to the restricted regular S-module
and M. Both extensions impose (s a(r)) tensor m = s tensor (rm). The comparison sends
s tensor m to itself and respects the S-action. Naturality is checked on these generators
using lem-pc-sites-sheaf-tensor-bilinear-universal.
3. The ordinary transpose sends f to (m ↦ f(1 tensor m)); its inverse sends g to
(s tensor m ↦ s g(m)). Balancing and the module axioms prove they are inverse.
The generator comparison preserves these formulas, including the unit and counit.
4. The exact section equivalences preserve quasi-isomorphisms, flat objects and K-flat
complexes by lem-pe-internal-section-tensor-comparison. Localizing them and the termwise
restriction identity gives the derived equivalences and exact restriction comparison.
5. Use lem-pc-kflat-resolution on the section side and pull the resolution back through
reconstruction. Transport the universal derived pair of lem-pur-derived-change-of-rings.
Its universal property is invariant under equivalences, and its comparison on a flat-term
K-flat resolution is localization of the generator-preserving termwise isomorphism.
6. The internal derived adjunction is normalized by the ordinary internal unit:
after internalCounit and the exact comap factorization, its unit on Q(P) is Q of
the ordinary chain unit. This is the defining unit compatibility of the derived
adjunction, transported along rightDerivedComapIsoMapDerivedCategory; it depends
only on the internal ordinary adjunction and universal derived comparison.
Apply lem-pur-sheaf-ring-derived-hom-comparison. The unit roof has second arrow
p ↦ 1 tensor p; the counit on a resolution q has map s tensor p ↦ s q(p).
The ordinary and representative comparisons preserve both maps and every resolution
arrow, so the normalized derived Hom transposes, units and counits agree. No step
requires flatness of a or preservation of K-flatness by restriction. -/
theorem internal_section_scalar_adjunction : InternalSectionScalarAdjunction J a := by
  sorry

end CategoryTheory.InternalAbelianSheafModule
