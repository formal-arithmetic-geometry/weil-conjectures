/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral

/-!
# Compatible changes of ring sheaves and derived adjunctions

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0D6E and 07A6;
Modules on Sites, lemma-adjoint-push-pull-modules
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Restriction along a commutative ring-sheaf map on the original small site.
Source: Stacks, Modules on Sites (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable abbrev proEtaleRingRestrictScalars {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    proEtaleRingModules T S ⥤ proEtaleRingModules T R :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)

/-- Restriction is exact and conservative before deriving.
Source: Stacks, Derived Categories, Tag 05RT
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
Proof: restriction leaves the underlying abelian sheaf and its kernels and sheafified
cokernels unchanged. A bijective linear sheaf map has a linear inverse: apply the map
to the proposed scalar-linearity equality for its inverse. Thus restriction reflects
isomorphisms and preserves finite limits and finite colimits. -/
theorem proEtaleRingRestrictScalars_properties {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteLimits (proEtaleRingRestrictScalars a) ∧
    PreservesFiniteColimits (proEtaleRingRestrictScalars a) ∧
    (proEtaleRingRestrictScalars a).ReflectsIsomorphisms := by
  sorry

/-- Left exactness of restriction. Source: Stacks, Tag 05RT
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
theorem proEtaleRingRestrictScalars_preservesFiniteLimits {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteLimits (proEtaleRingRestrictScalars a) :=
  (proEtaleRingRestrictScalars_properties a).1

attribute [local instance] proEtaleRingRestrictScalars_preservesFiniteLimits

/-- Right exactness of restriction. Source: Stacks, Tag 05RT
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
theorem proEtaleRingRestrictScalars_preservesFiniteColimits {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteColimits (proEtaleRingRestrictScalars a) :=
  (proEtaleRingRestrictScalars_properties a).2.1

attribute [local instance] proEtaleRingRestrictScalars_preservesFiniteColimits

variable {U V : Scheme.{u}} (f : U ⟶ V)
  (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
  (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
  (aV : RV ⟶ SV) (aU : RU ⟶ SU)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
  (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)

include comm in
/-- The underived comparison is uniquely specified by identity on every section.
Source: Stacks, Tag 0D6E (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
Proof: both composites have sections `N(U ×_V W)`. Their actions coincide by taking
adjoints of the coefficient-square identity. Identity on those sections is linear,
commutes with restrictions and module maps, and is its own inverse. Sectionwise
faithfulness determines the natural isomorphism uniquely. -/
theorem proEtaleRingRestrictionDirectImage_existsUnique :
    ∃! e : proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV ≅
        proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR,
      ∀ (N : proEtaleRingModules U SU) (W : V.ProEtᵒᵖ)
        (n : N.val.obj ((proEtaleBaseChange f).op.obj W)),
        (e.hom.app N).val.app W n = n := by
  sorry

/-- Canonical direct-image comparison, determined by the actual identity on sections.
Source: Stacks, Tag 0D6E (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable def proEtaleRingRestrictionDirectImage :
    proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV ≅
      proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR :=
  Classical.choose
    (proEtaleRingRestrictionDirectImage_existsUnique f RV SV RU SU aV aU cR cS comm)

/-- The inverse-image comparison before inversion is the mate of identity on sections.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable def proEtaleRingRestrictionPullbackApp (M : proEtaleRingModules V SV) :
    (proEtaleRingModulePullback f RV RU cR).obj ((proEtaleRingRestrictScalars aV).obj M) ⟶
      (proEtaleRingRestrictScalars aU).obj ((proEtaleRingModulePullback f SV SU cS).obj M) :=
  (proEtaleRingModulePullback f RV RU cR).map
    ((proEtaleRingRestrictScalars aV).map
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app M)) ≫
  (proEtaleRingModulePullback f RV RU cR).map
    ((proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom.app
      ((proEtaleRingModulePullback f SV SU cS).obj M)) ≫
  (proEtaleRingModuleAdjunction f RV RU cR).counit.app _

/-- The specified mate is natural and invertible.
Source: Stacks, Modules on Sites, lemma-adjoint-push-pull-modules
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
Proof: unit and counit naturality and naturality of the sectionwise identity give
naturality. Under the tensor-unit normalized adjunctions this mate is identity on
underlying inverse-image abelian sheaves. Its two scalar actions are equal because
`cS.inv aU = inverseImage(aV) cR.inv`, the coefficient-square equation. Hence it is
an isomorphism. No flatness of the coefficient-change maps is used. -/
theorem proEtaleRingRestrictionPullbackApp_properties :
    (∀ (M N : proEtaleRingModules V SV) (h : M ⟶ N),
      (proEtaleRingModulePullback f RV RU cR).map
          ((proEtaleRingRestrictScalars aV).map h) ≫
        proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm N =
      proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M ≫
        (proEtaleRingRestrictScalars aU).map
          ((proEtaleRingModulePullback f SV SU cS).map h)) ∧
    ∀ M : proEtaleRingModules V SV,
      IsIso (proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M) := by
  sorry

/-- The canonical ordinary inverse-image comparison, with its direction reversed.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable def proEtaleRingRestrictionPullbackInv :
    proEtaleRingRestrictScalars aV ⋙ proEtaleRingModulePullback f RV RU cR ⟶
      proEtaleRingModulePullback f SV SU cS ⋙ proEtaleRingRestrictScalars aU where
  app := proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm
  naturality := (proEtaleRingRestrictionPullbackApp_properties
    f RV SV RU SU aV aU cR cS comm).1

/-- The ordinary comparison is invertible. Source: Stacks, Modules on Sites
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
Proof: each component is invertible by the identity-on-inverse-image calculation
in proEtaleRingRestrictionPullbackApp_properties; naturality gives the inverse. -/
theorem proEtaleRingRestrictionPullbackInv_isIso :
    IsIso (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm) := by
  sorry

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso

/-- The termwise descended identified-coefficient inverse-image comparison `b`.
Source: Stacks, Tag 0D6D (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable def proEtaleRingRestrictionDerivedPullback :
    proEtaleRingDerivedPullback f SV SU cS ⋙ (proEtaleRingRestrictScalars aU).mapDerivedCategory ≅
      (proEtaleRingRestrictScalars aV).mapDerivedCategory ⋙
        proEtaleRingDerivedPullback f RV RU cR :=
  (Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback f SV SU cS)
    (proEtaleRingRestrictScalars aU)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (asIso (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm)).symm ≪≫
    Functor.mapDerivedCategoryCompIso (proEtaleRingRestrictScalars aV)
      (proEtaleRingModulePullback f RV RU cR)

/-- The right-derived unit on complexes, including the canonical quotient identifications.
Source: Stacks, Tag 07A5 (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable def proEtaleRingDirectImageDerivedUnit
    (K : CochainComplex (proEtaleRingModules U RU) ℤ) :
    DerivedCategory.Q.obj
        (((proEtaleRingModuleDirectImage f RV RU cR).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (proEtaleRingDerivedDirectImage f RV RU cR).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (proEtaleRingModuleDirectImage f RV RU cR).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj K) ≫
    (proEtaleRingDerivedDirectImage f RV RU cR).map
      ((DerivedCategory.quotientCompQhIso _).hom.app K)

/-- The direct-image comparison is the unique comparison compatible with the derived
units and the identity-on-sections underived comparison.
Source: Stacks, Tag 0D6E (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
Proof: regard both sides as the derived direct image of the same composite ringed-topos
morphism. The exact vertical direct images are termwise restriction. The composition
comparison supplies an invertible map compatible with the derived units. On a K-injective
complex I over SU and a K-injective resolution j of its RU-restriction, that map is
represented by directImage(j), which is a quasi-isomorphism by the composition theorem.
This does not assume that restriction preserves K-injectivity. The unit normalization
uniquely determines the comparison on K-injectives and hence everywhere by localization. -/
theorem proEtaleRingRestrictionDerivedDirectImage_existsUnique :
    ∃! d : proEtaleRingDerivedDirectImage f SV SU cS ⋙
        (proEtaleRingRestrictScalars aV).mapDerivedCategory ≅
      (proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage f RV RU cR,
      ∀ K : CochainComplex (proEtaleRingModules U SU) ℤ,
        (proEtaleRingRestrictScalars aV).mapDerivedCategory.map
            (proEtaleRingDirectImageDerivedUnit f SV SU cS K) ≫
          d.hom.app (DerivedCategory.Q.obj K) ≫
          (proEtaleRingDerivedDirectImage f RV RU cR).map
            ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app K) =
        (proEtaleRingRestrictScalars aV).mapDerivedCategoryFactors.hom.app
            (((proEtaleRingModuleDirectImage f SV SU cS).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm)
                (.up ℤ)).hom.app K) ≫
          proEtaleRingDirectImageDerivedUnit f RV RU cR
            (((proEtaleRingRestrictScalars aU).mapHomologicalComplex (.up ℤ)).obj K) := by
  sorry

/-- The canonical derived direct-image comparison `d`, determined by its unit normalization.
Source: Stacks, Tag 0D6E (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable def proEtaleRingRestrictionDerivedDirectImage :
    proEtaleRingDerivedDirectImage f SV SU cS ⋙
        (proEtaleRingRestrictScalars aV).mapDerivedCategory ≅
      (proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage f RV RU cR :=
  Classical.choose
    (proEtaleRingRestrictionDerivedDirectImage_existsUnique f RV SV RU SU aV aU cR cS comm)

/-- Exact restriction reflects derived isomorphisms, and the canonical coefficient
comparisons intertwine the canonical derived adjunctions.
Source: Stacks, Tags 05RT, 0D6D, 0D6E and 07A6
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
Proof: (1) restriction leaves underlying abelian kernels and sheafified cokernels
unchanged, so is exact and conservative. It commutes with cohomology; the unbounded
cohomology criterion therefore implies conservativity after localization.
(2) the inverse-image comparison is identity on the inverse-image abelian sheaf, with
the two scalar actions identified by the coefficient square. Descend it termwise.
(3) the two ringed-topos composites have identical structural maps; exact vertical
restriction identifies their derived direct images with termwise restriction.
(4) the derived direct-image composition theorem gives d, represented on K-injective
I and a K-injective resolution j of its restriction by directImage(j).
(5) represent t by a chain map into I. Its transpose is the ordinary module transpose
followed by the derived unit. After restriction and passage to j its transpose is
directImage(j) composed with that restricted transpose, by naturality of the ordinary
adjunction. The canonical pre-derived adjunction fraction formula then identifies this
with both sides of the displayed equation. Homotopies and canonical resolution
identifications make the equality valid for every derived M, N and t. -/
theorem proEtaleRingSheafChangeAdjunction :
    (proEtaleRingRestrictScalars aU).mapDerivedCategory.ReflectsIsomorphisms ∧
    (proEtaleRingRestrictScalars aV).mapDerivedCategory.ReflectsIsomorphisms ∧
    ∀ (M : DerivedCategory (proEtaleRingModules V SV))
      (N : DerivedCategory (proEtaleRingModules U SU))
      (t : (proEtaleRingDerivedPullback f SV SU cS).obj M ⟶ N),
      (proEtaleRingDerivedAdjunction f RV RU cR).homEquiv _ _
          ((proEtaleRingRestrictionDerivedPullback
              f RV SV RU SU aV aU cR cS comm).inv.app M ≫
            (proEtaleRingRestrictScalars aU).mapDerivedCategory.map t) =
        (proEtaleRingRestrictScalars aV).mapDerivedCategory.map
            ((proEtaleRingDerivedAdjunction f SV SU cS).homEquiv M N t) ≫
          (proEtaleRingRestrictionDerivedDirectImage
            f RV SV RU SU aV aU cR cS comm).hom.app N := by
  sorry

end AlgebraicGeometry.Scheme
