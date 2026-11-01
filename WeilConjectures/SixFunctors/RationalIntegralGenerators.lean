/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.Triangulated.Generators

import WeilConjectures.AlgebraicGeometry.PadicAlgClFiniteDescent
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp

/-!
# Integral generators of rational constructible complexes

Source: Hemo--Richarz--Scholbach, Theorem 7.7 and Lemma 7.9, with the
integral-lattice dévissage of the blueprint (blueprint: lem-fd-rational-integral-generators).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.SixFunctors

/-- The finite-extension integral scalar-extension generators, up to isomorphism.
Source: Hemo--Richarz--Scholbach, Theorem 7.7, and blueprint integral-model generation
(blueprint: lem-fd-rational-integral-generators). -/
noncomputable def rationalIntegralGenerator
    (ℓ : ℕ) [Fact ℓ.Prime] (Z : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.1) Z))) := fun K ↦
  ∃ M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z)),
    boundedConstructible
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z) M ∧
      Nonempty (K ≅
        (Mod.extendScalars
          (AlgebraicGeometry.ProEtale.padicIntegersToPadicSubfield Z ℓ E)).leftDerivedFunctor.obj M)

/-- The algebraic-closure generators, allowing all finite subextensions.
Source: Hemo--Richarz--Scholbach, Theorem 7.7 and Lemma 7.9, and blueprint integral models
(blueprint: lem-fd-rational-integral-generators). -/
noncomputable def qlbarRationalIntegralGenerator
    (ℓ : ℕ) [Fact ℓ.Prime] (Z : Scheme.{u}) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z))) := fun K ↦
  ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) Z))),
    boundedConstructible
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) Z) M ∧
      Nonempty (K ≅
        (Mod.extendScalars (coefficientMap
          (padicIntegersRingObjToContinuousMapRingObj ℓ F ≫
            Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) Z)).leftDerivedFunctor.obj M)

attribute [local irreducible] upperStarFromPoint Mod.extendScalars
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory

/-- Every bounded constructible complex with finite rational coefficients lies in the
triangulated retract closure of derived scalar extensions of bounded constructible integral
complexes; the same holds for the finite-subextension-valued algebraic closure.

Source: Hemo--Richarz--Scholbach, Theorem 7.7 and Lemma 7.9, with the
integral-lattice dévissage of the blueprint (blueprint: lem-fd-rational-integral-generators).

Proof. (1) The existing rationalization localization theorem is essentially
surjective on bounded constructible finite-field complexes. A preimage and its
isomorphism under the full-subcategory inclusion show that every such complex is
already an integral scalar-extension generator, hence lies in its envelope.
(2) Finite coefficient-field descent gives a finite-field model of an
algebraic-closure complex. Apply (1) to that model and extend scalars.
(3) The coefficient map preserves composition. The existing derived
scalar-extension composition isomorphism therefore identifies this iterated
extension with the direct integral-to-algebraic-closure extension, giving an
algebraic-closure generator and hence membership in its envelope.
-/
theorem rationalIntegralGenerators
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Z : Scheme.{u}) [CompactSpace Z] [IsLocallyNoetherian Z]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E.1) Z)),
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) Z) K →
      (rationalIntegralGenerator ℓ Z E).triangEnvelope K) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)),
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z) K →
      (qlbarRationalIntegralGenerator ℓ Z).triangEnvelope K) := by
  classical
  have : IsNoetherian Z := ⟨⟩
  have model (F : PadicAlgCl.FiniteIntermediateField ℓ)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj F.1) Z)))
      (hK : boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj F.1) Z) K) :
      rationalIntegralGenerator ℓ Z F K := by
    let T := boundedConstructibleExtendScalars Z ℓ F
    have : T.EssSurj := Localization.essSurj T
      (CategoryTheory.Rationalization.W (Submonoid.powers (ℓ : ℤ)) _)
    let K' : BoundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj F.1) Z) := ⟨K, hK⟩
    let M := T.objPreimage K'
    exact ⟨M.obj, M.property,
      ⟨((boundedConstructible _).ι.mapIso (T.objObjPreimageIso K')).symm⟩⟩
  constructor
  · intro K hK
    exact (rationalIntegralGenerator ℓ Z E).le_triangEnvelope K (model E K hK)
  · intro K hK
    obtain ⟨F, KF, ⟨eF⟩, _⟩ :=
      exists_padicAlgCl_finite_descent ℓ Z ⟨K, hK⟩
    obtain ⟨M, hM, ⟨eM⟩⟩ := model F KF.obj KF.property
    apply (qlbarRationalIntegralGenerator ℓ Z).le_triangEnvelope K
    refine ⟨F, M, hM, ⟨eF.symm ≪≫
      (derivedExtendScalarsToPadicAlgCl Z ℓ F).mapIso eM ≪≫ ?_⟩⟩
    exact (Mod.derivedExtendScalarsCompIso
      (padicIntegersToPadicSubfield Z ℓ F)
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) Z)
      (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ F ≫
        Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) Z)
      ((upperStarFromPoint Z).map_comp _ _).symm).symm.app M

end WeilConjectures.SixFunctors
