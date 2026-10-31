/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTensorPullbackData

import WeilConjectures.AlgebraicGeometry.IntegralPullbackInternalRoosUnit
import WeilConjectures.AlgebraicGeometry.IntegralPullbackConstantRoosUnit
import all WeilConjectures.AlgebraicGeometry.UnboundedLocalizingPullback
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift

/-! # Integral inverse image preserves constructibility and completed pullback

Source: blueprint det-lem-int-tensor-pullback.
(blueprint: det-lem-int-tensor-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The natural completion comparison is invertible on bounded constructible inputs,
and its scalar restriction is the Stacks completed inverse image with the same unit.
All K-flat representatives are allowed; they merely compute the fixed derived objects.
Source: blueprint det-lem-int-tensor-pullback, clauses (1),(2); Stacks 099I, 099N(2),(5)
(blueprint: det-lem-int-tensor-pullback).

Proof: exact inverse image commutes with homology and preserves cohomological
bounds. Pull back the constructible stratification and the given finite local
models; their finitely presented scalar modules remain unchanged. This gives
bounded constructibility of the ordinary inverse image. The internal integral
residue criterion then makes this inverse image derived complete. Inverse image
preserves native K-flatness, so its image of any specified K-flat representative
computes its completion unit. The ordinary Roos normalization identifies that
unit with comparison, including the quotient augmentation. Cancel the source
and target isomorphisms to obtain invertibility. The independent constant Roos
normalization identifies scalar restriction with the constant quotient tower
and its normalized source map. Applying localization to its chain equality gives
the final equation.
The zero complex, empty schemes and identity morphism require no exclusions. -/
theorem preserves_and_completed
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] (g : X ⟶ Y) [g.IsOver (Spec (.of k))]
    (K : DerivedCategory (AdicCompletion.Modules l E Y))
    (_hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Y K) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X
      (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapDerivedCategory).obj K) ∧
    ∀ (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ)
      (_hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E Y) (.up ℤ)).kFlat P)
      (_eP : DerivedCategory.Q.obj P ≅ K),
      IsIso (DerivedCategory.Q.map (comparison l E g P)) ∧
      ∃ e : DerivedCategory.Q.obj
          (((restriction l E X).mapHomologicalComplex (.up ℤ)).obj
            (WeilConjectures.integralOperationsRoos (pulledTower l E g P))) ≅
          DerivedCategory.Q.obj (WeilConjectures.integralOperationsRoos
            (constantPulledTower l E g
              (((restriction l E Y).mapHomologicalComplex (.up ℤ)).obj P))),
        DerivedCategory.Q.map
            (((restriction l E X).mapHomologicalComplex (.up ℤ)).map (comparison l E g P)) ≫
            e.hom =
          DerivedCategory.Q.map (restrictionPullbackComplex l E g P).hom ≫
            DerivedCategory.Q.map (constantComparison l E g
              (((restriction l E Y).mapHomologicalComplex (.up ℤ)).obj P)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace X :=
    (quasiSeparated_iff_quasiSeparatedSpace (X ↘ Spec (.of k))).mp inferInstance
  have : QuasiSeparatedSpace Y :=
    (quasiSeparated_iff_quasiSeparatedSpace (Y ↘ Spec (.of k))).mp inferInstance
  let F := CondensedRing.upperStar (DerivedNakayama.integerRing l E) g
  have hbc : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X
      (F.mapDerivedCategory.obj K) := by
    have := (constantModelConstructibleFiniteTor_wellDefined
      (DerivedNakayama.integerRing l E) X).1
    refine ⟨F.bounded_mapDerivedCategory_obj _hK.1, fun n ↦ ?_⟩
    exact ObjectProperty.prop_of_iso
      (IsConstantModelConstructible (DerivedNakayama.integerRing l E) X)
      ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
      (pullback_constructible (DerivedNakayama.integerRing l E) g _ (_hK.2 n))
  refine ⟨hbc, ?_⟩
  intro P hP eP
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have hc := ((internal_integral_residue_criterion l E X).1 _).mp hbc |>.1
  have hQ := CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj
    (DerivedNakayama.integerRing l E) g hP
  let eQ := (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso eP
  have hu := (AdicCompletion.isDerivedComplete_iff l E X _ _ hQ eQ).mp hc
  constructor
  · obtain ⟨e, he⟩ := ordinary_roos_unit l E g P
    change IsIso (eQ.inv ≫ DerivedCategory.Q.map
      (AdicCompletion.augmentation l E X
        ((F.mapHomologicalComplex (.up ℤ)).obj P))) at hu
    have := hu
    have : IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X
        ((F.mapHomologicalComplex (.up ℤ)).obj P))) :=
      IsIso.of_isIso_comp_left eQ.inv _
    have : IsIso (DerivedCategory.Q.map (comparison l E g P) ≫
        DerivedCategory.Q.map e.hom) := by
      rw [← Functor.map_comp, he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map e.hom)
  · obtain ⟨e, he⟩ := constant_roos_unit l E g P
    refine ⟨DerivedCategory.Q.mapIso e, ?_⟩
    simpa only [Functor.map_comp, Functor.mapIso_hom] using congrArg DerivedCategory.Q.map he

end AlgebraicGeometry.ProEtale.IntegralTensorPullback
