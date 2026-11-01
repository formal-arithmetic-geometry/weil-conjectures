/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.ProperBaseChange.FlatAlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.ProperBaseChange.RingedToposPullbackFilteredColimits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
import all WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.ProperBaseChange.FlatAlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.ProperBaseChange.RingedToposPullbackFilteredColimits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import WeilConjectures.RingTheory.LimitFlatModules
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Constant coefficient completion: Core

Scalar changes, finite and derived comparisons, quotient-tower completion and Koszul
presentations.

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}


section CoefficientIdeal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end CoefficientIdeal

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [instance] change_additive

set_option genSizeOf false in
set_option genInjectivity false in
attribute [local irreducible] derivedExtension

section ScalarTransitions
variable {R S T : Sheaf J CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def resCompIso (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T) (h : φ ≫ τ = ψ) :
    res τ ⋙ res φ ≅ res ψ := by
  subst ψ
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine { hom := { val := { app := fun U ↦ ?_, naturality := ?_ } }
             inv := { val := { app := fun U ↦ ?_, naturality := ?_ } }
             hom_inv_id := ?_
             inv_hom_id := ?_ }
    · exact ModuleCat.ofHom
        (X := ((res φ).obj ((res τ).obj M)).val.obj U)
        (Y := ((res (φ ≫ τ)).obj M).val.obj U)
        { toFun := fun m ↦ m
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
    · intros; ext; rfl
    · exact ModuleCat.ofHom
        (X := ((res (φ ≫ τ)).obj M).val.obj U)
        (Y := ((res φ).obj ((res τ).obj M)).val.obj U)
        { toFun := fun m ↦ m
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
    · intros; ext; rfl
    · ext; rfl
    · ext; rfl
  · intros; ext; rfl

end ScalarTransitions

section FiniteComparisons

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R B S : Sheaf J CommRingCat.{u}}

end FiniteComparisons

-- Subsequent proofs use the section formulas instead of reducing these constructions.
attribute [irreducible] resCompIso transitionLift scalarTransition
  quotientRestrictionHomEquiv quotientTensorAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory CochainComplex.IsAcyclicTensorKFlat
  CochainComplex.IsKFlatIndependentCoefficients

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend a natural comparison from a cochain resolving class. -/
private theorem resolving_nat
    {M H : Type*} [Category M] [Abelian M] [HasDerivedCategory M] [Category H]
    (F G : DerivedCategory M ⥤ H) (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (s : K ⟶ X), P K ∧ QuasiIso s)
    (α : ∀ X : CochainComplex M ℤ, P X →
      (F.obj (DerivedCategory.Q.obj X) ⟶ G.obj (DerivedCategory.Q.obj X)))
    (hα : ∀ (X Y : CochainComplex M ℤ) (hX : P X) (hY : P Y) (f : X ⟶ Y),
      F.map (DerivedCategory.Q.map f) ≫ α Y hY =
        α X hX ≫ G.map (DerivedCategory.Q.map f)) :
    ∃ e : F ⟶ G, ∀ (X : CochainComplex M ℤ) (hX : P X),
      e.app (DerivedCategory.Q.obj X) = α X hX := by
  let q := HomotopyCategory.quotient M (.up ℤ)
  let Q := DerivedCategory.Qh (C := M)
  let W := HomotopyCategory.quasiIso M (.up ℤ)
  let S (X : HomotopyCategory M (.up ℤ)) := P X.as
  have : W.HasRightCalculusOfFractions :=
    (HomotopyCategory.quasiIso_saturated_triangulated M).2.1
  have hres' (X : HomotopyCategory M (.up ℤ)) :
      ∃ (K : HomotopyCategory M (.up ℤ)) (s : K ⟶ X), S K ∧ W s := by
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, s, hK, hs⟩ := hres X
    exact ⟨q.obj K, q.map s, hK,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  let i := DerivedCategory.quotientCompQhIso M
  let α' (X : HomotopyCategory M (.up ℤ)) (hX : S X) :
      (Q ⋙ F).obj X ⟶ (Q ⋙ G).obj X :=
    F.map (i.hom.app X.as) ≫ α X.as hX ≫ G.map (i.inv.app X.as)
  have hα' (X Y : HomotopyCategory M (.up ℤ)) (hX : S X) (hY : S Y)
      (f : X ⟶ Y) :
      (Q ⋙ F).map f ≫ α' Y hY = α' X hX ≫ (Q ⋙ G).map f := by
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨f, rfl⟩ := q.map_surjective f
    change P X at hX
    change P Y at hY
    have hi : Q.map (q.map f) ≫ i.hom.app Y =
        i.hom.app X ≫ DerivedCategory.Q.map f := i.hom.naturality f
    have hi' : DerivedCategory.Q.map f ≫ i.inv.app Y =
        i.inv.app X ≫ Q.map (q.map f) := i.inv.naturality f
    change F.map (Q.map (q.map f)) ≫
        (F.map (i.hom.app Y) ≫ α Y hY ≫ G.map (i.inv.app Y)) =
      (F.map (i.hom.app X) ≫ α X hX ≫ G.map (i.inv.app X)) ≫ G.map (Q.map (q.map f))
    rw [← F.map_comp_assoc, hi, F.map_comp_assoc,
      reassoc_of% hα X Y hX hY f]
    simp only [Category.assoc]
    rw [← G.map_comp, hi', G.map_comp]
  obtain ⟨β, hβ⟩ := exists_natTrans_from_resolvingClass W S hres' (Q ⋙ F) (Q ⋙ G)
    (fun X Y s hs ↦ by
      have : IsIso (Q.map s) := Localization.inverts Q W s hs
      exact inferInstanceAs (IsIso (F.map (Q.map s))))
    (fun X hX ↦ α' X hX) hα'
  let K := (Functor.whiskeringLeft _ _ H).obj Q
  have : K.Full := Localization.full_whiskeringLeft Q W H
  have : K.Faithful := Localization.faithful_whiskeringLeft Q W H
  let e : F ⟶ G := K.preimage β
  have he (X : HomotopyCategory M (.up ℤ)) : e.app (Q.obj X) = β.app X :=
    congrArg (fun t ↦ t.app X) (K.map_preimage β)
  refine ⟨e, ?_⟩
  intro X hX
  have hn := e.naturality (i.hom.app X)
  change F.map (i.hom.app X) ≫ e.app (DerivedCategory.Q.obj X) =
    e.app (Q.obj (q.obj X)) ≫ G.map (i.hom.app X) at hn
  rw [he, hβ (q.obj X) hX] at hn
  change F.map (i.hom.app X) ≫ e.app (DerivedCategory.Q.obj X) =
    (F.map (i.hom.app X) ≫ α X hX ≫ G.map (i.inv.app X)) ≫ G.map (i.hom.app X) at hn
  apply (cancel_epi (F.map (i.hom.app X))).1
  rw [hn]
  simp only [Category.assoc, ← G.map_comp, i.inv_hom_id_app, G.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equality of derived natural maps can be checked on a cochain resolving class. -/
private theorem resolving_nat_ext
    {M H : Type*} [Category M] [Abelian M] [HasDerivedCategory M] [Category H]
    {F G : DerivedCategory M ⥤ H} (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (s : K ⟶ X), P K ∧ QuasiIso s)
    (α β : F ⟶ G)
    (h : ∀ X, P X → α.app (DerivedCategory.Q.obj X) =
      β.app (DerivedCategory.Q.obj X)) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso M (.up ℤ))
  intro X
  obtain ⟨K, f, hK, hf⟩ := hres X
  have : QuasiIso f := hf
  have : IsIso (F.map (DerivedCategory.Q.map f)) := inferInstance
  apply (cancel_epi (F.map (DerivedCategory.Q.map f))).1
  rw [α.naturality, β.naturality, h K hK]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend an invertible comparison from a cochain resolving class. -/
private theorem resolving_iso
    {M H : Type*} [Category M] [Abelian M] [HasDerivedCategory M] [Category H]
    (F G : DerivedCategory M ⥤ H) (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (s : K ⟶ X), P K ∧ QuasiIso s)
    (α : ∀ X : CochainComplex M ℤ, P X →
      (F.obj (DerivedCategory.Q.obj X) ≅ G.obj (DerivedCategory.Q.obj X)))
    (hα : ∀ (X Y : CochainComplex M ℤ) (hX : P X) (hY : P Y) (f : X ⟶ Y),
      F.map (DerivedCategory.Q.map f) ≫ (α Y hY).hom =
        (α X hX).hom ≫ G.map (DerivedCategory.Q.map f)) :
    ∃ e : F ≅ G, ∀ (X : CochainComplex M ℤ) (hX : P X),
      e.hom.app (DerivedCategory.Q.obj X) = (α X hX).hom := by
  obtain ⟨β, hβ⟩ := resolving_nat F G P hres (fun X hX ↦ (α X hX).hom) hα
  have hβiso (X : CochainComplex M ℤ) : IsIso (β.app (DerivedCategory.Q.obj X)) := by
    obtain ⟨K, f, hK, hf⟩ := hres X
    have : QuasiIso f := hf
    have : IsIso (F.map (DerivedCategory.Q.map f)) := inferInstance
    have : IsIso (G.map (DerivedCategory.Q.map f)) := inferInstance
    have : IsIso (β.app (DerivedCategory.Q.obj K)) := by rw [hβ K hK]; infer_instance
    have hn := β.naturality (DerivedCategory.Q.map f)
    have : IsIso (F.map (DerivedCategory.Q.map f) ≫ β.app (DerivedCategory.Q.obj X)) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left (F.map (DerivedCategory.Q.map f)) _
  let L := (Functor.whiskeringLeft _ _ H).obj (DerivedCategory.Q (C := M))
  let W := HomologicalComplex.quasiIso M (.up ℤ)
  have : L.Full := Localization.full_whiskeringLeft DerivedCategory.Q W H
  have : L.Faithful := Localization.faithful_whiskeringLeft DerivedCategory.Q W H
  have : ∀ X, IsIso ((L.map β).app X) := fun X ↦ hβiso X
  have : IsIso (L.map β) := NatIso.isIso_of_isIso_app _
  have : IsIso β := isIso_of_reflects_iso β L
  exact ⟨asIso β, hβ⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolving_comparison_iso
    {M H : Type*} [Category M] [Abelian M] [HasDerivedCategory M] [Category H]
    (F G : DerivedCategory M ⥤ H) (T : CochainComplex M ℤ ⥤ H)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (s : K ⟶ X), P K ∧ QuasiIso s)
    (α : DerivedCategory.Q ⋙ F ⟶ T) (β : DerivedCategory.Q ⋙ G ⟶ T)
    (hα : ∀ X, P X → IsIso (α.app X)) (hβ : ∀ X, P X → IsIso (β.app X)) :
    ∃ e : F ≅ G, ∀ X, P X → e.hom.app (DerivedCategory.Q.obj X) ≫ β.app X =
      α.app X := by
  let a (X : CochainComplex M ℤ) (hX : P X) :=
    let := hα X hX
    let := hβ X hX
    asIso (α.app X) ≪≫ (asIso (β.app X)).symm
  obtain ⟨e, he⟩ := resolving_iso F G P hres a (by
    intro X Y hX hY f
    let := hα X hX
    let := hα Y hY
    let := hβ X hX
    let := hβ Y hY
    apply (cancel_mono (β.app Y)).1
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have ha : F.map (DerivedCategory.Q.map f) ≫ α.app Y = α.app X ≫ T.map f :=
      α.naturality f
    have hb : G.map (DerivedCategory.Q.map f) ≫ β.app Y = β.app X ≫ T.map f :=
      β.naturality f
    rw [ha, hb]
    simp only [IsIso.inv_hom_id_assoc])
  refine ⟨e, ?_⟩
  intro X hX
  let := hα X hX
  let := hβ X hX
  rw [he X hX]
  simp only [a, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Descend a square whose two iterated computations are invertible. -/
private theorem resolving_square_iso
    {M H₁ H₂ H₃ D₁ D₂ D₃ : Type*}
    [Category M] [Abelian M] [HasDerivedCategory M]
    [Category H₁] [Category H₂] [Category H₃]
    [Category D₁] [Category D₂] [Category D₃]
    (q₁ : H₁ ⥤ D₁) (q₂ : H₂ ⥤ D₂) (q₃ : H₃ ⥤ D₃)
    (r : CochainComplex M ℤ ⥤ H₁) (b : CochainComplex M ℤ ⥤ H₂)
    (p : H₁ ⥤ H₃) (s : H₂ ⥤ H₃)
    (dr : DerivedCategory M ⥤ D₁) (db : DerivedCategory M ⥤ D₂)
    (dp : D₁ ⥤ D₃) (ds : D₂ ⥤ D₃)
    (α : DerivedCategory.Q ⋙ dr ⟶ r ⋙ q₁)
    (β : q₁ ⋙ dp ⟶ p ⋙ q₃) (γ : r ⋙ p ≅ b ⋙ s)
    (δ : DerivedCategory.Q ⋙ db ⟶ b ⋙ q₂) (ε : q₂ ⋙ ds ⟶ s ⋙ q₃)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ X), P K ∧ QuasiIso f)
    (hα : ∀ X, P X → IsIso (α.app X))
    (hβ : ∀ X, P X → IsIso (β.app (r.obj X)))
    (hδ : ∀ X, P X → IsIso (δ.app X))
    (hε : ∀ X, P X → IsIso (ε.app (b.obj X))) :
    ∃! e : dr ⋙ dp ≅ db ⋙ ds, ∀ X, P X →
      dp.map (α.app X) ≫ β.app (r.obj X) ≫ q₃.map (γ.hom.app X) =
        e.hom.app (DerivedCategory.Q.obj X) ≫ ds.map (δ.app X) ≫ ε.app (b.obj X) := by
  let T := b ⋙ s ⋙ q₃
  let a : DerivedCategory.Q ⋙ (dr ⋙ dp) ⟶ T :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α _ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft r β ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight γ.hom _ ≫
      (Functor.associator _ _ _).hom
  let z : DerivedCategory.Q ⋙ (db ⋙ ds) ⟶ T :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight δ _ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft b ε
  have ha X (hX : P X) : IsIso (a.app X) := by
    have := hα X hX
    have := hβ X hX
    dsimp only [a, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  have hz X (hX : P X) : IsIso (z.app X) := by
    have := hδ X hX
    have := hε X hX
    dsimp only [z, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  obtain ⟨e, he⟩ := resolving_comparison_iso (dr ⋙ dp) (db ⋙ ds) T P hres a z ha hz
  have hf (t : dr ⋙ dp ≅ db ⋙ ds) :
      (∀ X, P X → t.hom.app (DerivedCategory.Q.obj X) ≫ z.app X = a.app X) ↔
      (∀ X, P X → dp.map (α.app X) ≫ β.app (r.obj X) ≫ q₃.map (γ.hom.app X) =
        t.hom.app (DerivedCategory.Q.obj X) ≫ ds.map (δ.app X) ≫ ε.app (b.obj X)) := by
    dsimp only [a, z, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.id_comp, Category.comp_id]
    exact ⟨fun h X hX ↦ (h X hX).symm, fun h X hX ↦ (h X hX).symm⟩
  refine ⟨e, (hf e).1 he, ?_⟩
  intro t ht
  apply Iso.ext
  apply resolving_nat_ext P hres
  intro X hX
  have := hz X hX
  apply (cancel_mono (z.app X)).1
  rw [(hf t).2 ht X hX, he X hX]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section
attribute [local irreducible] dres change

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end

variable (J A I)

attribute [instance] reductionTower_additive

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
variable {J A I}


set_option genSizeOf false in
set_option genInjectivity false in
attribute [local irreducible] strictLimit

variable (J A I)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] ordinaryUnit

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option genSizeOf false in
set_option genInjectivity false in
section

attribute [local irreducible] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.types true in
end

attribute [local irreducible] quotientPresentation

end CategoryTheory.ConstantCompletion
