/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import all WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Tensor constructibility for admissible condensed coefficients

This isolates the constructibility calculation, without the generic Tor-amplitude addition,
from det-thm-sf-ctf-stability-direct-images.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

section TensorHelpers

-- Fix the coefficient size while elaborating the private comparison arguments.
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify

private local instance (priority := 2000) tensorSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _

attribute [local irreducible] Functor.mapDerivedCategory
  DerivedCategory.tensorLeftCompMapDerivedCategoryIso
  Functor.mapDerivedCategoryHomologyFunctorIso
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed

private theorem coefficient_tensor_transport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u})
    (h : ∀ K M, (constantModelBoundedConstructible Λ' X K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      (constantModelBoundedConstructible Λ' X M ∧ DerivedCategory.finiteTorAmplitude _ M) →
      constantModelBoundedConstructible Λ' X (((derivedTensor Λ' X).obj K).obj M)) :
    ∀ K M, (constantModelBoundedConstructible Λ X K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      (constantModelBoundedConstructible Λ X M ∧ DerivedCategory.finiteTorAmplitude _ M) →
      constantModelBoundedConstructible Λ X (((derivedTensor Λ X).obj K).obj M) := by
  let φ := e.inv.hom
  have : IsIso φ := inferInstanceAs (IsIso e.inv.hom)
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap φ X)
  have : F.IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso (coefficientMap φ X)).functor.IsEquivalence
  have : (constantModelBoundedConstructible Λ' X).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ' X).2.1
  intro K M hK hM
  apply (constantModel_derived_comap_iff φ X _).mp
  apply (constantModelBoundedConstructible Λ' X).prop_of_iso
    ((DerivedCategory.tensorLeftCompMapDerivedCategoryIso F K).app M).symm
  exact h _ _ (constantModelCtf_coefficientIso e X ⟨K, hK⟩)
    (constantModelCtf_coefficientIso e X ⟨M, hM⟩)

private theorem etale_tensor_constructible
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K M : Etale.DerivedCategoryModule A X)
    (hK : Etale.DerivedCategory.isBoundedConstructible A X K)
    (hM : Etale.DerivedCategory.isBoundedConstructible A X M)
    (hMt : DerivedCategory.finiteTorAmplitude _ M) :
    Etale.DerivedCategory.isBoundedConstructible A X
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj M) := by
  have old (L : Etale.DerivedCategoryModule A X)
      (hL : Etale.DerivedCategory.isBoundedConstructible A X L) :
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X L := by
    obtain ⟨hc, a, b, _, hv⟩ := hL
    refine ⟨⟨⟨a, (DerivedCategory.isGE_iff _ a).mpr (fun i hi ↦ hv i (.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff _ b).mpr (fun i hi ↦ hv i (.inr hi))⟩⟩, ?_⟩
    intro i
    exact (Etale.constructibleSheaf_iff _ _ _).mpr
      ((Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i))
  have ht := Etale.boundedConstructible_tensor A X (old K hK) (old M hM) hMt
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ht.1
  refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    ((Etale.constructibleSheaf_iff _ _ _).mp (ht.2 i)), min a b, b,
      min_le_right _ _, ?_⟩
  intro i hi
  rcases hi with hi | hi
  · exact (DerivedCategory.isGE_iff _ a).mp ha i (lt_of_lt_of_le hi (min_le_left _ _))
  · exact (DerivedCategory.isLE_iff _ b).mp hb i hi

private theorem finite_tensor_constructible
    (B : Type) [CommRing B] [TopologicalSpace B] [DiscreteTopology B]
    [IsTopologicalRing B] [Finite B] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj B) X)))
    (hK : constantModelBoundedConstructible (Profinite.continuousMapRingObj B) X K ∧
      DerivedCategory.finiteTorAmplitude _ K)
    (hM : constantModelBoundedConstructible (Profinite.continuousMapRingObj B) X M ∧
      DerivedCategory.finiteTorAmplitude _ M) :
    constantModelBoundedConstructible (Profinite.continuousMapRingObj B) X
      (((derivedTensor (Profinite.continuousMapRingObj B) X).obj K).obj M) := by
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  let := heR
  let G := finiteComparisonRealization B X eR
  have : G.IsEquivalence := (finiteComparisonRealization_exact B X eR).1
  obtain ⟨hG⟩ := finiteRealizationMonoidal_exists B X eR
  let := hG
  let F := G.mapDerivedCategory
  let K₀ := F.objPreimage K
  let M₀ := F.objPreimage M
  let eK := F.objObjPreimageIso K
  let eM := F.objObjPreimageIso M
  let P := constantModelBoundedConstructible (Profinite.continuousMapRingObj B) X
  let : P.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined _ X).2.1
  let : (DerivedCategory.finiteTorAmplitude _).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined
      (Profinite.continuousMapRingObj B) X).2.2.2.1
  have hK₀ : finiteComparisonProEtaleGenerators B eR X K₀ :=
    ⟨P.prop_of_iso eK.symm hK.1, ObjectProperty.prop_of_iso _ eK.symm hK.2⟩
  have hM₀ : finiteComparisonProEtaleGenerators B eR X M₀ :=
    ⟨P.prop_of_iso eM.symm hM.1, ObjectProperty.prop_of_iso _ eM.symm hM.2⟩
  obtain ⟨K', hK', ⟨dK⟩⟩ :=
    (finiteComparisonGenerators_identification B eR X).2 K₀ hK₀
  obtain ⟨M', hM', ⟨dM⟩⟩ :=
    (finiteComparisonGenerators_identification B eR X).2 M₀ hM₀
  let N := ((Etale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).obj K').obj M'
  have hN : finiteComparisonEtaleGenerators B X N := by
    refine ⟨etale_tensor_constructible _ X K' M' hK'.1 hM'.1 hM'.2, ?_⟩
    obtain ⟨a, b, ha⟩ := hK'.2
    obtain ⟨c, d, hb⟩ := hM'.2
    exact ⟨a + c, b + d, Etale.torAmplitudeIn_tensor _ X a b c d ha hb⟩
  have hFN := (finiteComparisonGenerators_identification B eR X).1 N hN
  let t := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) K').app M' ≪≫ tensorIso dK dM
  apply P.prop_of_iso (F.mapIso t ≪≫
    (DerivedCategory.tensorLeftCompMapDerivedCategoryIso G K₀).app M₀ ≪≫
    tensorIso eK eM)
  exact hFN.1

end TensorHelpers

/-- Derived tensor preserves bounded constructibility for two admissible-coefficient
constructible complexes of finite Tor amplitude.

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-ctf-stability,
det-thm-sf-ctf-stability-direct-images, proof steps 2--3
(blueprint: lem-sfb-admissible-tensor-constructibility).

Proof:
1. Finite type over the field makes X Noetherian and qcqs. Restriction along a coefficient
ring isomorphism is an exact monoidal equivalence. It preserves finite constant local
models, boundedness and Tor intervals, and its derived tensor comparison transports the
conclusion back to the original coefficient.
2. For a finite discrete ring B, use its specified constant-ring realization to lift both
inputs to ordinary pro-etale module complexes. The finite comparison generator theorem
supplies bounded constructible finite-Tor etale origins. Convert the constructibility
predicates and apply the existing etale boundedConstructible_tensor theorem. Addition of
Tor intervals makes the result another etale generator. The comparison inverse image and
the coefficient realization are monoidal on derived categories; their canonical comparisons
and the origin isomorphisms identify this generator's realization with the specified tensor.
3. For O_E use integralModelsOperations(2), and for E and the finite-subextension-valued
algebraic closure use tensorClosureRational(1). The explicit base-coefficient isomorphisms
identify Z_l and Q_l with the bottom finite intermediate field's integer ring and field.
Split the six alternatives of the current admissibility predicate and transport as in step 1.
The zero ring, zero complexes and empty scheme are included by the same constructions.
-/
theorem constantModelBoundedConstructible_tensor_of_admissible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.finiteTorAmplitude _ K)
    (hM : constantModelBoundedConstructible Λ X M ∧
      DerivedCategory.finiteTorAmplitude _ M) :
    constantModelBoundedConstructible Λ X (((-⊗ᴸ-(X)⟦Λ⟧).obj K).obj M) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  let E₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  obtain ⟨_, _, _, _, _, _, _, _, qIso, zIso, _⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} ℓ
  have integral (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
    (integralModelsOperations.{u} ℓ E).2.1 X
  have rational (Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Γ] [IsCommMonObj Γ]
      (hΓ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Γ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
        Nonempty (Mon.mk Γ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :=
    (tensorClosureRational ℓ (k := k) (ringChar k)
      (Nat.Prime.pos (Fact.out : (ringChar k).Prime))
      (Fact.out : ringChar k ≠ ℓ) (X ↘ Spec (.of k)) Γ hΓ).1
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨A, _, _, _, _, hfin, _, ⟨e⟩⟩ := h
    have : Finite A := hfin
    exact coefficient_tensor_transport e X (finite_tensor_constructible A X) K M hK hM
  · obtain ⟨e⟩ := h
    exact coefficient_tensor_transport (e ≪≫ zIso) X
      (fun K M hK hM ↦ integral E₀ K M hK.1 hM.1) K M hK hM
  · obtain ⟨e⟩ := h
    exact rational Λ (.inl ⟨E₀, ⟨e ≪≫ qIso⟩⟩) K M hK.1 hM.1
  · exact rational Λ (.inl h) K M hK.1 hM.1
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact coefficient_tensor_transport e X
      (fun K M hK hM ↦ integral E K M hK.1 hM.1) K M hK hM
  · exact rational Λ (.inr h) K M hK.1 hM.1

end AlgebraicGeometry.ProEtale.CondensedRing
