/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.Paper.IntegralHeartLocalModelData
import Sheaf.Paper.IntegralConstantModelHeart
import Sheaf.Paper.IntegralHeartProjectiveLocalModels
import Sheaf.Paper.IntegralHeartConstructibleModuleComplete
import Sheaf.Paper.IntegralHeartRealizationExact
import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Integral constructible local models

Source: the current blueprint, integral-heart-local-model, clauses (1)--(3).
(blueprint: det-lem-int-integral-heart-local-model)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

-- Keep the coefficient structure explicit while transporting the categorical package.
private def localModel_categoricalHeartProperty
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (m : MonObj Λ) (hc : @IsCommMonObj _ _ _ _ Λ m) (X : Scheme.{u}) : Prop :=
  letI := m
  letI := hc
  ObjectProperty.IsClosedUnderIsomorphisms
    (constantModelBoundedConstructible Λ X) ∧
  ObjectProperty.IsTriangulated
    (constantModelBoundedConstructible Λ X) ∧
  (∀ K, constantModelBoundedConstructible Λ X K →
    DerivedCategory.TStructure.t.bounded K ∧ ∀ n : ℤ,
      constantModelBoundedConstructible Λ X
        ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      constantModelBoundedConstructible Λ X
        ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
  (ObjectProperty.ι (IsConstantModelConstructible Λ X) ⋙
    DerivedCategory.singleFunctor _ 0).Full ∧
  (ObjectProperty.ι (IsConstantModelConstructible Λ X) ⋙
    DerivedCategory.singleFunctor _ 0).Faithful ∧
  (∀ K, (ObjectProperty.ι
      (IsConstantModelConstructible Λ X) ⋙
      DerivedCategory.singleFunctor _ 0).essImage K ↔
    constantModelBoundedConstructible Λ X K ∧
    DerivedCategory.TStructure.t.le 0 K ∧ DerivedCategory.TStructure.t.ge 0 K) ∧
  Nonempty (Abelian (ConstantModelConstructible Λ X)) ∧
  ObjectProperty.IsClosedUnderKernels
    (IsConstantModelConstructible Λ X) ∧
  ObjectProperty.IsClosedUnderCokernels
    (IsConstantModelConstructible Λ X) ∧
  ObjectProperty.IsClosedUnderExtensions
    (IsConstantModelConstructible Λ X) ∧
  EssentiallySmall.{u + 1}
    (ConstantModelConstructible Λ X)

attribute [-instance] SmallAdicCompletion.Coefficients.integerRingMonObj
  SmallAdicCompletion.Coefficients.integerRingComm in
private noncomputable def localModel_canonicalCoefficient
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    {m : MonObj (integralHeartCoefficientRingObj.{u} ℓ E) //
      @IsCommMonObj _ _ _ _ _ m} := ⟨inferInstance, inferInstance⟩

attribute [-instance] SmallAdicCompletion.Coefficients.integerRingMonObj
  SmallAdicCompletion.Coefficients.integerRingComm in
private theorem localModel_categoricalHeart_canonical
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    localModel_categoricalHeartProperty (integralHeartCoefficientRingObj ℓ E)
      (localModel_canonicalCoefficient.{u} ℓ E).val
      (localModel_canonicalCoefficient.{u} ℓ E).property X := by
  have h := @integralConstantModelHeart.{u, v} k ‹Field k› p ‹CharP k p› hp
    ℓ ‹Fact ℓ.Prime› hℓ E ‹Field E› ‹Algebra (Padic ℓ) E›
    ‹FiniteDimensional (Padic ℓ) E› X ‹X.Over (Spec (.of k))›
    ‹IsSeparated (X ↘ Spec (.of k))› ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    ‹QuasiCompact (X ↘ Spec (.of k))›
  unfold localModel_categoricalHeartProperty
  exact h

attribute [local irreducible] localModel_categoricalHeartProperty

private theorem localModel_coefficient_transport
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (P : {m : MonObj (integralHeartCoefficientRingObj.{u} ℓ E) //
      @IsCommMonObj _ _ _ _ _ m} → Prop)
    (h : P (localModel_canonicalCoefficient.{u} ℓ E)) :
    P ⟨SmallAdicCompletion.Coefficients.integerRingMonObj.{u} ℓ E,
      SmallAdicCompletion.Coefficients.integerRingComm.{u} ℓ E⟩ := by
  have heq : (⟨SmallAdicCompletion.Coefficients.integerRingMonObj.{u} ℓ E,
      SmallAdicCompletion.Coefficients.integerRingComm.{u} ℓ E⟩ :
      {m : MonObj (integralHeartCoefficientRingObj.{u} ℓ E) //
        @IsCommMonObj _ _ _ _ _ m}) = localModel_canonicalCoefficient.{u} ℓ E := by
    exact Subtype.ext (show _ = _ from rfl)
  exact (congrArg P heq).mpr h

private theorem localModel_categoricalHeart_cached
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    localModel_categoricalHeartProperty (integralHeartCoefficientRingObj ℓ E)
      (SmallAdicCompletion.Coefficients.integerRingMonObj ℓ E)
      (SmallAdicCompletion.Coefficients.integerRingComm ℓ E) X := by
  have h := @localModel_categoricalHeart_canonical.{u, v} k ‹Field k› p ‹CharP k p› hp
    ℓ ‹Fact ℓ.Prime› hℓ E ‹Field E› ‹Algebra (Padic ℓ) E›
    ‹FiniteDimensional (Padic ℓ) E› X ‹X.Over (Spec (.of k))›
    ‹IsSeparated (X ↘ Spec (.of k))› ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    ‹QuasiCompact (X ↘ Spec (.of k))›
  exact localModel_coefficient_transport ℓ E (fun x ↦ localModel_categoricalHeartProperty
    (integralHeartCoefficientRingObj.{u} ℓ E) x.val x.property X) h

private theorem localModel_single_constructible_of_essImage
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (h : ∀ K, (ObjectProperty.ι (IsConstantModelConstructible Λ X) ⋙
      DerivedCategory.singleFunctor _ 0).essImage K ↔
      constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.TStructure.t.le 0 K ∧ DerivedCategory.TStructure.t.ge 0 K)
    (C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) (hC : IsConstantModelConstructible Λ X C) :
    constantModelBoundedConstructible Λ X ((DerivedCategory.singleFunctor _ 0).obj C) := by
  exact ((h _).1 ⟨⟨C, hC⟩, ⟨Iso.refl _⟩⟩).1

private def localModel_singleConstructibleProperty
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (m : MonObj Λ) (hc : @IsCommMonObj _ _ _ _ Λ m) (X : Scheme.{u}) : Prop :=
  letI := m
  letI := hc
  ∀ C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X),
    IsConstantModelConstructible Λ X C →
      constantModelBoundedConstructible Λ X ((DerivedCategory.singleFunctor _ 0).obj C)

attribute [local irreducible] localModel_singleConstructibleProperty

private theorem localModel_singleConstructible_cached
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    localModel_singleConstructibleProperty (SmallAdicCompletion.Coefficients.integerRing ℓ E)
      (SmallAdicCompletion.Coefficients.integerRingMonObj ℓ E)
      (SmallAdicCompletion.Coefficients.integerRingComm ℓ E) X := by
  have h := @localModel_categoricalHeart_cached.{u, v} k ‹Field k› p ‹CharP k p› hp
    ℓ ‹Fact ℓ.Prime› hℓ E ‹Field E› ‹Algebra (Padic ℓ) E›
    ‹FiniteDimensional (Padic ℓ) E› X ‹X.Over (Spec (.of k))›
    ‹IsSeparated (X ↘ Spec (.of k))› ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    ‹QuasiCompact (X ↘ Spec (.of k))›
  unfold localModel_categoricalHeartProperty at h
  unfold localModel_singleConstructibleProperty
  exact localModel_single_constructible_of_essImage _ X h.2.2.2.2.2.1



/-- Integral constructible complexes have finite free local models, their cohomology is
complete and constructible, and both good truncations remain constructible.
Source: blueprint main-20261015, integral-heart-local-model, clauses (1)--(3), and
Stacks Tags 099I, 09C7, 09C4, 0990, 099Q, 099Y
(blueprint: det-lem-int-integral-heart-local-model).

Proof: (1) The coefficient DVR is a local PID and hence Noetherian. Completeness
follows by lifting a compatible sequence of residues and using the absolute-value
bound by successive powers of the uniformizer. The integral cohomological adic
criterion identifies the hypothesis with local derived completeness and finite-Tor
constructible residue reduction. The stratified-perfect theorem supplies finite
projective scalar complexes on a finite constructible stratification and its covers.
Each finite projective module embeds in a finite free module, is torsion-free, and
is free over the DVR; bases give the scalar differential matrices.
(2) Each H^q(K)[0] is bounded constructible by the cohomological definition, so the
integral-models criterion gives derived completeness in the canonical reduction-limit
sense. On exactly the original charts, exact cartesian inverse image and flat completed
scalar extension commute with kernels, images and cohomology. Thus the model is the
realization of H^q(P), which is finite since the DVR is Noetherian.
(3) Good truncations retain the original cohomology in the retained degrees and zero
elsewhere. Both lists are bounded and constructible, which is exactly the same
constant-model bounded-constructible predicate as in the hypothesis. -/
theorem integralHeartLocalModel
    (k₀ : Type u) [Field k₀] (p : ℕ) [CharP k₀ p] (_hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : p ≠ ℓ)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k₀))]
    [IsSeparated (X ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
    [QuasiCompact (X ↘ Spec (.of k₀))]
    (K : integralHeartDerivedCategory.{u} ℓ E X)
    (hK : constantModelBoundedConstructible
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X K) :
    integralHeartFiniteFreeLocalModel.{u} ℓ E X K ∧
      (∀ q : ℤ,
        SmallAdicCompletion.IsDerivedComplete ℓ E X (integralHeartCohomology.{u} ℓ E X K q) ∧
        constantModelBoundedConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
          (integralHeartCohomology.{u} ℓ E X K q)) ∧
      (∀ q : ℤ,
        constantModelBoundedConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
          ((DerivedCategory.TStructure.t.truncLE q).obj K) ∧
        constantModelBoundedConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
          ((DerivedCategory.TStructure.t.truncGE q).obj K)) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k₀))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k₀))
  have : IsNoetherian X := ⟨⟩
  have hcat := @localModel_categoricalHeart_cached.{u, v} k₀ ‹Field k₀› p ‹CharP k₀ p› _hp
    ℓ ‹Fact ℓ.Prime› _hℓ.symm E ‹Field E› ‹Algebra (Padic ℓ) E›
    ‹FiniteDimensional (Padic ℓ) E› X ‹X.Over (Spec (.of k₀))›
    ‹IsSeparated (X ↘ Spec (.of k₀))› ‹LocallyOfFiniteType (X ↘ Spec (.of k₀))›
    ‹QuasiCompact (X ↘ Spec (.of k₀))›
  unfold localModel_categoricalHeartProperty at hcat
  have hs := @localModel_singleConstructible_cached.{u, v} k₀ ‹Field k₀› p ‹CharP k₀ p› _hp
    ℓ ‹Fact ℓ.Prime› _hℓ.symm E ‹Field E› ‹Algebra (Padic ℓ) E›
    ‹FiniteDimensional (Padic ℓ) E› X ‹X.Over (Spec (.of k₀))›
    ‹IsSeparated (X ↘ Spec (.of k₀))› ‹LocallyOfFiniteType (X ↘ Spec (.of k₀))›
    ‹QuasiCompact (X ↘ Spec (.of k₀))›
  unfold localModel_singleConstructibleProperty at hs
  refine ⟨?_, ?_, (hcat.2.2.1 K hK).2⟩
  · obtain ⟨s, hs, hmodels⟩ := integralHeart_projective_local_models ℓ E X K hK
    refine ⟨s, hs, fun a ↦ ?_⟩
    obtain ⟨𝒰, h𝒰⟩ := hmodels a
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, b, c, hb, hc, hP, ⟨e⟩⟩ := h𝒰 i
    let A := integralHeartScalars.{u} ℓ E
    let O := SmallAdicCompletion.Coefficients.integers ℓ E
    have hDvr : IsDiscreteValuationRing O :=
      (Padic.extension_integers_dvr ℓ (SmallAdicCompletion.Coefficients.field ℓ E)
        (Padic.coefficientExtensionAbsoluteValue ℓ _)
        (spectralNorm_extends (K := Padic ℓ)
          (L := SmallAdicCompletion.Coefficients.field ℓ E))).choose_spec.choose_spec
          |>.2.2.2.2.2.2.2.1
    have : IsPrincipalIdealRing O := hDvr.toIsPrincipalIdealRing
    have : IsDomain A := MulEquiv.isDomain O (ULift.ringEquiv (R := O)).toMulEquiv
    have : IsPrincipalIdealRing A :=
      IsPrincipalIdealRing.of_surjective ULift.ringEquiv.symm ULift.ringEquiv.symm.surjective
    refine ⟨P, b, c, hb, hc, ?_, ⟨e⟩, ?_⟩
    · intro q
      have : Module.Projective A (P.X q) := (hP q).1
      have : Module.Finite A (P.X q) := (hP q).2
      have : Module.IsTorsionFree A (P.X q) := by
        obtain ⟨f, hf⟩ := (inferInstance : Module.Projective A (P.X q)).out
        exact Function.Injective.moduleIsTorsionFree f hf.injective f.map_smul
      exact ⟨inferInstance, inferInstance⟩
    · intro q
      have : Module.Finite A (P.X q) := (hP q).2
      have : Module.Finite A (P.cycles q) :=
        Module.Finite.of_injective (P.iCycles q).hom
          ((ModuleCat.mono_iff_injective _).1 inferInstance)
      have : Module.Finite A (P.homology q) :=
        Module.Finite.of_surjective (P.homologyπ q).hom
          ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      let F := integralHeartRealization.{u} ℓ E (𝒰.X i)
      obtain ⟨hFlim, hFcolim, _⟩ := integralHeartRealization_exact_free ℓ E (𝒰.X i)
      have : PreservesFiniteLimits F := hFlim
      have : PreservesFiniteColimits F := hFcolim
      let G := CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
        (𝒰.f i ≫ s.immersion a)
      exact ⟨inferInstance, ⟨(G.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
        (DerivedCategory.homologyFunctorFactors _ q).app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
        (F.mapHomologicalComplexHomologyIso (.up ℤ) q).app P⟩⟩
  · intro q
    have hq : constantModelBoundedConstructible
        (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
        (integralHeartCohomology.{u} ℓ E X K q) := hs _ (hK.2 q)
    exact ⟨integralHeart_constructible_module_complete ℓ E X _ (hK.2 q), hq⟩

end AlgebraicGeometry.ProEtale
