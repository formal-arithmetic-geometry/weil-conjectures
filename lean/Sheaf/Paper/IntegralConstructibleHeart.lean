/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.IntegralConstantModelHeart
public import Sheaf.Paper.IntegralHeartLocalModel
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Sheaf.Paper.IntegralHeartDualizable
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Structure of integral constructible complexes

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-lem-int-integral-heart/_section.md`, assertions (1)--(3), and its proof;
Stacks Project, Tags 099I, 09C2, 09C7, 09C4, 0990, 099Q, 099Y
(blueprint: sk-lem-int-integral-heart).

The coefficients are the completed continuous coefficient sheaf, and the ambient
category is the ordinary unbounded derived category of its internal module objects.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

-- Keep the coefficient structure explicit while transporting the categorical package.
private def categoricalHeartProperty
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
private noncomputable def canonicalCoefficient
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    {m : MonObj (integralHeartCoefficientRingObj.{u} ℓ E) //
      @IsCommMonObj _ _ _ _ _ m} := ⟨inferInstance, inferInstance⟩

attribute [-instance] SmallAdicCompletion.Coefficients.integerRingMonObj
  SmallAdicCompletion.Coefficients.integerRingComm in
private theorem categoricalHeart_canonical
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    categoricalHeartProperty (integralHeartCoefficientRingObj ℓ E)
      (canonicalCoefficient.{u} ℓ E).val (canonicalCoefficient.{u} ℓ E).property X := by
  have h := @integralConstantModelHeart.{u, v} k ‹Field k› p ‹CharP k p› hp
    ℓ ‹Fact ℓ.Prime› hℓ E ‹Field E› ‹Algebra (Padic ℓ) E›
    ‹FiniteDimensional (Padic ℓ) E› X ‹X.Over (Spec (.of k))›
    ‹IsSeparated (X ↘ Spec (.of k))› ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    ‹QuasiCompact (X ↘ Spec (.of k))›
  unfold categoricalHeartProperty
  exact h

attribute [local irreducible] categoricalHeartProperty

private theorem coefficient_transport
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (P : {m : MonObj (integralHeartCoefficientRingObj.{u} ℓ E) //
      @IsCommMonObj _ _ _ _ _ m} → Prop)
    (h : P (canonicalCoefficient.{u} ℓ E)) :
    P ⟨SmallAdicCompletion.Coefficients.integerRingMonObj.{u} ℓ E,
      SmallAdicCompletion.Coefficients.integerRingComm.{u} ℓ E⟩ := by
  have heq : (⟨SmallAdicCompletion.Coefficients.integerRingMonObj.{u} ℓ E,
      SmallAdicCompletion.Coefficients.integerRingComm.{u} ℓ E⟩ :
      {m : MonObj (integralHeartCoefficientRingObj.{u} ℓ E) //
        @IsCommMonObj _ _ _ _ _ m}) = canonicalCoefficient.{u} ℓ E := by
    exact Subtype.ext (show _ = _ from rfl)
  exact (congrArg P heq).mpr h

private theorem categoricalHeart_cached
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    categoricalHeartProperty (integralHeartCoefficientRingObj ℓ E)
      (SmallAdicCompletion.Coefficients.integerRingMonObj ℓ E)
      (SmallAdicCompletion.Coefficients.integerRingComm ℓ E) X := by
  have h := @categoricalHeart_canonical.{u, v} k ‹Field k› p ‹CharP k p› hp
    ℓ ‹Fact ℓ.Prime› hℓ E ‹Field E› ‹Algebra (Padic ℓ) E›
    ‹FiniteDimensional (Padic ℓ) E› X ‹X.Over (Spec (.of k))›
    ‹IsSeparated (X ↘ Spec (.of k))› ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    ‹QuasiCompact (X ↘ Spec (.of k))›
  exact coefficient_transport ℓ E (fun x ↦ categoricalHeartProperty
    (integralHeartCoefficientRingObj.{u} ℓ E) x.val x.property X) h

private theorem single_constructible_of_essImage
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

private def singleConstructibleProperty
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (m : MonObj Λ) (hc : @IsCommMonObj _ _ _ _ Λ m) (X : Scheme.{u}) : Prop :=
  letI := m
  letI := hc
  ∀ C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X),
    IsConstantModelConstructible Λ X C →
      constantModelBoundedConstructible Λ X ((DerivedCategory.singleFunctor _ 0).obj C)

attribute [local irreducible] singleConstructibleProperty

private theorem singleConstructible_cached
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    singleConstructibleProperty (SmallAdicCompletion.Coefficients.integerRing ℓ E)
      (SmallAdicCompletion.Coefficients.integerRingMonObj ℓ E)
      (SmallAdicCompletion.Coefficients.integerRingComm ℓ E) X := by
  have h := @categoricalHeart_cached.{u, v} k ‹Field k› p ‹CharP k p› hp
    ℓ ‹Fact ℓ.Prime› hℓ E ‹Field E› ‹Algebra (Padic ℓ) E›
    ‹FiniteDimensional (Padic ℓ) E› X ‹X.Over (Spec (.of k))›
    ‹IsSeparated (X ↘ Spec (.of k))› ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    ‹QuasiCompact (X ↘ Spec (.of k))›
  unfold categoricalHeartProperty at h
  unfold singleConstructibleProperty
  exact single_constructible_of_essImage _ X h.2.2.2.2.2.1

private theorem finiteModels_of_single
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (C : SmallAdicCompletion.Modules ℓ E X)
    (hK : constantModelBoundedConstructible
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
      ((DerivedCategory.singleFunctor _ 0).obj C)) :
    ∃ s : Scheme.FiniteLocallyClosedStratification X,
      (∀ a : Fin s.n, Topology.IsConstructible (s.stratum a)) ∧
      ∀ a : Fin s.n,
        ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
          ∀ i : 𝒰.I₀,
            ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
              Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
              Nonempty ((CondensedRing.upperStar
                (SmallAdicCompletion.Coefficients.integerRing ℓ E)
                (𝒰.f i ≫ s.immersion a)).obj C ≅
                (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj N) := by
  let K : integralHeartDerivedCategory.{u} ℓ E X :=
    (DerivedCategory.singleFunctor _ 0).obj C
  have lm := @integralHeartLocalModel.{u, v} k ‹Field k› p ‹CharP k p› _hp
    ℓ ‹Fact ℓ.Prime› (Ne.symm _hℓ) E ‹Field E› ‹Algebra (Padic ℓ) E›
    ‹FiniteDimensional (Padic ℓ) E› X ‹X.Over (Spec (.of k))›
    ‹IsSeparated (X ↘ Spec (.of k))› ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    ‹QuasiCompact (X ↘ Spec (.of k))›
  obtain ⟨s, hs, hmodels⟩ := (lm K hK).1
  have hmodel (a : Fin s.n) :
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
        ∀ i : 𝒰.I₀,
          ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
            Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
            Nonempty ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
                (𝒰.f i ≫ s.immersion a)).obj C ≅
              (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj N) := by
    obtain ⟨𝒰, h𝒰⟩ := hmodels a
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, b, c, hb, hc, hfree, hP, hcoh⟩ := h𝒰 i
    obtain ⟨hfinite, ⟨e⟩⟩ := hcoh 0
    refine ⟨P.homology 0, hfinite, ⟨?_⟩⟩
    exact ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
      (𝒰.f i ≫ s.immersion a)).mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app C).symm) ≪≫ e
  exact ⟨s, hs, hmodel⟩

-- Delay unfolding derived categories until after the stratification conversion.
private def stratumDualProperty
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    {X : Scheme.{u}} (S : Scheme.{u}) (f : S ⟶ X)
    (C : SmallAdicCompletion.Modules ℓ E X) : Prop :=
  ∃ D : integralHeartDerivedCategory.{u} ℓ E S,
    Nonempty (ExactPairing D (integralHeartStratumComplex ℓ E f C)) ∧
    DerivedCategory.torAmplitudeIn _ (-1) 0 (integralHeartStratumComplex ℓ E f C) ∧
    DerivedCategory.torAmplitudeIn _ 0 1 D

attribute [local irreducible] stratumDualProperty

private def finiteModelProperty
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    {X : Scheme.{u}} (S : Scheme.{u}) (f : S ⟶ X)
    (C : SmallAdicCompletion.Modules ℓ E X) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
    ∀ i : 𝒰.I₀, ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
      Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
      Nonempty ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
        (𝒰.f i ≫ f)).obj C ≅ (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj N)

attribute [local irreducible] finiteModelProperty

private theorem stratumDualExact
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) (C : SmallAdicCompletion.Modules ℓ E X)
    (_hC : IsConstantModelConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X C)
    (s : Scheme.Stratification X) (a : Fin s.n)
    (_hmodel : finiteModelProperty ℓ E (s.domain a) (s.immersion a) C) :
    stratumDualProperty ℓ E (s.domain a) (s.immersion a) C := by
  unfold stratumDualProperty
  unfold finiteModelProperty at _hmodel
  obtain ⟨⟨hp⟩, ht, hd, _⟩ := integralHeartDualizable ℓ E X C _hC s a _hmodel
  obtain ⟨braiding⟩ := DerivedCategory.nonempty_braidedCategory
    (SmallAdicCompletion.Modules ℓ E (s.domain a))
  let := braiding
  let := hp
  exact ⟨_, ⟨BraidedCategory.exactPairing_swap _ _⟩, ht, hd⟩

private theorem localModelsDuals
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
  ∀ C : SmallAdicCompletion.Modules ℓ E X,
  IsConstantModelConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X C →
  ∃ s : Scheme.FiniteLocallyClosedStratification X,
    (∀ a : Fin s.n, Topology.IsConstructible (s.stratum a)) ∧
    ∀ a : Fin s.n,
      (∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
        ∀ i : 𝒰.I₀,
          ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
            Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
            Nonempty ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
                (𝒰.f i ≫ s.immersion a)).obj C ≅
              (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj N)) ∧
      ∃ D : integralHeartDerivedCategory.{u} ℓ E (s.domain a),
        Nonempty (ExactPairing D
          (integralHeartStratumComplex ℓ E (s.immersion a) C)) ∧
        DerivedCategory.torAmplitudeIn _ (-1) 0
          (integralHeartStratumComplex ℓ E (s.immersion a) C) ∧
        DerivedCategory.torAmplitudeIn _ 0 1 D := by
  intro C hC
  have hc := @singleConstructible_cached.{u, v} k ‹Field k› p ‹CharP k p› _hp
    ℓ ‹Fact ℓ.Prime› _hℓ E ‹Field E› ‹Algebra (Padic ℓ) E›
    ‹FiniteDimensional (Padic ℓ) E› X ‹X.Over (Spec (.of k))›
    ‹IsSeparated (X ↘ Spec (.of k))› ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    ‹QuasiCompact (X ↘ Spec (.of k))›
  unfold singleConstructibleProperty at hc
  have hK := hc C hC
  obtain ⟨s, hs, hmodel⟩ := finiteModels_of_single k p _hp ℓ _hℓ E X C hK
  let t : Scheme.Stratification X :=
    { n := s.n
      stratum := s.stratum
      isLocallyClosed_stratum := s.isLocallyClosed_stratum
      isConstructible_stratum := hs
      iUnion_stratum_eq_univ := s.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := s.pairwise_disjoint_stratum
      domain := s.domain
      immersion := s.immersion
      isImmersion := s.isImmersion
      range_immersion := s.range_immersion }
  refine ⟨s, hs, fun a ↦ ⟨hmodel a, ?_⟩⟩
  have hm : finiteModelProperty ℓ E (s.domain a) (s.immersion a) C := by
    unfold finiteModelProperty
    exact hmodel a
  have hd : stratumDualProperty ℓ E (s.domain a) (s.immersion a) C :=
    stratumDualExact ℓ E X C hC t a hm
  unfold stratumDualProperty at hd
  exact hd

end

/-- The integral constructible derived category is triangulated and stable under
standard truncations, with essentially small extension-closed abelian heart. Every
heart object has finite module models on a finite stratification, and its restrictions
and their duals have Tor amplitudes [-1,0] and [0,1] on those very strata.
Source: blueprint main-20261015, sk-lem-int-integral-heart, assertions (1)--(3)
(blueprint: sk-lem-int-integral-heart).

Proof (the four steps of the DAG node):
1. The finite-type integral-model setting of sk-lem-integral-models makes X Noetherian.
Apply det-lem-int-integral-heart-triangulated(1): the bounded constructible predicate
is closed under isomorphisms, triangulated, bounded, and stable under both truncations.
2. By sk-def-sfb-constructible, a module in degree zero belongs to Dbc exactly when
it is constructible. The fully faithful single functor identifies every degree-zero
object with its H^0. Apply det-lem-int-integral-heart-triangulated(2) for ambient
kernels and cokernels, abelianness, extension closure, and essential smallness.
3. Given a constructible C, place it in degree zero by step 2. Apply
 det-lem-int-integral-heart-local-model(1),(2) and take q = 0. Its same finite strata
and charts identify C with the completed realization of the finite scalar module
H^0 of the finite free complex. This allows torsion in that module.
4. On each of those strata, det-lem-int-integral-heart-dualizable gives the derived
dual and its evaluation and coevaluation satisfying both triangle identities, encoded
by ExactPairing. A finite module over the coefficient DVR has a finite free resolution
in degrees [-1,0]; flat completed scalar extension preserves it. Dualizing gives a
finite free complex in degrees [0,1]. These compute Tor against every module sheaf,
including torsion sheaves. In particular O_E/pi has derived dual (O_E/pi)[-1]. -/
theorem integral_constructible_heart
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsTriangulated
      (constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    (∀ K, constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X K →
      DerivedCategory.TStructure.t.bounded K ∧ ∀ n : ℤ,
        constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X
          ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
        constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X
          ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (ObjectProperty.ι (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
      DerivedCategory.singleFunctor _ 0).Full ∧
    (ObjectProperty.ι (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
      DerivedCategory.singleFunctor _ 0).Faithful ∧
    (∀ K, (ObjectProperty.ι
        (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
        DerivedCategory.singleFunctor _ 0).essImage K ↔
      constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X K ∧
      DerivedCategory.TStructure.t.le 0 K ∧ DerivedCategory.TStructure.t.ge 0 K) ∧
    Nonempty (Abelian (ConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X)) ∧
    ObjectProperty.IsClosedUnderKernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderCokernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderExtensions
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    EssentiallySmall.{u + 1}
      (ConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    (∀ C : SmallAdicCompletion.Modules ℓ E X,
      IsConstantModelConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X C →
      ∃ s : Scheme.FiniteLocallyClosedStratification X,
        (∀ a : Fin s.n, Topology.IsConstructible (s.stratum a)) ∧
        ∀ a : Fin s.n,
          (∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
            ∀ i : 𝒰.I₀,
              ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
                Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
                Nonempty ((CondensedRing.upperStar
                    (SmallAdicCompletion.Coefficients.integerRing ℓ E)
                    (𝒰.f i ≫ s.immersion a)).obj C ≅
                  (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj N)) ∧
          ∃ D : integralHeartDerivedCategory.{u} ℓ E (s.domain a),
            Nonempty (ExactPairing D
              (integralHeartStratumComplex ℓ E (s.immersion a) C)) ∧
            DerivedCategory.torAmplitudeIn _ (-1) 0
              (integralHeartStratumComplex ℓ E (s.immersion a) C) ∧
            DerivedCategory.torAmplitudeIn _ 0 1 D) := by
  classical
  have h := @categoricalHeart_cached.{u, v} k ‹Field k› p ‹CharP k p› _hp
    ℓ ‹Fact ℓ.Prime› _hℓ E ‹Field E› ‹Algebra (Padic ℓ) E›
    ‹FiniteDimensional (Padic ℓ) E› X ‹X.Over (Spec (.of k))›
    ‹IsSeparated (X ↘ Spec (.of k))› ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    ‹QuasiCompact (X ↘ Spec (.of k))›
  unfold categoricalHeartProperty at h
  constructor
  · exact h.1
  constructor
  · exact h.2.1
  constructor
  · exact h.2.2.1
  constructor
  · exact h.2.2.2.1
  constructor
  · exact h.2.2.2.2.1
  constructor
  · exact h.2.2.2.2.2.1
  constructor
  · exact h.2.2.2.2.2.2.1
  constructor
  · exact h.2.2.2.2.2.2.2.1
  constructor
  · exact h.2.2.2.2.2.2.2.2.1
  constructor
  · exact h.2.2.2.2.2.2.2.2.2.1
  constructor
  · exact h.2.2.2.2.2.2.2.2.2.2
  have hm := @localModelsDuals.{u, v} k ‹Field k› p ‹CharP k p› _hp
    ℓ ‹Fact ℓ.Prime› _hℓ E ‹Field E› ‹Algebra (Padic ℓ) E›
    ‹FiniteDimensional (Padic ℓ) E› X ‹X.Over (Spec (.of k))›
    ‹IsSeparated (X ↘ Spec (.of k))› ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    ‹QuasiCompact (X ↘ Spec (.of k))›
  exact hm

end AlgebraicGeometry.ProEtale
