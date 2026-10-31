/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
public import WeilConjectures.AlgebraicGeometry.BoundedBelowProEtaleComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.AlgebraicGeometry.FixedModuleGeometricStalkFunctors
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleExceptionalOriginTransfer
import WeilConjectures.AlgebraicGeometry.ProEtaleResidueComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleResiduesZeroCharacterization
import WeilConjectures.AlgebraicGeometry.ProEtalePerfectStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonStalk
import WeilConjectures.AlgebraicGeometry.ComparisonTorInterval
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import WeilConjectures.AlgebraicGeometry.EtaleModuleStalkCohomologyTest
import WeilConjectures.AlgebraicGeometry.EtaleStalkTorTest
import WeilConjectures.SixFunctors.GeometricStalkTensorConstantSingle
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import WeilConjectures.Algebra.Homology.FreeComplexResidueTensorExact
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.Algebra.Homology.FreeComplexResidueDegreeCancellation
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.Algebra.Homology.MinimalComplex
import WeilConjectures.Algebra.Homology.LocalizedExactPairContraction
import Mathlib.Algebra.Exact.Basic
import WeilConjectures.Algebra.Homology.PrincipalContractionSpreading
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Residue coefficients detect finite-Tor constructible isomorphisms

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-lem-sf-kunneth-star/
sk-lem-sf-kunneth-star.proof.md, arbitrary finite coefficient rings (devissage);
Stacks Project, more-algebra.tex, Tags 066E, 0658 and 068V
(blueprint: lem-sf-finite-ring-residue-conservativity).

Residue tensors are displayed after restriction to A-modules. Forgetting the quotient-ring
module action reflects zero objects and isomorphisms, so this is exactly the derived
extension-of-scalars test, computed by the existing K-flat derived tensor. No flatness of
A/m over A is assumed. The pro-etale stalk is evaluated termwise on any representative,
using the existing pointed-neighbourhood module-stalk functor.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme

namespace DerivedCategory

/-- A perfect complex over a finite commutative ring is zero if all its derived maximal
residues are zero. Source: blueprint Kunneth proof, arbitrary finite coefficient rings;
Stacks Project, Tags 066E and 068V
(blueprint: lem-sf-finite-ring-residue-conservativity).

Proof: A finite ring is Noetherian. A bounded finite-projective representative has finite
terms, hence bounded-above finite cohomology, so P is pseudo-coherent by
lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion: P is represented by a
bounded-above complex P₁ of finite free modules. P₁ is K-flat
(lem-sfb-bounded-above-flat-kflat), so the derived tensor of P with a single module M is
the termwise tensor P₁ ⊗ M (lem-weil-pbc-source-kflat-tensor-single-model). The residue
hypothesis makes every homology of P₁ ⊗ A/m zero; by
lem-weil-pbc-free-complex-residue-tensor-exact every homology of P₁ ⊗ M is then zero for
every module M, in particular for M = A, where P₁ ⊗ A ≅ P via the unit isomorphism.
A derived object with zero homology in every degree is zero. If A is the zero ring,
every unital module is zero, so the empty family of maximal ideals is harmless. -/
theorem isZero_of_isPerfect_finiteRing_residues
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [HasDerivedCategory.{w} (ModuleCat.{u + 1} A)]
    (P : DerivedCategory (ModuleCat.{u + 1} A)) (_hP : P.IsPerfectRingComplex)
    (_hres : ∀ m : Ideal A, m.IsMaximal →
      IsZero (P ⊗ (singleFunctor (ModuleCat.{u + 1} A) 0).obj
        (ModuleCat.of A (A ⧸ m)))) :
    IsZero P := by
  obtain ⟨P₀, a, b, ha, hb, hfin, ⟨e₀⟩⟩ := _hP
  have : P₀.IsStrictlyLE b := hb
  have hPC : P.IsPseudoCoherent := by
    apply (isPseudoCoherent_iff_boundedAbove_finite_homology.{w, u + 1, u + 1} A P).2
    constructor
    · refine ⟨b, fun i hi ↦ ?_⟩
      exact (isZero_of_isLE (Q.obj P₀) b i hi).of_iso
        ((homologyFunctor (ModuleCat.{u + 1} A) i).mapIso e₀)
    · intro i
      have : Module.Finite A (P₀.X i) := (hfin i).2
      have : Module.Finite A (P₀.cycles i) :=
        Module.Finite.of_injective (P₀.iCycles i).hom
          ((ModuleCat.mono_iff_injective _).1 inferInstance)
      have : Module.Finite A (P₀.homology i) :=
        Module.Finite.of_surjective (P₀.homologyπ i).hom
          ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      have : Module.Finite A ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A)
          (ComplexShape.up ℤ) i).obj P₀) := ‹Module.Finite A (P₀.homology i)›
      let e : P₀.homology i ≅
          (homologyFunctor (ModuleCat.{u + 1} A) i).obj P :=
        ((homologyFunctorFactors (ModuleCat.{u + 1} A) i).app P₀).symm ≪≫
          (homologyFunctor (ModuleCat.{u + 1} A) i).mapIso e₀.symm
      exact Module.Finite.of_surjective e.hom.hom
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  obtain ⟨P₁, c, hc, hP₁, ⟨e₁⟩⟩ := hPC
  have : P₁.IsStrictlyLE c := hc
  have hflat := CochainComplex.kFlat_of_isStrictlyLE_of_flat P₁ c fun j ↦ by
    have := (hP₁ j).1
    exact (ModuleCat.flat_iff_flat _).2 inferInstance
  let eH (M : ModuleCat.{u + 1} A) (i : ℤ) :
      (homologyFunctor (ModuleCat.{u + 1} A) i).obj
          (P ⊗ (singleFunctor (ModuleCat.{u + 1} A) 0).obj M) ≅
        (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P₁).homology i :=
    (homologyFunctor (ModuleCat.{u + 1} A) i).mapIso
      (whiskerRightIso e₁.symm _ ≪≫ QObjTensorSingleFunctorObjIso P₁ hflat M) ≪≫
      (homologyFunctorFactors _ i).app _
  let eunit : P ⊗ (singleFunctor (ModuleCat.{u + 1} A) 0).obj (ModuleCat.of A A) ≅ P :=
    whiskerLeftIso P (singleFunctorObjUnitIso (ModuleCat.{u + 1} A)) ≪≫ ρ_ P
  apply isZero_of_forall_isZero_homology
  intro i
  apply IsZero.of_iso _ ((homologyFunctor (ModuleCat.{u + 1} A) i).mapIso eunit).symm
  apply IsZero.of_iso _ (eH (ModuleCat.of A A) i)
  apply CochainComplex.isZero_homology_tensor_of_residue P₁
    (fun j ↦ (hP₁ j).1) (fun j ↦ (hP₁ j).2) i
  intro m hm
  exact ((homologyFunctor (ModuleCat.{u + 1} A) i).map_isZero (_hres m hm)).of_iso
    (eH (ModuleCat.of A (A ⧸ m)) i).symm

end DerivedCategory

namespace AlgebraicGeometry.Etale
private theorem finiteRing_perfect_stalks
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (C : DerivedCategoryModule A S)
    (hC : ProEtale.exceptionalTransportEtaleObjects A S C) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      _root_.DerivedCategory.IsPerfectRingComplex
        (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)).mapDerivedCategory.obj C) := by
  unfold ProEtale.exceptionalTransportEtaleObjects at hC
  intro Ω _ _ s
  let F := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)
  obtain ⟨a, b, hab, htor⟩ := hC.2
  have htor' : _root_.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) a b
      (F.mapDerivedCategory.obj C) := by
    intro M
    rw [_root_.DerivedCategory.homologyConcentratedIn_iff]
    exact ⟨(_root_.DerivedCategory.isGE_iff _ a).2 (fun i hi ↦
        (geometricStalk_torAmplitude_test A S C a b hab).1.mp htor Ω s M i (.inl hi)),
      (_root_.DerivedCategory.isLE_iff _ b).2 (fun i hi ↦
        (geometricStalk_torAmplitude_test A S C a b hab).1.mp htor Ω s M i (.inr hi))⟩
  have hpc : _root_.DerivedCategory.IsPseudoCoherent (F.mapDerivedCategory.obj C) := by
    apply (_root_.DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology.{
      u + 1, u + 1, u + 1} A (F.mapDerivedCategory.obj C)).2
    constructor
    · obtain ⟨c, d, hcd, hz⟩ := hC.1.2
      refine ⟨d, fun i hi ↦ ?_⟩
      exact (F.map_isZero (hz i (.inr hi))).of_iso
        ((F.mapDerivedCategoryHomologyFunctorIso i).app C).symm
    · intro i
      have hfin := Scheme.constructibleModule_finite_geometric_stalk _
        (hC.1.1 i) Ω s
      let : Module.Finite A
          (F.obj ((_root_.DerivedCategory.homologyFunctor
            (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj C)) := hfin.2
      let e : F.obj ((_root_.DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj C) ≅
          (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i).obj
            (F.mapDerivedCategory.obj C) := (F.mapDerivedCategoryHomologyFunctorIso i).app C
      exact Module.Finite.equiv e.toLinearEquiv
  obtain ⟨P, ⟨c, d, hz⟩, hfin, hproj, ⟨e⟩⟩ :=
    _root_.DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude
      (F.mapDerivedCategory.obj C) hpc ⟨a, b, hab, htor'⟩
  refine ⟨P, c, d, ?_, ?_, fun i ↦ ⟨hproj i, hfin i⟩, ⟨e.symm⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ hz i (.inl hi)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ hz i (.inr hi)

private theorem finiteRing_isZero_of_residues
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (C : DerivedCategoryModule A S)
    (hC : ProEtale.exceptionalTransportEtaleObjects A S C)
    (hres : ∀ m : Ideal A, m.IsMaximal →
      IsZero ((reductionModIdeal A S m).obj C)) : IsZero C := by
  apply _root_.DerivedCategory.isZero_of_forall_isZero_homology C
  intro i
  apply (etaleModuleStalk_cohomology_test A S C i).2
  intro Ω _ _ s
  let F := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)
  have hP := finiteRing_perfect_stalks A S C hC Ω s
  have hz : IsZero (F.mapDerivedCategory.obj C) := by
    apply _root_.DerivedCategory.isZero_of_isPerfect_finiteRing_residues A
      (F.mapDerivedCategory.obj C) hP
    intro m hm
    have hz := F.mapDerivedCategory.map_isZero (hres m hm)
    exact hz.of_iso (geometricStalk_tensor_constant_single A s C
      (ModuleCat.of A (A ⧸ m))).some.symm
  exact (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i).map_isZero hz


/-- Residue coefficient changes detect isomorphisms in the bounded constructible finite-Tor
etale category. Source: blueprint Kunneth proof, arbitrary finite coefficient rings;
Stacks Project, Tags 0658, 068V, 0DJJ and 03PU
(blueprint: lem-sf-finite-ring-residue-conservativity).

Proof: Form the signed cone of u. The long exact cohomology sequence
lem-sf-derived-homology-long-exact and thm-constructible-serre give bounded constructible
cohomology. If the endpoint Tor intervals are [a,b] and [a',b'], triangulatedness of tensor
lem-kun-derived-tensor-triangulated gives the cone interval
[min(a',a-1), max(b',b-1)]. Every residue cone is zero by the same long exact sequence.
At every geometric point, lem-sf-etale-module-stalk-cohomology-test and
lem-weil-pbc-constructible-module-finite-stalks give bounded finite cohomology, while
lem-sf-etale-stalk-tor-test gives finite Tor amplitude. The finite ring is Noetherian;
lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion and
lem-pc-ring-pseudo-coherent-finite-tor-perfect give a perfect stalk. By
lem-sfb-geometric-stalk-tensor-constant-single its residues are zero. Apply the scalar
perfect-complex criterion above. The stalk cohomology test now makes the cone zero,
hence u invertible. Empty schemes and the zero coefficient ring are included. -/
theorem finiteRing_residue_conservativity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    {K K' : DerivedCategoryModule A S}
    (_hK : ProEtale.exceptionalTransportEtaleObjects A S K)
    (_hK' : ProEtale.exceptionalTransportEtaleObjects A S K')
    (u : K ⟶ K')
    (_hres : ∀ m : Ideal A, m.IsMaximal → IsIso ((reductionModIdeal A S m).map u)) :
    IsIso u := by
  obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle u
  let P := ProEtale.exceptionalTransportEtaleObjects A S
  have hbc (Z : Etale.DerivedCategoryModule A S) :
      Etale.DerivedCategory.isBoundedConstructible A S Z ↔
        Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) S Z := by
    constructor
    · rintro ⟨hc, a, b, _, h⟩
      exact ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff Z a).mpr
        (fun i hi ↦ h i (Or.inl hi))⟩,
        ⟨b, (_root_.DerivedCategory.isLE_iff Z b).mpr
          (fun i hi ↦ h i (Or.inr hi))⟩⟩,
        fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
          (hc i)⟩
    · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
      refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
        (hc i), min a b, b, min_le_right _ _, ?_⟩
      intro i hi
      rcases hi with hi | hi
      · exact (_root_.DerivedCategory.isGE_iff Z a).mp ha i
          (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (_root_.DerivedCategory.isLE_iff Z b).mp hb i hi
  have hPeq : P = Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) S := by
    funext Z
    apply propext
    constructor
    · rintro ⟨hZ, a, b, hab, ht⟩
      refine ⟨(hbc Z).mp hZ, a, b, ?_⟩
      exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht
    · rintro ⟨hZ, a, b, ht⟩
      refine ⟨(hbc Z).mpr hZ, min a b, b, min_le_right _ _, ?_⟩
      exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
        (_root_.DerivedCategory.torAmplitudeIn.mono (min_le_left _ _) le_rfl ht)
  have : P.IsTriangulated := by
    rw [hPeq]
    infer_instance
  have : P.IsClosedUnderIsomorphisms := by
    rw [hPeq]
    infer_instance
  have hP : P C := by
    exact P.ext_of_isTriangulatedClosed₃ (Pretriangulated.Triangle.mk u g h) hT _hK _hK'
  have hresC : ∀ m : Ideal A, m.IsMaximal →
      IsZero ((reductionModIdeal A S m).obj C) := by
    intro m hm
    apply (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((reductionModIdeal A S m).map_distinguished _ hT)).2
    exact _hres m hm
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1
    (finiteRing_isZero_of_residues A S C hP hresC)

/-- The zero-complex formulation and perfectness of all geometric stalks. Taking C to be
a cone gives the cone formulation; conversely every C is the cone of 0 → C.
Source: blueprint Kunneth proof, arbitrary finite coefficient rings; Stacks Project,
Tags 066E, 0658, 068V, 0DJJ and 03PU
(blueprint: lem-sf-finite-ring-residue-conservativity).

Proof: At each geometric point, exact stalks commute with cohomology by
lem-sf-etale-module-stalk-cohomology-test. Constructible cohomology has finite stalks by
lem-weil-pbc-constructible-module-finite-stalks, and lem-sf-etale-stalk-tor-test gives
finite Tor amplitude. Since A is Noetherian, apply
lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion and
lem-pc-ring-pseudo-coherent-finite-tor-perfect to obtain a bounded finite-projective model.
If all residue tensors of C vanish, lem-sfb-geometric-stalk-tensor-constant-single makes
all residues of these perfect stalks zero. The scalar assertion makes each stalk zero,
and lem-sf-etale-module-stalk-cohomology-test gives zero cohomology sheaves in every degree,
hence a zero derived object. Conversely derived tensor sends the zero complex to zero.
For cones, bounded constructibility and finite Tor amplitude follow from the long exact
sequence and lem-kun-derived-tensor-triangulated as in the morphism formulation. -/
theorem finiteRing_residues_zero_iff_and_perfect_stalks
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (C : DerivedCategoryModule A S)
    (_hC : ProEtale.exceptionalTransportEtaleObjects A S C) :
    (IsZero C ↔ ∀ m : Ideal A, m.IsMaximal → IsZero ((reductionModIdeal A S m).obj C)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        _root_.DerivedCategory.IsPerfectRingComplex
          (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)).mapDerivedCategory.obj
            C) := by
  refine ⟨⟨fun hz m hm ↦ by
      let : (reductionModIdeal A S m).PreservesZeroMorphisms := inferInstanceAs
        (((derivedTensor (ModuleCat.{u + 1} A) S).flip.obj _).PreservesZeroMorphisms)
      exact (reductionModIdeal A S m).map_isZero hz,
    fun hres ↦ finiteRing_isZero_of_residues A S C _hC hres⟩,
    finiteRing_perfect_stalks A S C _hC⟩

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- Residues detect morphisms between classical bounded constructible finite-Tor pro-etale
complexes. Classical means inverse image of a bounded-below etale complex, without a
chosen origin. Source: blueprint Kunneth proof, arbitrary finite coefficient rings;
Stacks Project, Tags 09AL, 09B1, 07A4, 0G7E and 03PU
(blueprint: lem-sf-finite-ring-residue-conservativity).

Proof: By lem-weil-pbc-finite-ring-constructible-derived-origin choose bounded constructible
etale models of the two endpoints. Full faithfulness in sk-prop-sf-comparison lifts the
conjugated arrow uniquely. The models have the same Tor intervals by
lem-exc-comparison-tor-interval. For every quotient A/m,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback and preservation of constant sheaves
identify the comparison inverse image of the residue arrow with the given residue arrow.
The Tor bounds make these etale residue objects bounded below. Full faithfulness of
sk-prop-sf-comparison, with coefficient A/m, reflects the residue isomorphism. The etale
assertion applies to the lifted arrow: its cone is bounded constructible finite-Tor,
its geometric stalks are perfect by Tags 066E and 0658, its residue stalks vanish by
lem-sfb-geometric-stalk-tensor-constant-single, and the scalar criterion gives zero
stalks. The cohomology stalk test gives zero cone, hence an invertible lifted arrow.
Comparison inverse image sends this isomorphism to u under the endpoint identifications.
The zero ring and the empty scheme require no exclusions. -/
theorem finiteRing_residue_conservativity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    {K K' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))}
    (_hK : exceptionalTransportProEtaleObjects A S K)
    (_hK' : exceptionalTransportProEtaleObjects A S K')
    (_hclassicalK : ∃ E : Etale.DerivedCategoryModule A S,
      _root_.DerivedCategory.TStructure.t.plus E ∧
        Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj E ≅ K))
    (_hclassicalK' : ∃ E : Etale.DerivedCategoryModule A S,
      _root_.DerivedCategory.TStructure.t.plus E ∧
        Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj E ≅ K'))
    (u : K ⟶ K')
    (_hres : ∀ m : Ideal A, m.IsMaximal →
      IsIso (((derivedTensor (ModuleCat.{u + 1} A) S).map u).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A (A ⧸ m)))))) :
    IsIso u := by
  classical
  obtain ⟨E, hE, hEplus, ⟨eK⟩⟩ :=
    exceptional_etale_origin_of_pro_origin A S _hK _hclassicalK
  obtain ⟨E', hE', hE'plus, ⟨eK'⟩⟩ :=
    exceptional_etale_origin_of_pro_origin A S _hK' _hclassicalK'
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory
  let v : F.obj E ⟶ F.obj E' := eK.hom ≫ u ≫ eK'.inv
  let w : E ⟶ E' := Classical.choose
    ((AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
      E E' hE'plus).2 v)
  have hw : F.map w = v := Classical.choose_spec
    ((AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
      E E' hE'plus).2 v)
  have hresE : ∀ m : Ideal A, m.IsMaximal →
      IsIso ((Etale.reductionModIdeal A S m).map w) := by
    apply etale_residue_isIso_of_pro_residue_isIso A S hE hE' hEplus hE'plus w eK eK' u
    · exact hw
    · exact _hres
  have hwiso : IsIso w := AlgebraicGeometry.Etale.finiteRing_residue_conservativity
    A S hE hE' w hresE
  have hv : IsIso v := by
    rw [← hw]
    have := hwiso
    infer_instance
  have hi : IsIso (eK.inv ≫ v ≫ eK'.hom) := by infer_instance
  simpa [v] using hi

/-- The classical pro-etale zero-complex formulation and perfectness of every geometric
stalk, computed on any cochain representative. Source: blueprint Kunneth proof, arbitrary
finite coefficient rings; Stacks Project, Tags 09AL, 0993, 066E, 0658, 068V and 03PU
(blueprint: lem-sf-finite-ring-residue-conservativity).

Proof: Use lem-weil-pbc-finite-ring-constructible-derived-origin and
lem-exc-comparison-tor-interval to obtain a bounded constructible finite-Tor etale model.
By lem-cbc-proetale-comparison-stalk the termwise geometric stalk of its comparison image
is the etale geometric stalk, A-linearly. The exactness in lem-cbc-proetale-classical-stalk
makes this identification descend through quasi-isomorphisms, so it applies to every
representative P of C. The etale argument gives bounded finite cohomology and finite Tor
amplitude, hence perfectness by lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion
and lem-pc-ring-pseudo-coherent-finite-tor-perfect. If all residues vanish, tensor pullback
compatibility lem-weil-pbc-ringed-topoi-derived-tensor-pullback and bounded-below full
faithfulness sk-prop-sf-comparison transfer their vanishing to the etale model. Its
perfect stalks vanish by lem-sfb-geometric-stalk-tensor-constant-single and the scalar
criterion; lem-sf-etale-module-stalk-cohomology-test gives a zero model, hence C = 0.
Conversely every residue tensor sends zero to zero. Applying this to the cone proves
the morphism formulation; every C is itself the cone of 0 → C. -/
theorem finiteRing_residues_zero_iff_and_perfect_stalks
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (C : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (_hC : exceptionalTransportProEtaleObjects A S C)
    (_hclassicalC : ∃ E : Etale.DerivedCategoryModule A S,
      _root_.DerivedCategory.TStructure.t.plus E ∧
        Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj E ≅ C)) :
    (IsZero C ↔ ∀ m : Ideal A, m.IsMaximal →
      IsZero (((derivedTensor (ModuleCat.{u + 1} A) S).obj C).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A (A ⧸ m)))))) ∧
      ∀ (P : CochainComplex
        (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)) ℤ),
        Nonempty (_root_.DerivedCategory.Q.obj P ≅ C) →
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
            _root_.DerivedCategory.IsPerfectRingComplex (_root_.DerivedCategory.Q.obj
              (((geometricModuleStalkFunctor A s).mapHomologicalComplex (.up ℤ)).obj P)) := by
  refine ⟨proEtale_residues_zero_iff A S C _hC _hclassicalC, ?_⟩
  exact proEtale_perfect_stalks_of_classical A S C _hC _hclassicalC

end AlgebraicGeometry.ProEtale
