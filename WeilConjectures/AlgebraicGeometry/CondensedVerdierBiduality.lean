/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.DetThmSfCtfStabilityInternalHom
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.NativeInternalHomExact
import WeilConjectures.CategoryTheory.ObjectProperty.Duality
import WeilConjectures.AlgebraicGeometry.CondensedVerdierCoefficientComparison
import WeilConjectures.AlgebraicGeometry.CondensedVerdierFiniteEvaluation
import WeilConjectures.AlgebraicGeometry.CondensedVerdierCoefficientPassage
import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Verdier biduality for actual condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-pd-verdier-duality/_section.md and det-pd-biduality-coefficients.proof.md
(blueprint: lem-sf-condensed-verdier-biduality).

The exceptional inverse image is a right adjoint on the actual constructible
finite-Tor full subcategories. The double-dual map uses the descended Koszul
braiding on the ordinary unbounded derived category of internal modules.
The ambient-category and domain-predicate aliases are the plain definitions of
`def-sf-condensed-constructible-derived-domain`; internal-Hom stability is only
a proof dependency.

## Main definitions and statement

* `condensedVerdierBiduality`: the canonical natural double-dual map.
* `condensedVerdierAmbientSupport`: the prescribed ambient compact-support functor.
* `condensedVerdierSupport`: its restriction to the constructible finite-Tor domain.
* `condensed_verdier_biduality`: preservation, biduality and exact anti-equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped MonoidalCategory ZeroObject
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The natural evaluation transpose for the recorded relative derived internal Hom.
The braiding is the canonical Koszul braiding descended from complexes.
Source: latest blueprint, sk-def-ops, evaluation and double-dual morphism
(blueprint: lem-sf-condensed-verdier-biduality). -/
def condensedVerdierBiduality (T : Scheme.{u}) (ω : moduleDerived Λ T) :
    𝟭 (moduleDerived Λ T) ⟶
      ((derivedHom Λ T).flip.obj ω).rightOp ⋙ (derivedHom Λ T).flip.obj ω :=
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
  MonoidalClosed.toIhomIhomNatTrans ω

/-- The prescribed ambient compactification lower shriek for the structure map.
The two internal instances only unfold the structure morphism of the base point.
Source: latest blueprint, sk-def-ops, compactly supported direct image
(blueprint: lem-sf-condensed-verdier-biduality). -/
def condensedVerdierAmbientSupport {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom] :
    moduleDerived Λ T.left ⥤ moduleDerived Λ (Spec (.of k)) :=
  letI : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))
  letI : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))
  rightDerivedLowerShriekOfCompactification Λ
    (compactificationOverField (Over.mkIdTerminal.from T))

/-- Restriction of the prescribed compactification lower shriek to the actual
constructible finite-Tor categories; its objects and maps are those of that functor.
Source: latest blueprint, sk-def-ops, constructible exceptional adjunction
(blueprint: lem-sf-condensed-verdier-biduality). -/
def condensedVerdierSupport {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom]
    (h : ∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
      dctfPred Λ (Spec (.of k))
        ((condensedVerdierAmbientSupport Λ T).obj K)) :
    ConstantModelConstructibleFiniteTor Λ T.left ⥤
      ConstantModelConstructibleFiniteTor Λ (Spec (.of k)) :=
  (dctfPred Λ (Spec (.of k))).lift
    ((dctfPred Λ T.left).ι ⋙ condensedVerdierAmbientSupport Λ T)
    (fun K ↦ h K.obj K.property)

omit [IsCommMonObj Λ] in
private theorem regular_finitelyPresented : Mod.IsFinitelyPresented Λ (Mod.regular Λ) := by
  let e : Mod.finiteFree Λ 1 ≅ Mod.regular Λ := biproductUniqueIso _
  exact ⟨1, 0, 0, ⟨e.symm ≪≫ (cokernelZeroIsoTarget (X := Mod.finiteFree Λ 0)).symm⟩⟩

omit [IsCommMonObj Λ] in
private theorem zero_finitelyPresented : Mod.IsFinitelyPresented Λ (0 : Mod _ Λ) := by
  exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩

private local instance pointBraided (X : Scheme.{u}) :
    (upperStarFromPoint X).Braided where
  toMonoidal := inferInstance
  braided := Functor.LaxBraided.braided

private theorem model_regular {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj (Mod.regular (condensedRingObj Λ S))) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨Mod.regular Λ, regular_finitelyPresented Λ, ⟨?_⟩⟩
  exact (CondensedRing.upperStar Λ (𝟙 X)).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).symm ≪≫
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (𝟙 X))).symm ≪≫
    Functor.Monoidal.εIso ((upperStarFromPoint X).mapMod Λ)

private theorem model_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj (0 : Mod _ (condensedRingObj Λ S))) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, zero_finitelyPresented Λ, ⟨?_⟩⟩
  exact ((CondensedRing.upperStar Λ (𝟙 X)).map_isZero
    ((CondensedRing.upperStar Λ f).map_isZero (isZero_zero _))).iso
      (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_zero _))

private def oneStratum (X : Scheme.{u}) : Scheme.Stratification X :=
  { n := 1
    stratum := fun _ ↦ Set.univ
    isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
    isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
    iUnion_stratum_eq_univ := Set.iUnion_const _
    pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
    domain := fun _ ↦ X
    immersion := fun _ ↦ 𝟙 X
    range_immersion := fun _ ↦ Set.range_id' }

private theorem regular_constructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X (Mod.regular (condensedRingObj Λ X)) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX]
  exact ⟨oneStratum X, fun _ ↦ model_regular Λ (𝟙 X)⟩

private theorem zero_constructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X (0 : Mod _ (condensedRingObj Λ X)) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX]
  exact ⟨oneStratum X, fun _ ↦ model_zero Λ (𝟙 X)⟩

set_option maxHeartbeats 800000 in
-- The homology comparison elaborates through the internal module category.
/-- The coefficient sheaf in degree zero has a finite constant model.
Source: rational projective-line unit/counit proof step 5, rank-one scalar model
(blueprint: lem-sf-condensed-verdier-biduality).
Proof: use the one-stratum partition and the identity cover. The scalar model is the
regular coefficient module, with its rank-one finite presentation. Monoidality of
inverse image identifies both pullbacks of this regular module. The single complex
is bounded, has this module as its zeroth cohomology and zero cohomology otherwise. -/
private theorem coefficientUnit_boundedConstructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    constantModelBoundedConstructible Λ X
      ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ X))) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _).symm
      (regular_constructible Λ X)
  · have hz : IsZero ((DerivedCategory.homologyFunctor C n).obj
        ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ X)))) := by
      rcases lt_or_gt_of_ne hn with h | h
      · exact (DerivedCategory.isGE_iff
          ((DerivedCategory.singleFunctor _ 0).obj
            (Mod.regular (condensedRingObj Λ X))) 0).1 inferInstance n h
      · exact (DerivedCategory.isLE_iff
          ((DerivedCategory.singleFunctor _ 0).obj
            (Mod.regular (condensedRingObj Λ X))) 0).1 inferInstance n h
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((isZero_zero _).iso hz) (zero_constructible Λ X)

private theorem condensedVerdier_unit (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    dctfPred Λ X (𝟙_ (moduleDerived Λ X)) := by
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
  refine ⟨(constantModelBoundedConstructible Λ X).prop_of_iso
    (DerivedCategory.singleFunctorObjUnitIso _) (coefficientUnit_boundedConstructible Λ X),
    0, 0, ?_⟩
  intro F
  exact (DerivedCategory.homologyConcentratedIn (C :=
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) 0 0).prop_of_iso
      (λ_ ((DerivedCategory.singleFunctor _ 0).obj F)).symm ⟨inferInstance, inferInstance⟩

/-- Finite discrete coefficients have the same actual constant and continuous ring
objects. The comparison is induced by the constant-function morphism. -/
private theorem condensedVerdier_discreteIso (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    Nonempty (Mon.mk (IntegralModelsEmbedded.discreteObj.{u} A) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} A)) := by
  let J := coherentTopology Profinite.{u}
  let f := Profinite.constantToContinuousRing.{u} A
  have : Presheaf.IsLocallyInjective J f :=
    ⟨fun a b h ↦ Presheaf.equalizerSieve_mem J
      (Profinite.constantToContinuousAb.{u} A) a b h⟩
  have : Presheaf.IsLocallySurjective J f :=
    ⟨fun a ↦ Presheaf.imageSieve_mem J (Profinite.constantToContinuousAb.{u} A) a⟩
  have hf : J.W f := J.W_of_isLocallyBijective f
  have : IsIso ((presheafToSheaf J RingCat.{u + 1}).map f) := (J.W_iff f).mp hf
  have : IsIso (IntegralModelsEmbedded.constantToContinuous.{u} A) := by
    unfold IntegralModelsEmbedded.constantToContinuous
    rw [Adjunction.homEquiv_counit]
    change IsIso (_ ≫ (presheafToSheaf J RingCat.{u + 1}).map f ≫ _)
    infer_instance
  let e := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
    (asIso (IntegralModelsEmbedded.constantToContinuous.{u} A))
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map J
    (IntegralModelsEmbedded.constantToContinuous.{u} A)
  exact ⟨Mon.mkIso' e⟩

/-- A uniformizer quotient is finite by the normalized coefficient comparison,
and the maximal ideal membership of ell makes it ell-power torsion. -/
private theorem condensedVerdier_finiteAdmissible
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ+) :
    IsLocalizingAdmissibleCoefficient ℓ (IntegralModelsEmbedded.discreteObj.{u}
      (PadicAlgCl.integers ℓ E.1 ⧸ (Ideal.span {π}) ^ (n : ℕ))) := by
  let R := PadicAlgCl.integers ℓ E.1
  let I : Ideal R := Ideal.span {π}
  let A := R ⧸ I ^ (n : ℕ)
  have hℓ : (ℓ : R) ∈ I := by
    rw [show I = IsLocalRing.maximalIdeal R from hπ]
    exact PadicAlgCl.natCast_mem_maximalIdeal_integers ℓ E.1
  have : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.1) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.1)).symm.finiteDimensional
  have : Finite (Padic.coefficientExtensionRing ℓ (ULift.{u} E.1) (n : ℕ)) :=
    Padic.finite_coefficientExtensionRing ℓ (ULift.{u} E.1) (n : ℕ) n.pos
  obtain ⟨g⟩ := condensedVerdier_quotient_ringEquiv.{u} ℓ E π hπ (n : ℕ)
  have : Finite A := Finite.of_equiv _ g.symm.toEquiv
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have : IsTopologicalRing A := inferInstance
  have hz : (ℓ ^ (n : ℕ) : A) = 0 := by
    change (Ideal.Quotient.mk (I ^ (n : ℕ))) (ℓ ^ (n : ℕ)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hℓ (n : ℕ))
  refine Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨(n : ℕ), ?_⟩, condensedVerdier_discreteIso A⟩
  intro a
  rw [nsmul_eq_mul, Nat.cast_pow, hz, zero_mul]

omit [IsCommMonObj Λ] in
private theorem condensedVerdier_admissibleIso
    (ℓ : ℕ) [Fact ℓ.Prime]
    {Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Γ]
    (e : Mon.mk Λ ≅ Mon.mk Γ) (hΓ : IsLocalizingAdmissibleCoefficient ℓ Γ) :
    IsLocalizingAdmissibleCoefficient ℓ Λ := by
  rcases hΓ with hA | hZ | hQ | hE | hO | hbar
  · obtain ⟨A, hr, ht, hd, htr, hf, hn, ⟨i⟩⟩ := hA
    exact Or.inl ⟨A, hr, ht, hd, htr, hf, hn, ⟨e ≪≫ i⟩⟩
  · exact Or.inr (Or.inl ⟨e ≪≫ hZ.some⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e ≪≫ hQ.some⟩))
  · obtain ⟨E, ⟨i⟩⟩ := hE
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨e ≪≫ i⟩⟩)))
  · obtain ⟨E, ⟨i⟩⟩ := hO
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨e ≪≫ i⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e ≪≫ hbar.some⟩))))

private theorem condensedVerdier_preserves
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcd : BaseFieldFiniteCD ℓ k) (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom]
    (W : ConstantModelConstructibleFiniteTor Λ T.left) :
    ∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
      dctfPred Λ T.left (((derivedHom Λ T.left).flip.obj W.obj).obj (op K)) := by
  let : T.left.Over (Spec (.of k)) := ⟨T.hom⟩
  have : LocallyOfFiniteType (T.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType T.hom›
  have : QuasiCompact (T.left ↘ Spec (.of k)) := ‹QuasiCompact T.hom›
  have : IsSeparated (T.left ↘ Spec (.of k)) := ‹IsSeparated T.hom›
  intro K hK
  exact (internalHom_stability Λ ℓ k hcd hΛ K W.obj hK W.property).1

private theorem condensedVerdier_adjunction
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcd : BaseFieldFiniteCD ℓ k)
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∃ (h : ∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
        dctfPred Λ (Spec (.of k)) ((condensedVerdierAmbientSupport Λ T).obj K))
      (G : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)) ⥤
        ConstantModelConstructibleFiniteTor Λ T.left)
      (_adj : condensedVerdierSupport Λ T h ⊣ G)
      (N : ConstantModelConstructibleFiniteTor Λ (Spec (.of k))),
      N.obj = 𝟙_ (moduleDerived Λ (Spec (.of k))) := by
  have : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))
  have : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))
  have : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))
  let f := Over.mkIdTerminal.from T
  let A := sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ
  have h : ∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
      dctfPred Λ (Spec (.of k)) ((condensedVerdierAmbientSupport Λ T).obj K) := by
    intro K hK
    exact A.lower_ctf ⟨K, A.source_mem K hK⟩ hK
  refine ⟨h, ctfExceptionalInverseImage Λ ℓ k hcd f hΛ,
    ctfExceptionalAdjunction Λ ℓ k hcd f hΛ,
    ⟨𝟙_ _, condensedVerdier_unit Λ _⟩, rfl⟩

/-- Preservation and invertibility of evaluation give the specified restricted duality;
contravariant exactness is inherited from the native closed structure. -/
private theorem condensedVerdier_formal (X : Scheme.{u}) (W : moduleDerived Λ X)
    (hD : ∀ K : moduleDerived Λ X, dctfPred Λ X K →
      dctfPred Λ X (((derivedHom Λ X).flip.obj W).obj (op K)))
    (hδ : ∀ K : moduleDerived Λ X, dctfPred Λ X K →
      IsIso ((condensedVerdierBiduality Λ X W).app K)) :
    (∃ e : (ConstantModelConstructibleFiniteTor Λ X)ᵒᵖ ≌
        ConstantModelConstructibleFiniteTor Λ X,
      Nonempty (e.functor ⋙ (dctfPred Λ X).ι ≅
        (dctfPred Λ X).ι.op ⋙ (derivedHom Λ X).flip.obj W)) ∧
    ∃ s : ((derivedHom Λ X).flip.obj W).CommShift ℤ,
      ∀ U : Triangle (moduleDerived Λ X)ᵒᵖ,
        dctfPred Λ X U.obj₁.unop → dctfPred Λ X U.obj₂.unop →
        dctfPred Λ X U.obj₃.unop → U ∈ distTriang (moduleDerived Λ X)ᵒᵖ →
        Triangle.mk
          (((derivedHom Λ X).flip.obj W).map U.mor₁)
          (((derivedHom Λ X).flip.obj W).map U.mor₂)
          ((((derivedHom Λ X).flip.obj W).map U.mor₃) ≫
            (s.commShiftIso (1 : ℤ)).hom.app U.obj₁) ∈ distTriang (moduleDerived Λ X) := by
  constructor
  · exact ⟨(dctfPred Λ X).liftDualEquivalence ((derivedHom Λ X).flip.obj W) hD
      (condensedVerdierBiduality Λ X W) hδ, ⟨Iso.refl _⟩⟩
  · obtain ⟨s, hs⟩ := DerivedCategory.nativeInternalHom_contravariant_exact
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) W
    let : ((derivedHom Λ X).flip.obj W).CommShift ℤ := s
    have : ((derivedHom Λ X).flip.obj W).IsTriangulated := hs
    exact ⟨s, fun U _ _ _ hU ↦ ((derivedHom Λ X).flip.obj W).map_distinguished U hU⟩

/-- Verdier biduality on the four actual condensed coefficient categories.
The existential adjunction is the constructible exceptional adjunction of
sk-thm-existence. Its input N is precisely the coefficient unit, and its image
is omega. Duality is the recorded internal Hom into this omega. The restricted
anti-equivalence is identified with that same functor on objects and morphisms;
exactness uses ambient distinguished triangles with all vertices in Dctf.

Source: latest blueprint, sk-thm-pd-verdier-duality, statement, and
 det-pd-biduality-coefficients.proof.md, clauses (i)--(iv)
(blueprint: lem-sf-condensed-verdier-biduality).

Proof:
1. The finite quotient is isomorphic to the normalized spectral quotient, hence
finite; ell belongs to the uniformizer ideal, so ell^n kills it. Its discrete
constant and continuous coefficient objects are canonically isomorphic. The other
three coefficient rings are explicitly admissible.
2. The coefficient unit is a one-stratum constant regular module of rank one,
concentrated in degree zero, with Tor interval [0,0]. The six-operations adjunction
restricts compact support to the prescribed constructible finite-Tor domain and
supplies its right adjoint G. Take N to be this unit.
3. Internal-Hom stability proves that RHom(-,G N) preserves this domain.
4. For finite coefficients, condensedVerdier_finite_evaluation transports
geometric etale evaluation through the normalized finite comparison and reflects
it by conservative geometric pullback. For the other coefficient alternatives,
condensedVerdier_coefficient_passage applies the integral completeness, finite
reduction, rational generation and finite descent arguments of clauses (ii)--(iv).
5. ObjectProperty.liftDualEquivalence restricts this very dual functor, using its
canonical evaluation natural transformation. The inclusion comparison is the
identity. Native contravariant internal-Hom exactness supplies the coherent
reversed shifts and maps the indicated ambient triangles to distinguished ones.
-/
theorem condensed_verdier_biduality
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (_hk : Finite k ∨ IsAlgClosed k) (_hcd : BaseFieldFiniteCD ℓ k)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ+) (_hΛ :
      Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralModelsEmbedded.discreteObj
        (PadicAlgCl.integers ℓ E.1 ⧸ (Ideal.span {π}) ^ (n : ℕ)))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom] :
    ∃ (h : ∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
        dctfPred Λ (Spec (.of k))
          ((condensedVerdierAmbientSupport Λ T).obj K))
      (G : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)) ⥤
        ConstantModelConstructibleFiniteTor Λ T.left)
      (_adj : condensedVerdierSupport Λ T h ⊣ G)
      (N : ConstantModelConstructibleFiniteTor Λ (Spec (.of k))),
      N.obj = 𝟙_ (moduleDerived Λ (Spec (.of k))) ∧
      (∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
        dctfPred Λ T.left (((derivedHom Λ T.left).flip.obj (G.obj N).obj).obj (op K))) ∧
      (∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
        IsIso ((condensedVerdierBiduality Λ T.left (G.obj N).obj).app K)) ∧
      (∃ e : (ConstantModelConstructibleFiniteTor Λ T.left)ᵒᵖ ≌
          ConstantModelConstructibleFiniteTor Λ T.left,
        Nonempty (e.functor ⋙ (dctfPred Λ T.left).ι ≅
          (dctfPred Λ T.left).ι.op ⋙ (derivedHom Λ T.left).flip.obj (G.obj N).obj)) ∧
      ∃ s : ((derivedHom Λ T.left).flip.obj (G.obj N).obj).CommShift ℤ,
        ∀ U : Triangle (moduleDerived Λ T.left)ᵒᵖ,
          dctfPred Λ T.left U.obj₁.unop → dctfPred Λ T.left U.obj₂.unop →
          dctfPred Λ T.left U.obj₃.unop → U ∈ distTriang (moduleDerived Λ T.left)ᵒᵖ →
          Triangle.mk
            (((derivedHom Λ T.left).flip.obj (G.obj N).obj).map U.mor₁)
            (((derivedHom Λ T.left).flip.obj (G.obj N).obj).map U.mor₂)
            ((((derivedHom Λ T.left).flip.obj (G.obj N).obj).map U.mor₃) ≫
              (s.commShiftIso (1 : ℤ)).hom.app U.obj₁) ∈ distTriang (moduleDerived Λ T.left) := by
  have hadm : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases _hΛ with hfinite | hO | hE | hbar
    · obtain ⟨e⟩ := hfinite
      exact condensedVerdier_admissibleIso Λ ℓ e
        (condensedVerdier_finiteAdmissible ℓ E π _hπ n)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hO⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hE⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbar))))
  obtain ⟨h, G, adj, N, hN⟩ := condensedVerdier_adjunction Λ ℓ k _hcd T hadm
  have hD := condensedVerdier_preserves Λ ℓ k _hcd hadm T (G.obj N)
  have hδ : ∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
      IsIso ((condensedVerdierBiduality Λ T.left (G.obj N).obj).app K) := by
    have : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))
    have : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))
    have : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))
    have adj' : ctfLowerShriek Λ ℓ k _hcd (Over.mkIdTerminal.from T) hadm ⊣ G := adj
    rcases _hΛ with hfinite | hnonfinite
    · exact condensedVerdier_finite_evaluation Λ ℓ k _hk _hcd E π _hπ n
        hfinite hadm T G adj' N hN
    · exact condensedVerdier_coefficient_passage Λ ℓ k _hk _hcd E
        hnonfinite hadm T G adj' N hN
  obtain ⟨he, hs⟩ := condensedVerdier_formal Λ T.left (G.obj N).obj hD hδ
  exact ⟨h, G, adj, N, hN, hD, hδ, he, hs⟩

end AlgebraicGeometry.ProEtale.CondensedRing
