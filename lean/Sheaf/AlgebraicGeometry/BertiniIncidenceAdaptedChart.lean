/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Sheaf.FieldTheory.BertiniFieldExtension
public import Sheaf.AlgebraicGeometry.BertiniPolynomialResidueArrow
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg
import WeilConjectures.RingTheory.KrullDimension.FiniteType
import Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility
import Sheaf.AlgebraicGeometry.BertiniIncidenceNaturality
import Sheaf.AlgebraicGeometry.BertiniBasisCoordinates
import Sheaf.AlgebraicGeometry.BertiniAffineIncidenceChart
import Sheaf.AlgebraicGeometry.BertiniIncidenceElimination
import Sheaf.AlgebraicGeometry.BertiniAffineIncidenceIrreducible
import Sheaf.AlgebraicGeometry.BertiniUniversalZeroSection
import Mathlib.Topology.Sets.OpenCover
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-! Intermediate steps in the incidence proof of Stacks Project, Tag 0G4F. -/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry

private theorem exists_affine_generator_avoiding_zeroLocus
    {Y : Scheme.{u}} (L : Y.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    {x : Y} (hx : x ∉ (Scheme.Modules.homOfGlobalSection L s).zeroLocus.support) :
    ∃ U : Y.affineOpens, x ∈ U.1 ∧
      Scheme.Modules.IsFreeGenerator
        (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s) := by
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  obtain ⟨U, hU, hxU, hUD⟩ := exists_isAffineOpen_mem_and_subset
    (U := (Scheme.Modules.homOfGlobalSection L s).zeroLocus.support.compl) hx
  refine ⟨⟨U, hU⟩, hxU, ?_⟩
  have hgen := Scheme.Modules.isFreeGenerator_app_one_of_le
    (Scheme.Modules.homOfGlobalSection L s) hUD
  change Scheme.Modules.IsFreeGenerator
    ((Scheme.Modules.homOfGlobalSection L s).app U (1 : Γ(Y, U))) at hgen
  simpa only [Scheme.Modules.homOfGlobalSection_app_one] using hgen

private theorem affine_preimage_section_zeroLocus
    {Y : Scheme.{u}} (L : Y.Modules) [L.IsInvertible]
    (U : Y.affineOpens) {e : Γ(L, U.1)} (he : Scheme.Modules.IsFreeGenerator e)
    (s : Γ(L, ⊤)) :
    U.2.fromSpec ⁻¹'
        ((Scheme.Modules.homOfGlobalSection L s).zeroLocus.support : Set Y) =
      PrimeSpectrum.zeroLocus
        ({he.coeff (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s)} : Set Γ(Y, U.1)) := by
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  have : SheafOfModules.IsInvertible.{u, u, u} (Scheme.Modules.unit Y) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ Y.Modules)
  have hlocal := (Scheme.Modules.homOfGlobalSection L s).ideal_zeroLocus U
    (Scheme.Modules.isFreeGenerator_one U.1) he
    (b := he.coeff (L.presheaf.map (homOfLE le_top).op s)) (by
      rw [Scheme.Modules.homOfGlobalSection_app_one]
      exact (he.coeff_smul _).symm)
  have hpre : U.2.fromSpec ⁻¹'
        ((Scheme.Modules.homOfGlobalSection L s).zeroLocus.support : Set Y) =
      PrimeSpectrum.zeroLocus
        (((Scheme.Modules.homOfGlobalSection L s).zeroLocus.ideal U : Ideal Γ(Y, U.1)) :
          Set Γ(Y, U.1)) := by
    apply U.2.fromSpec.isOpenEmbedding.injective.image_injective
    rw [Set.image_preimage_eq_inter_range, IsAffineOpen.range_fromSpec,
      Scheme.IdealSheafData.coe_support_inter, IsAffineOpen.fromSpec_image_zeroLocus]
  rw [hpre, hlocal, PrimeSpectrum.zeroLocus_span]

private theorem restrict_maximal_irreducible_closed
    {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (f : X → Z) (hf : Topology.IsOpenEmbedding f)
    {S : Set Z} (hS : IsClosed S) (W : TopologicalSpace.IrreducibleCloseds Z)
    (hW : Maximal (fun T : TopologicalSpace.IrreducibleCloseds Z ↦
      (T : Set Z) ⊆ S) W) (hne : (f ⁻¹' (W : Set Z)).Nonempty) :
    ∃ U : TopologicalSpace.IrreducibleCloseds X,
      (U : Set X) = f ⁻¹' (W : Set Z) ∧
      Maximal (fun T : TopologicalSpace.IrreducibleCloseds X ↦
        (T : Set X) ⊆ f ⁻¹' S) U ∧ Order.coheight U = Order.coheight W := by
  let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf
  let U := e.symm ⟨W, hne⟩
  have hpre : (U : Set X) = f ⁻¹' (W : Set Z) := rfl
  have hmap : TopologicalSpace.IrreducibleCloseds.map f hf.continuous U = W :=
    congrArg Subtype.val (e.apply_symm_apply ⟨W, hne⟩)
  refine ⟨U, hpre, ⟨?_, ?_⟩, ?_⟩
  · change (U : Set X) ⊆ f ⁻¹' S
    rw [hpre]
    exact Set.preimage_mono hW.1
  · intro T hT hUT
    have hTS : (TopologicalSpace.IrreducibleCloseds.map f hf.continuous T : Set Z)
        ⊆ S := closure_minimal (Set.image_subset_iff.mpr hT) hS
    have hTU : TopologicalSpace.IrreducibleCloseds.map f hf.continuous T ≤
        TopologicalSpace.IrreducibleCloseds.map f hf.continuous U := by
      rw [hmap]
      exact hW.2 hTS (hmap ▸
        TopologicalSpace.IrreducibleCloseds.map_mono hf.continuous hUT)
    change e T ≤ e U at hTU
    exact e.le_iff_le.mp hTU
  · rw [← hf.coheight_map U, hmap]

private theorem prime_of_maximal_irreducible_zeroLocus
    (R : Type u) [CommRing R] (I : Ideal R)
    (W : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))
    (hW : Maximal (fun T : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) ↦
      (T : Set (PrimeSpectrum R)) ⊆ PrimeSpectrum.zeroLocus (I : Set R)) W) :
    ∃ p : Ideal R, p ∈ I.minimalPrimes ∧ p.height = Order.coheight W ∧
      (W : Set (PrimeSpectrum R)) = PrimeSpectrum.zeroLocus (p : Set R) := by
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds R
  let p := e.symm (OrderDual.toDual W)
  have he : e p = OrderDual.toDual W := e.apply_symm_apply _
  have hc : PrimeSpectrum.zeroLocus (p.asIdeal : Set R) =
      (W : Set (PrimeSpectrum R)) := by
    have h := congrArg (fun T :
        (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ ↦
      ((OrderDual.ofDual T : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R)) :
        Set (PrimeSpectrum R))) he
    change closure ({p} : Set (PrimeSpectrum R)) = (W : Set (PrimeSpectrum R)) at h
    simpa only [PrimeSpectrum.closure_singleton] using h
  have hIp : I ≤ p.asIdeal := by
    apply hW.1
    rw [← hc]
    change p.asIdeal ≤ p.asIdeal
    exact le_rfl
  have hmin : p.asIdeal ∈ I.minimalPrimes := by
    refine ⟨⟨p.isPrime, hIp⟩, ?_⟩
    intro q hq hqp
    let Q : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) :=
      ⟨PrimeSpectrum.zeroLocus (q : Set R),
        (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical q hq.1.isRadical).mpr hq.1,
        PrimeSpectrum.isClosed_zeroLocus _⟩
    have hPQ : W ≤ Q := by
      change (W : Set (PrimeSpectrum R)) ⊆ PrimeSpectrum.zeroLocus (q : Set R)
      rw [← hc]
      exact PrimeSpectrum.zeroLocus_anti_mono hqp
    have hQW : Q ≤ W := hW.2 (PrimeSpectrum.zeroLocus_anti_mono hq.2) hPQ
    have hmem : (⟨q, hq.1⟩ : PrimeSpectrum R) ∈ (W : Set (PrimeSpectrum R)) :=
      hQW (by change (q : Set R) ⊆ q; exact Set.Subset.rfl)
    rw [← hc] at hmem
    exact hmem
  refine ⟨p.asIdeal, hmin, ?_, hc.symm⟩
  rw [PrimeSpectrum.height_eq_orderHeight, ← Order.height_orderIso e p, he]
  rfl

private theorem map_maximal_irreducible_closed
    {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (f : X → Z) (hf : Topology.IsOpenEmbedding f)
    {S : Set Z} (hS : IsClosed S) (W : TopologicalSpace.IrreducibleCloseds X)
    (hW : Maximal (fun T : TopologicalSpace.IrreducibleCloseds X ↦
      (T : Set X) ⊆ f ⁻¹' S) W) :
    Maximal (fun T : TopologicalSpace.IrreducibleCloseds Z ↦ (T : Set Z) ⊆ S)
      (TopologicalSpace.IrreducibleCloseds.map f hf.continuous W) := by
  let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf
  refine ⟨closure_minimal (Set.image_subset_iff.mpr hW.1) hS, ?_⟩
  intro T hT hWT
  have hne : (f ⁻¹' (T : Set Z)).Nonempty := by
    obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
    exact ⟨x, hWT (subset_closure ⟨x, hx, rfl⟩)⟩
  let U := e.symm ⟨T, hne⟩
  have hWU : W ≤ U := by
    intro x hx
    exact hWT (subset_closure ⟨x, hx, rfl⟩)
  have hUW : U ≤ W := hW.2 (fun x hx ↦ hT hx) hWU
  have hh := e.monotone hUW
  change (e U).val ≤ (e W).val at hh
  have hU : (e U).val = T := congrArg Subtype.val (e.apply_symm_apply ⟨T, hne⟩)
  rw [hU] at hh
  exact hh

private theorem component_of_maximal_irreducible_closed
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClosed S)
    (W : TopologicalSpace.IrreducibleCloseds X)
    (hW : Maximal (fun T : TopologicalSpace.IrreducibleCloseds X ↦ (T : Set X) ⊆ S) W) :
    ∃ C : Set S, C ∈ irreducibleComponents S ∧
      topologicalKrullDim C = topologicalKrullDim (W : Set X) := by
  let C : Set S := Subtype.val ⁻¹' (W : Set X)
  have hrange : (W : Set X) ⊆ Set.range (Subtype.val : S → X) := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hW.1
  let e := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hrange
  have hWC : IrreducibleSpace (W : Set X) :=
    isIrreducible_iff_irreducibleSpace.mp W.isIrreducible
  have hC : IsIrreducible C := isIrreducible_iff_irreducibleSpace.mpr
    (e.irreducibleSpace_iff.mpr hWC)
  refine ⟨C, ?_, e.isHomeomorph.topologicalKrullDim_eq _⟩
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨W.isClosed.preimage continuous_subtype_val, hC⟩, ?_⟩
  intro D hD hCD
  let T : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Subtype.val '' D, hD.2.image Subtype.val continuous_subtype_val.continuousOn,
      hS.isClosedEmbedding_subtypeVal.isClosedMap D hD.1⟩
  have hWT : W ≤ T := by
    intro x hx
    exact ⟨⟨x, hW.1 hx⟩, hCD hx, rfl⟩
  have hTW : T ≤ W := hW.2 (by rintro _ ⟨x, _, rfl⟩; exact x.property) hWT
  intro x hx
  exact hTW ⟨x, hx, rfl⟩

private theorem independent_pair_of_minimalPrime_height_two
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
    (f g : A) (p : Ideal A) (hp : p ∈ (Ideal.span ({f, g} : Set A)).minimalPrimes)
    (hheight : p.height = 2) : LinearIndependent k ![f, g] := by
  have hnot : ¬ (Ideal.span ({f, g} : Set A)).IsPrincipal := by
    intro h
    have ht := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span ({f, g} : Set A)) p hp
    rw [hheight] at ht
    norm_num at ht
  apply linearIndependent_fin2.mpr
  constructor
  · change g ≠ 0
    intro hg
    apply hnot
    have he : Ideal.span ({f, g} : Set A) = Ideal.span ({f} : Set A) :=
      Ideal.span_pair_eq_span_left_iff_dvd.mpr (hg ▸ dvd_zero f)
    rw [he]
    infer_instance
  · intro t ht
    change t • g = f at ht
    apply hnot
    have hd : g ∣ f := ⟨algebraMap k A t, by rw [← ht, Algebra.smul_def, mul_comm]⟩
    have he : Ideal.span ({f, g} : Set A) = Ideal.span ({g} : Set A) :=
      Ideal.span_pair_eq_span_right_iff_dvd.mpr hd
    rw [he]
    infer_instance

private theorem independent_triple_of_minimalPrime_height_two
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
    {V : Type v} [AddCommGroup V] [Module k V] (a : V →ₗ[k] A)
    (v₁ v₂ v₃ : V) (ha₁ : a v₁ = 1) (p : Ideal A)
    (hp : p ∈ (Ideal.span ({a v₂, a v₃} : Set A)).minimalPrimes)
    (hheight : p.height = 2) : LinearIndependent k ![v₁, v₂, v₃] := by
  have h23 := independent_pair_of_minimalPrime_height_two k A (a v₂) (a v₃) p hp hheight
  have hv23 : LinearIndependent k ![v₂, v₃] := by
    apply LinearIndependent.of_comp a
    convert h23 using 1
    ext j
    fin_cases j <;> rfl
  apply linearIndependent_finCons.mpr
  refine ⟨hv23, ?_⟩
  intro hv₁
  have hspan : Submodule.span k (Set.range ![v₂, v₃]) ≤
      (p.restrictScalars k).comap a := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change a (![v₂, v₃] j) ∈ p
    fin_cases j
    · exact hp.le (Ideal.subset_span (Set.mem_insert _ _))
    · exact hp.le (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hmem : a v₁ ∈ p := hspan hv₁
  rw [ha₁] at hmem
  exact hp.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p hmem isUnit_one)

private theorem sumExtend_inl
    (k : Type u) [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    {ι : Type*} {v : ι → V} (hv : LinearIndependent k v) (i : ι) :
    Module.Basis.sumExtend hv (Sum.inl i) = v i := by
  simp [Module.Basis.sumExtend,
    Equiv.sumCongr, Equiv.Set.sumDiffSubset_apply_inl]

private theorem exists_basis_extending_triple
    (k : Type u) [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (v : Fin 3 → V) (hv : LinearIndependent k v) :
    ∃ (n : ℕ) (hn : 2 ≤ n) (b : Module.Basis (Fin (n + 1)) k V),
      ∀ i : Fin 3, b ⟨i.val, by omega⟩ = v i := by
  classical
  let J := Module.Basis.sumExtendIndex hv
  let d := Module.Basis.sumExtend hv
  have : Finite (Fin 3 ⊕ J) := Module.Finite.finite_basis d
  have : Finite J := Finite.of_injective (Sum.inr : J → Fin 3 ⊕ J) Sum.inr_injective
  let := Fintype.ofFinite J
  let n := Fintype.card J + 2
  have hn : 2 ≤ n := by dsimp [n]; omega
  let e : Fin 3 ⊕ J ≃ Fin (n + 1) :=
    (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin J)).trans
      (finSumFinEquiv.trans (finCongr (by dsimp [n]; omega)))
  refine ⟨n, hn, d.reindex e, ?_⟩
  intro i
  have hei : e (Sum.inl i) = ⟨i.val, by omega⟩ := by
    apply Fin.ext
    rfl
  rw [← hei, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  exact sumExtend_inl k hv i

private theorem finiteType_domain_quotient_dimension
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [IsDomain A] (p : Ideal A) [p.IsPrime] :
    ringKrullDim (A ⧸ p) + (p.height : WithBot ℕ∞) = ringKrullDim A := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let : (Spec (.of A)).Over (Spec (.of k)) := ⟨f⟩
  have : LocallyOfFiniteType f := HasRingHomProperty.Spec_iff.mpr
    ((RingHom.finiteType_algebraMap).mpr inferInstance)
  have : LocallyOfFiniteType ((Spec (.of A)) ↘ Spec (.of k)) := by
    change LocallyOfFiniteType f
    infer_instance
  obtain ⟨d, r, hd, hr, ht⟩ :=
    topologicalKrullDimAt_eq_ringKrullDim_add_trdeg (k := k) p
  obtain ⟨m, hm, htr, _⟩ :=
    finiteType_domain_ringKrullDim_eq_trdeg (k := k) (S := A ⧸ p)
  have hres : Algebra.trdeg k p.ResidueField = (m : Cardinal) := by
    let e := (FractionRing.algEquiv (A ⧸ p) p.ResidueField).restrictScalars k
    rw [← e.trdeg_eq]
    exact htr
  have hmr : m = r := by exact_mod_cast hres.symm.trans hr
  have htop : topologicalKrullDimAt (⟨p, inferInstance⟩ : Spec (.of A)) =
      ringKrullDim A := by
    rw [(dimension_locally_algebraic (k := k) (Spec (.of A))).2 _]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A
  rw [hm, ← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hd,
    ← htop, ht, hmr]
  simp only [Nat.cast_add, add_comm]

private theorem geomIrred_comp_universalHomeomorphism
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ Z)
    [IsUniversalHomeomorphism i] [GeometricallyIrreducible f] :
    GeometricallyIrreducible (i ≫ f) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  have : IrreducibleSpace ↥(pullback f x) :=
    (geometrically_iff_of_isClosedUnderIsomorphisms.mp
      (GeometricallyIrreducible.geometrically_irreducibleSpace (f := f))) K x
  let e := pullbackRightPullbackFstIso f x i
  rw [← e.hom.homeomorph.irreducibleSpace_iff]
  exact (IsUniversalHomeomorphism.homeomorph
    (pullback.snd i (pullback.fst f x))).irreducibleSpace_iff.mpr inferInstance

private theorem geomIrred_fractionRing
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k A)))] :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing A)))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let : (Spec (.of A)).Over (Spec (.of k)) := ⟨f⟩
  let η : Spec (.of A) := (⊥ : PrimeSpectrum A)
  have hη : IsGenericPoint η (Set.univ : Set (Spec (.of A))) := by
    change closure ({(⊥ : PrimeSpectrum A)} : Set (PrimeSpectrum A)) = Set.univ
    rw [PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  have hf := (geometricallyIrreducible_iff_genericResidueField k
    (Spec (.of A)) η hη).mp (inferInstance : GeometricallyIrreducible f)
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField] at hf
  have hr : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap A (⊥ : Ideal A).ResidueField)) ≫ f) :=
    (MorphismProperty.cancel_left_of_respectsIso
      @GeometricallyIrreducible _ _).mp hf
  let e := FractionRing.algEquiv A (⊥ : Ideal A).ResidueField
  have he : Spec.map e.toCommRingCatIso.inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (⊥ : Ideal A).ResidueField)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing A))) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    change e.symm (algebraMap A _ (algebraMap k A t)) = _
    rw [e.symm.commutes]
    exact (IsScalarTower.algebraMap_apply k A (FractionRing A) t).symm
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso
    @GeometricallyIrreducible _ _).mpr hr

set_option backward.isDefEq.respectTransparency false in
private theorem coefficient_minimalPrime_height
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    {Y : Scheme.{u}} (i : Spec (.of A) ⟶ Y) (hi : Topology.IsOpenEmbedding i)
    (L : Y.Modules) {V : Type v} [AddCommGroup V] [Module k V]
    (ψ : V → Γ(L, ⊤)) (a : V →ₗ[k] A)
    (hZ : ∀ v, i ⁻¹' ((Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.support :
      Set Y) = PrimeSpectrum.zeroLocus ({a v} : Set A))
    (hbase : ∀ B : TopologicalSpace.IrreducibleCloseds Y,
      Maximal (fun T : TopologicalSpace.IrreducibleCloseds Y ↦ (T : Set Y) ⊆
        ⋂ v : V, ((Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.support : Set Y)) B →
        2 ≤ Order.coheight B)
    {I : Type*} [Finite I] (b : Module.Basis I k V) (p : Ideal A)
    (hp : p ∈ (Ideal.span (Set.range (fun j ↦ a (b j)))).minimalPrimes) :
    (2 : ℕ∞) ≤ p.height := by
  classical
  let := Fintype.ofFinite I
  let S : Set Y := ⋂ v : V,
    ((Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.support : Set Y)
  let J := Ideal.span (Set.range (fun j ↦ a (b j)))
  have hS : IsClosed S := isClosed_iInter fun v ↦
    (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.support.isClosed
  have hpre : i ⁻¹' S = PrimeSpectrum.zeroLocus (J : Set A) := by
    dsimp only [S]
    rw [Set.preimage_iInter]
    simp_rw [hZ]
    apply Set.ext
    intro q
    simp only [Set.mem_iInter, PrimeSpectrum.zeroLocus,
      Set.singleton_subset_iff]
    change (∀ v, a v ∈ q.asIdeal) ↔ J ≤ q.asIdeal
    rw [Ideal.span_le]
    simp only [Set.range_subset_iff]
    refine ⟨fun h j ↦ h (b j), fun h v ↦ ?_⟩
    rw [← b.sum_repr v, map_sum]
    apply q.asIdeal.sum_mem
    intro j _
    rw [a.map_smul, Algebra.smul_def]
    exact q.asIdeal.mul_mem_left _ (h j)
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds A
  let point : PrimeSpectrum A := ⟨p, hp.isPrime⟩
  let W := OrderDual.ofDual (e point)
  have hWV : (W : Set (PrimeSpectrum A)) = PrimeSpectrum.zeroLocus (p : Set A) :=
    PrimeSpectrum.closure_singleton point
  have hheight : p.height = Order.coheight W := by
    change point.asIdeal.height = Order.coheight W
    rw [PrimeSpectrum.height_eq_orderHeight, ← Order.height_orderIso e point]
    rfl
  have hWmax : Maximal (fun T : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A) ↦
      (T : Set (PrimeSpectrum A)) ⊆ i ⁻¹' S) W := by
    rw [hpre]
    refine ⟨?_, ?_⟩
    · change (W : Set (PrimeSpectrum A)) ⊆ PrimeSpectrum.zeroLocus (J : Set A)
      rw [hWV]
      exact PrimeSpectrum.zeroLocus_anti_mono hp.le
    · intro T hT hWT
      let q := e.symm (OrderDual.toDual T)
      have hq : e q = OrderDual.toDual T := e.apply_symm_apply _
      have hqV : (T : Set (PrimeSpectrum A)) =
          PrimeSpectrum.zeroLocus (q.asIdeal : Set A) := by
        have hh := congrArg (fun Z :
            (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ ↦
          ((OrderDual.ofDual Z : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A)) :
            Set (PrimeSpectrum A))) hq
        change closure ({q} : Set (PrimeSpectrum A)) = (T : Set (PrimeSpectrum A)) at hh
        rw [PrimeSpectrum.closure_singleton] at hh
        exact hh.symm
      have hqT : q ∈ (T : Set (PrimeSpectrum A)) := by
        rw [hqV]
        change q.asIdeal ≤ q.asIdeal
        exact le_rfl
      have hJq : J ≤ q.asIdeal := hT hqT
      have hqp : q.asIdeal ≤ p := by
        have hpW : point ∈ (W : Set (PrimeSpectrum A)) := by
          rw [hWV]
          change p ≤ p
          exact le_rfl
        have hh := hWT hpW
        change point ∈ (T : Set (PrimeSpectrum A)) at hh
        rw [hqV] at hh
        exact hh
      have hpq : p ≤ q.asIdeal := hp.2 ⟨q.isPrime, hJq⟩ hqp
      change (T : Set (PrimeSpectrum A)) ⊆ (W : Set (PrimeSpectrum A))
      rw [hqV, hWV]
      exact PrimeSpectrum.zeroLocus_anti_mono hpq
  have hB := map_maximal_irreducible_closed i hi hS W hWmax
  have hd := hbase (TopologicalSpace.IrreducibleCloseds.map i hi.continuous W) hB
  rw [hi.coheight_map W, ← hheight] at hd
  exact hd

private theorem sectionCoefficient_scalar
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    {Y : Scheme.{u}} [Y.Over (Spec (.of k))] (i : Spec (.of A) ⟶ Y)
    (hi : i ≫ Y ↘ Spec (.of k) = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (t : k) :
    (Scheme.ΓSpecIso (.of A)).hom
      (i.appTop (Scheme.globalSectionsRingHom k (X := Y) t)) = algebraMap k A t := by
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫
      (Y ↘ Spec (.of k)).appTop ≫ i.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom =
        CommRingCat.ofHom (algebraMap k A) := by
    rw [← Category.assoc (Y ↘ Spec (.of k)).appTop,
      ← Scheme.Hom.comp_appTop, hi, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  exact congrArg (fun f ↦ f.hom t) h

private noncomputable def sectionCoefficientLinearMap
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    {Y : Scheme.{u}} [Y.Over (Spec (.of k))] (i : Spec (.of A) ⟶ Y)
    (hi : i ≫ Y ↘ Spec (.of k) = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (L : Y.Modules) {e : Γ((Scheme.Modules.tensorPullback i).obj L, ⊤)}
    (he : Scheme.Modules.IsFreeGenerator e)
    {V : Type v} [AddCommGroup V] [Module k V] :
    letI : Module k Γ(L, ⊤) :=
      Module.compHom Γ(L, ⊤) (Scheme.globalSectionsRingHom k (X := Y))
    (V →ₗ[k] Γ(L, ⊤)) → (V →ₗ[k] A) := by
  let : Module k Γ(L, ⊤) :=
    Module.compHom Γ(L, ⊤) (Scheme.globalSectionsRingHom k (X := Y))
  intro ψ
  exact
    { toFun := fun v ↦ (Scheme.ΓSpecIso (.of A)).hom
        (he.coeff (Scheme.Modules.tensorSectionsUnit i L (ψ v)))
      map_add' := fun v w ↦ by rw [ψ.map_add, map_add, he.coeff_add, map_add]
      map_smul' := fun t v ↦ by
        rw [ψ.map_smul]
        change (Scheme.ΓSpecIso (.of A)).hom (he.coeff
          (Scheme.Modules.tensorSectionsUnit i L
            (Scheme.globalSectionsRingHom k (X := Y) t • ψ v))) = _
        rw [bertiniTensorSectionsUnit_smul, he.coeff_smul_left, map_mul,
          sectionCoefficient_scalar k A i hi, Algebra.smul_def]
        rfl }

private theorem universalHomeomorphism_universallyOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f] : UniversallyOpen f := by
  constructor
  intro X' Y' i₁ i₂ f' hp
  exact (isUniversalHomeomorphism_le_universally_isHomeomorph _ _ f inferInstance
    i₁ i₂ f' hp).isOpenMap

private theorem exists_reduced_affine_trivialization
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [IrreducibleSpace Y]
    (L : Y.Modules) [L.IsInvertible] (U : Y.affineOpens) (hne : (U.1 : Set Y).Nonempty)
    {e : Γ(L, U.1)} (hgen : Scheme.Modules.IsFreeGenerator e) :
    ∃ (A : CommRingCat.{u}) (a : Algebra k A),
      letI := a
      ∃ (hft : Algebra.FiniteType k A) (hdom : IsDomain A),
        letI := hft
        letI := hdom
        ∃ i : Spec A ⟶ Y,
          Topology.IsOpenEmbedding i ∧ UniversallyOpen i ∧ UniversallyInjective i ∧
          SurjectiveOnStalks i ∧ i ≫ Y ↘ Spec (.of k) =
            Spec.map (CommRingCat.ofHom (algebraMap k A)) ∧
          Set.range i = (U.1 : Set Y) ∧
          ∃ (e' : Γ((Scheme.Modules.tensorPullback i).obj L, ⊤))
            (he' : Scheme.Modules.IsFreeGenerator e'),
            ∀ t : Γ(L, ⊤),
              i ⁻¹' ((Scheme.Modules.homOfGlobalSection L t).zeroLocus.support : Set Y) =
                PrimeSpectrum.zeroLocus ({(Scheme.ΓSpecIso A).hom
                  (he'.coeff (Scheme.Modules.tensorSectionsUnit i L t))} : Set A) := by
  classical
  obtain ⟨x, hxU⟩ := hne
  let R := Γ(Y, U.1)
  let φ : k →+* R := ((Y ↘ Spec (.of k)).appLE ⊤ U.1 (by simp)).hom.comp
    (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Algebra k R := φ.toAlgebra
  have hftR : Algebra.FiniteType k R :=
    ((Y ↘ Spec (.of k)).finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  have hneR : Nonempty (Spec (.of R)) := by
    obtain ⟨p, hp⟩ := (IsAffineOpen.range_fromSpec U.2).ge hxU
    exact ⟨p⟩
  have hIR : IrreducibleSpace (Spec (.of R)) := U.2.fromSpec.isOpenEmbedding.irreducibleSpace
  have hnil : (nilradical R).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hIR
  let A := R ⧸ nilradical R
  have : (nilradical R).IsPrime := hnil
  have hdom : IsDomain A := inferInstance
  have hftA : Algebra.FiniteType k A := inferInstance
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let ρ : Spec (.of A) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical R)))
  have hρ : IsHomeomorph ρ := by
    change IsHomeomorph (PrimeSpectrum.comap (Ideal.Quotient.mk (nilradical R)))
    exact isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨(PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
        Ideal.Quotient.mk_surjective).isEmbedding,
        (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical le_rfl).2⟩
  have hρclosed : IsClosedImmersion ρ := inferInstance
  have hρsurj : Surjective ρ := ⟨hρ.surjective⟩
  have hρuniv : IsUniversalHomeomorphism ρ := inferInstance
  have hUover : U.2.fromSpec ≫ Y ↘ Spec (.of k) =
      Spec.map (CommRingCat.ofHom φ) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec (Y ↘ Spec (.of k))
      (isAffineOpen_top _) U.2 (by simp), IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  let i : Spec (.of A) ⟶ Y := ρ ≫ U.2.fromSpec
  have hiover : i ≫ Y ↘ Spec (.of k) =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    dsimp only [i]
    rw [Category.assoc, hUover, ← Spec.map_comp]
    rfl
  have hiU : ⊤ ≤ i ⁻¹ᵁ U.1 := by
    change ⊤ ≤ ρ ⁻¹ᵁ (U.2.fromSpec ⁻¹ᵁ U.1)
    rw [U.2.fromSpec_preimage_self, ρ.preimage_top]
  have hiapp : i.appLE U.1 ⊤ hiU =
      CommRingCat.ofHom (Ideal.Quotient.mk (nilradical R)) ≫
        (Scheme.ΓSpecIso (.of A)).inv := by
    dsimp only [i]
    rw [Scheme.Hom.comp_appLE, U.2.fromSpec_app_self, Category.assoc,
      Scheme.Hom.map_appLE]
    change (Scheme.ΓSpecIso (.of R)).inv ≫ ρ.appLE ⊤ ⊤ _ = _
    have he : ρ.appLE ⊤ ⊤ (by simp) = ρ.appTop := by
      convert! ρ.appLE_eq_app (U := ⊤) using 1
    rw [he]
    exact (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical R)))).symm
  have hi : Topology.IsOpenEmbedding i :=
    U.2.fromSpec.isOpenEmbedding.comp hρ.isOpenEmbedding
  have hρopen : UniversallyOpen ρ := universalHomeomorphism_universallyOpen ρ
  have hiopen : UniversallyOpen i := by dsimp only [i]; infer_instance
  have hiinj : UniversallyInjective i := by dsimp only [i]; infer_instance
  have hiS : SurjectiveOnStalks i := by dsimp only [i]; infer_instance
  have hirange : Set.range i = (U.1 : Set Y) := by
    change Set.range (U.2.fromSpec ∘ ρ) = _
    rw [Set.range_comp, hρ.surjective.range_eq, Set.image_univ,
      IsAffineOpen.range_fromSpec]
  obtain ⟨e', he', hc⟩ := exists_bertiniTensorLocalGenerator i L hiU hgen
  refine ⟨.of A, inferInstance, hftA, hdom, i, hi, hiopen, hiinj, hiS,
    hiover, hirange, e', he', ?_⟩
  intro t
  have hcoeff : (Scheme.ΓSpecIso (.of A)).hom
      (he'.coeff (Scheme.Modules.tensorSectionsUnit i L t)) =
      Ideal.Quotient.mk (nilradical R)
        (hgen.coeff (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op t)) := by
    rw [hc, hiapp]
    exact Iso.inv_hom_id_apply _ _
  rw [hcoeff]
  change ρ ⁻¹' (U.2.fromSpec ⁻¹'
    ((Scheme.Modules.homOfGlobalSection L t).zeroLocus.support : Set Y)) = _
  rw [affine_preimage_section_zeroLocus L U hgen]
  change (PrimeSpectrum.comap (Ideal.Quotient.mk (nilradical R))) ⁻¹' _ = _
  rw [PrimeSpectrum.preimage_comap_zeroLocus]
  simp only [Set.image_singleton]

private theorem range_bertiniIncidenceBaseChange
    {k : Type u} [Field k] {Y X : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (i : X ⟶ Y) (L : Y.Modules) [L.IsInvertible]
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    Set.range (bertiniIncidenceBaseChange f i L s) =
      ((bertiniUniversalIdeal f L s).subschemeι ≫
        pullback.snd (Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial I k))) f) ⁻¹' Set.range i := by
  let hp := isPullback_bertiniIncidenceBaseChange f i L s
  rw [← hp.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, (show Function.Surjective hp.isoPullback.hom from
      (Scheme.homeoOfIso hp.isoPullback).surjective).range_eq,
    Set.image_univ, Scheme.Pullback.range_fst]

private theorem irreducible_bertiniIncidence_over_trivialization
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [IrreducibleSpace Y]
    (L : Y.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V] :
    letI : Module k Γ(L, ⊤) :=
      Module.compHom Γ(L, ⊤) (Scheme.globalSectionsRingHom k (X := Y))
    ∀ (ψ : V →ₗ[k] Γ(L, ⊤)) (v₀ : V),
      (∃ y : Y, y ∉ (Scheme.Modules.homOfGlobalSection L (ψ v₀)).zeroLocus.support) →
      (∀ B : TopologicalSpace.IrreducibleCloseds Y,
        Maximal (fun T : TopologicalSpace.IrreducibleCloseds Y ↦ (T : Set Y) ⊆
          ⋂ v : V, ((Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.support : Set Y)) B →
          2 ≤ Order.coheight B) →
      ∀ {I : Type u} [Fintype I] (b : Module.Basis I k V)
        (U : Y.affineOpens) (_hne : (U.1 : Set Y).Nonempty)
        {e : Γ(L, U.1)} (_he : Scheme.Modules.IsFreeGenerator e),
      IsIrreducible
        (((bertiniUniversalIdeal (Y ↘ Spec (.of k)) L (fun j ↦ ψ (b j))).subschemeι ≫
          pullback.snd (Spec.map (CommRingCat.ofHom
            (MvPolynomial.C : k →+* MvPolynomial I k))) (Y ↘ Spec (.of k))) ⁻¹'
          (U.1 : Set Y)) := by
  classical
  let : Module k Γ(L, ⊤) :=
    Module.compHom Γ(L, ⊤) (Scheme.globalSectionsRingHom k (X := Y))
  intro ψ v₀ hv₀ hbase I _ b U hne e he
  obtain ⟨A, a, hft, hdom, i, hi, hiopen, hiinj, hiS, hiover, hirange, e', he', hZ⟩ :=
    exists_reduced_affine_trivialization k Y L U hne he
  let := a
  let := hft
  let := hdom
  let L' := (Scheme.Modules.tensorPullback i).obj L
  have : L'.IsInvertible := bertiniTensorPullback_invertible i L
  let aL := sectionCoefficientLinearMap k A i hiover L he' ψ
  have hZa (v : V) : i ⁻¹'
      ((Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.support : Set Y) =
      PrimeSpectrum.zeroLocus ({aL v} : Set A) := hZ (ψ v)
  have hf : ∃ j, aL (b j) ≠ 0 := by
    by_contra! hzero
    have ha : aL v₀ = 0 := by
      rw [← b.sum_repr v₀, map_sum]
      simp only [aL.map_smul, hzero, smul_zero, Finset.sum_const_zero]
    obtain ⟨y, hy⟩ := hv₀
    obtain ⟨z, hzU, hz⟩ := nonempty_preirreducible_inter U.1.isOpen
      (Scheme.Modules.homOfGlobalSection L (ψ v₀)).zeroLocus.support.isClosed.isOpen_compl
      hne ⟨y, hy⟩
    obtain ⟨q, rfl⟩ := hirange.ge hzU
    apply hz
    have hh : q ∈ i ⁻¹'
        ((Scheme.Modules.homOfGlobalSection L (ψ v₀)).zeroLocus.support : Set Y) := by
      rw [hZa, ha]
      change ({0} : Set A) ⊆ q.asIdeal
      exact Set.singleton_subset_iff.mpr q.asIdeal.zero_mem
    exact hh
  have hJ := coefficient_minimalPrime_height k A i hi L (fun v ↦ ψ v) aL hZa hbase b
  let s := fun j ↦ ψ (b j)
  let s' := fun j ↦ Scheme.Modules.tensorSectionsUnit i L (s j)
  have hH : IrreducibleSpace
      ((bertiniUniversalIdeal (i ≫ Y ↘ Spec (.of k)) L' s').subscheme) := by
    rw [hiover]
    exact irreducibleSpace_bertiniAffineIncidence k A L' he' s' hf hJ
  have hh := (IrreducibleSpace.isIrreducible_univ
    ((bertiniUniversalIdeal (i ≫ Y ↘ Spec (.of k)) L' s').subscheme)).image
      (bertiniIncidenceBaseChange (Y ↘ Spec (.of k)) i L s)
      (bertiniIncidenceBaseChange (Y ↘ Spec (.of k)) i L s).continuous.continuousOn
  rw [Set.image_univ, range_bertiniIncidenceBaseChange, hirange] at hh
  exact hh

private theorem irreducibleSpace_bertiniUniversalIncidence
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [IrreducibleSpace Y]
    (L : Y.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V] :
    letI : Module k Γ(L, ⊤) :=
      Module.compHom Γ(L, ⊤) (Scheme.globalSectionsRingHom k (X := Y))
    ∀ (ψ : V →ₗ[k] Γ(L, ⊤)) (v₀ : V),
      (∃ y : Y, y ∉ (Scheme.Modules.homOfGlobalSection L (ψ v₀)).zeroLocus.support) →
      (∀ B : TopologicalSpace.IrreducibleCloseds Y,
        Maximal (fun T : TopologicalSpace.IrreducibleCloseds Y ↦ (T : Set Y) ⊆
          ⋂ v : V, ((Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.support : Set Y)) B →
          2 ≤ Order.coheight B) →
      ∀ {I : Type u} [Fintype I] (b : Module.Basis I k V),
        IrreducibleSpace ((bertiniUniversalIdeal (Y ↘ Spec (.of k)) L
          (fun j ↦ ψ (b j))).subscheme) := by
  classical
  let : Module k Γ(L, ⊤) :=
    Module.compHom Γ(L, ⊤) (Scheme.globalSectionsRingHom k (X := Y))
  intro ψ v₀ hv₀ hbase I _ b
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  choose U hxU _ e he using fun y : Y ↦
    Scheme.Modules.exists_isFreeGenerator L (x := y) (W := ⊤) trivial
  let s := fun j ↦ ψ (b j)
  let H := (bertiniUniversalIdeal (Y ↘ Spec (.of k)) L s).subscheme
  let π : H ⟶ Y := (bertiniUniversalIdeal (Y ↘ Spec (.of k)) L s).subschemeι ≫
    pullback.snd (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : k →+* MvPolynomial I k))) (Y ↘ Spec (.of k))
  let O : Y → H.Opens := fun y ↦ (TopologicalSpace.Opens.map π.base).obj (U y).1
  obtain ⟨z, hz⟩ := exists_bertiniUniversalZeroSection (Y ↘ Spec (.of k)) L s
  have hzπ : z ≫ π = 𝟙 Y := hz
  have hzn (y : Y) : π (z y) = y := congrArg (fun f : Y ⟶ Y ↦ f y) hzπ
  have hnonempty : Nonempty H := ⟨z (Classical.arbitrary Y)⟩
  have hlocal (y : Y) : IsIrreducible (O y : Set H) :=
    irreducible_bertiniIncidence_over_trivialization k Y L V ψ v₀ hv₀ hbase b
      (U y) ⟨y, hxU y⟩ (he y)
  have hn : Pairwise (fun y y' ↦ ¬ Disjoint (O y) (O y')) := by
    intro y y' _
    obtain ⟨t, ht, ht'⟩ := nonempty_preirreducible_inter (U y).1.isOpen
      (U y').1.isOpen ⟨y, hxU y⟩ ⟨y', hxU y'⟩
    rw [← TopologicalSpace.Opens.coe_disjoint]
    apply Set.not_disjoint_iff_nonempty_inter.mpr
    refine ⟨z t, ?_, ?_⟩
    · change π (z t) ∈ (U y).1
      rw [hzn]
      exact ht
    · change π (z t) ∈ (U y').1
      rw [hzn]
      exact ht'
  have hcover : (Set.univ : Set H) ⊆ ⋃ y : Y, (O y : Set H) := by
    intro t _
    exact Set.mem_iUnion.mpr ⟨π t, hxU (π t)⟩
  have hpre : PreirreducibleSpace H :=
    ⟨IsPreirreducible.of_subset_iUnion hn (fun y ↦ (hlocal y).2) isOpen_univ hcover⟩
  exact { toNonempty := hnonempty }

/-- A dense affine chart of the incidence scheme, with its actual coefficient projection.

Source: Stacks Project, More on Morphisms, Tag 0G4F, first and final proof paragraphs.
(blueprint: lem-zl-bertini-incidence-adapted-chart).

Proof: Pass to the integral reduction; the reduction immersion identifies the topological
spaces and residue fields. The three vectors in the codimension hypothesis are independent:
evaluation at the generic point of the component kills the first coefficient, and dependence
of the other two contradicts the principal ideal theorem. Extend them to a basis. Choose an
affine open meeting that component on which the first section is invertible. Use that section
to trivialize the line bundle. The remaining section ratios are g. The finite type domain
dimension formula gives the displayed component dimension, and the generic-residue-field
criterion gives geometric irreducibility of the fraction field. The affine incidence chart
and elimination of the first variable give Spec A[x₂,...,xᵣ] mapping to the original incidence
scheme. On every reduced affine trivialization, the base-locus codimension bound gives an
irreducible incidence chart. The zero-parameter section makes these charts pairwise intersect,
so the whole incidence scheme is irreducible. The chosen chart has nonempty open image and is
therefore dominant; its reduction map is surjective on stalks. The adapted-basis change gives
c. The substitution formula for incidence elimination proves the displayed morphism equation.
-/
theorem exists_bertiniIncidenceAdaptedChart
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [GeometricallyIrreducible (Y ↘ Spec (.of k))]
    (L : Y.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    letI : Module k Γ(L, ⊤) :=
      Module.compHom Γ(L, ⊤) (Scheme.globalSectionsRingHom k (X := Y))
    ∀ ψ : V →ₗ[k] Γ(L, ⊤),
      (∃ (v₁ v₂ v₃ : V) (W : TopologicalSpace.IrreducibleCloseds Y),
        Maximal (fun Z : TopologicalSpace.IrreducibleCloseds Y ↦
          (Z : Set Y) ⊆ (Scheme.Modules.homOfGlobalSection L (ψ v₂)).zeroLocus.support ∩
            (Scheme.Modules.homOfGlobalSection L (ψ v₃)).zeroLocus.support) W ∧
        ¬ (W : Set Y) ⊆ (Scheme.Modules.homOfGlobalSection L (ψ v₁)).zeroLocus.support ∧
        Order.coheight W = 2) →
      (∀ B : TopologicalSpace.IrreducibleCloseds Y,
        Maximal (fun Z : TopologicalSpace.IrreducibleCloseds Y ↦
          (Z : Set Y) ⊆ ⋂ w : V,
            ((Scheme.Modules.homOfGlobalSection L (ψ w)).zeroLocus.support : Set Y)) B →
        2 ≤ Order.coheight B) →
      ∀ (r : ℕ) (b : Module.Basis (Fin r) k V),
      ∃ (A : CommRingCat.{u}) (a : Algebra k A),
        letI := a
        ∃ (hft : Algebra.FiniteType k A) (hdom : IsDomain A),
          letI := hft
          letI := hdom
          ∃ (n : ℕ) (hn : 2 ≤ n) (g : Fin n → A),
            (∃ W : Set (PrimeSpectrum.zeroLocus
                ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)),
              W ∈ irreducibleComponents (PrimeSpectrum.zeroLocus
                ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)) ∧
              topologicalKrullDim W + 2 = ringKrullDim A) ∧
            GeometricallyIrreducible
              (Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing A)))) ∧
            ∃ (j : Spec (.of (MvPolynomial (Fin n) A)) ⟶
                (bertiniUniversalIdeal (Y ↘ Spec (.of k)) L
                  (fun i : ULift.{u} (Fin r) ↦ ψ (b i.down))).subscheme)
              (c : Spec (.of (MvPolynomial (ULift.{u} (Fin r)) k)) ≅
                Spec (.of (MvPolynomial (Fin (n + 1)) k))),
              IsDominant j ∧ SurjectiveOnStalks j ∧
              j ≫ bertiniUniversalProjection (Y ↘ Spec (.of k)) L
                  (fun i : ULift.{u} (Fin r) ↦ ψ (b i.down)) ≫ c.hom =
                bertiniEliminatedProjection k A n g := by
  classical
  let : Module k Γ(L, ⊤) :=
    Module.compHom Γ(L, ⊤) (Scheme.globalSectionsRingHom k (X := Y))
  intro ψ hcomp hbase r b
  have hY : IrreducibleSpace Y :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (Y ↘ Spec (.of k))
  obtain ⟨v₁, v₂, v₃, W, hW, havoid, hcodim⟩ := hcomp
  obtain ⟨x, hxW, hx₁⟩ := Set.not_subset.mp havoid
  obtain ⟨U, hxU, hgen⟩ := exists_affine_generator_avoiding_zeroLocus L (ψ v₁) hx₁
  let R := Γ(Y, U.1)
  let φ : k →+* R := ((Y ↘ Spec (.of k)).appLE ⊤ U.1 (by simp)).hom.comp
    (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Algebra k R := φ.toAlgebra
  have hftR : Algebra.FiniteType k R :=
    ((Y ↘ Spec (.of k)).finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  have hneR : Nonempty (Spec (.of R)) := by
    obtain ⟨p, hp⟩ := (IsAffineOpen.range_fromSpec U.2).ge hxU
    exact ⟨p⟩
  have hIR : IrreducibleSpace (Spec (.of R)) := U.2.fromSpec.isOpenEmbedding.irreducibleSpace
  have hnil : (nilradical R).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hIR
  let A := R ⧸ nilradical R
  have : (nilradical R).IsPrime := hnil
  have hdom : IsDomain A := inferInstance
  have hftA : Algebra.FiniteType k A := inferInstance
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let ρ : Spec (.of A) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical R)))
  have hρ : IsHomeomorph ρ := by
    change IsHomeomorph (PrimeSpectrum.comap (Ideal.Quotient.mk (nilradical R)))
    exact isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨(PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
        Ideal.Quotient.mk_surjective).isEmbedding,
        (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical le_rfl).2⟩
  have hρclosed : IsClosedImmersion ρ := inferInstance
  have hρsurj : Surjective ρ := ⟨hρ.surjective⟩
  have hρuniv : IsUniversalHomeomorphism ρ := inferInstance
  have hUover : U.2.fromSpec ≫ Y ↘ Spec (.of k) =
      Spec.map (CommRingCat.ofHom φ) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec (Y ↘ Spec (.of k))
      (isAffineOpen_top _) U.2 (by simp), IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hUsurj : Surjective (U.2.fromSpec ≫ Y ↘ Spec (.of k)) :=
    ⟨Function.surjective_to_subsingleton _⟩
  have hUgeom : GeometricallyIrreducible (Spec.map (CommRingCat.ofHom φ)) := by
    rw [← hUover]
    infer_instance
  have hAgeom : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
    have h := geomIrred_comp_universalHomeomorphism ρ (Spec.map (CommRingCat.ofHom φ))
    rw [← Spec.map_comp] at h
    exact h
  have hKgeom : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing A)))) :=
    geomIrred_fractionRing k A
  let i : Spec (.of A) ⟶ Y := ρ ≫ U.2.fromSpec
  have hiover : i ≫ Y ↘ Spec (.of k) =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    dsimp only [i]
    rw [Category.assoc, hUover, ← Spec.map_comp]
    rfl
  have hiU : ⊤ ≤ i ⁻¹ᵁ U.1 := by
    change ⊤ ≤ ρ ⁻¹ᵁ (U.2.fromSpec ⁻¹ᵁ U.1)
    rw [U.2.fromSpec_preimage_self, ρ.preimage_top]
  have hiapp : i.appLE U.1 ⊤ hiU =
      CommRingCat.ofHom (Ideal.Quotient.mk (nilradical R)) ≫
        (Scheme.ΓSpecIso (.of A)).inv := by
    dsimp only [i]
    rw [Scheme.Hom.comp_appLE, U.2.fromSpec_app_self, Category.assoc,
      Scheme.Hom.map_appLE]
    change (Scheme.ΓSpecIso (.of R)).inv ≫ ρ.appLE ⊤ ⊤ _ = _
    have he : ρ.appLE ⊤ ⊤ (by simp) = ρ.appTop := by
      convert! ρ.appLE_eq_app (U := ⊤) using 1
    rw [he]
    exact (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical R)))).symm
  let L' := (Scheme.Modules.tensorPullback i).obj L
  have hL' : L'.IsInvertible := bertiniTensorPullback_invertible i L
  let e' := Scheme.Modules.tensorSectionsUnit i L (ψ v₁)
  have he' : Scheme.Modules.IsFreeGenerator e' :=
    bertiniTensorSectionsUnit_freeGenerator i L hiU (ψ v₁) hgen
  have hi : Topology.IsOpenEmbedding i :=
    U.2.fromSpec.isOpenEmbedding.comp hρ.isOpenEmbedding
  have hWne : (i ⁻¹' (W : Set Y)).Nonempty := by
    obtain ⟨p, hp⟩ := (IsAffineOpen.range_fromSpec U.2).ge hxU
    obtain ⟨q, hq⟩ := hρ.surjective p
    refine ⟨q, ?_⟩
    change U.2.fromSpec (ρ q) ∈ (W : Set Y)
    rw [hq, hp]
    exact hxW
  obtain ⟨W', hWpre, hWmax, hWcodim⟩ := restrict_maximal_irreducible_closed i hi
    ((Scheme.Modules.homOfGlobalSection L (ψ v₂)).zeroLocus.support.isClosed.inter
      (Scheme.Modules.homOfGlobalSection L (ψ v₃)).zeroLocus.support.isClosed) W hW hWne
  let c : V → R := fun v ↦
    hgen.coeff (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (ψ v))
  let a : V → A := fun v ↦ Ideal.Quotient.mk (nilradical R) (c v)
  have hcadd (v w : V) : c (v + w) = c v + c w := by
    dsimp only [c]
    rw [ψ.map_add, map_add, hgen.coeff_add]
  have hcsmul (t : k) (v : V) : c (t • v) = φ t * c v := by
    dsimp only [c]
    rw [ψ.map_smul]
    change hgen.coeff (L.presheaf.map (homOfLE le_top).op
      (Scheme.globalSectionsRingHom k (X := Y) t • ψ v)) = _
    rw [Scheme.Modules.map_smul, hgen.coeff_smul_left]
    rfl
  let aL : V →ₗ[k] A :=
    { toFun := a
      map_add' := fun v w ↦ by dsimp [a]; rw [hcadd, map_add]
      map_smul' := fun t v ↦ by
        dsimp only [a]
        rw [hcsmul, map_mul]
        rfl }
  have ha₁ : aL v₁ = 1 := by
    change Ideal.Quotient.mk (nilradical R) (hgen.coeff _) = 1
    have he : hgen.coeff
        (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (ψ v₁)) = 1 := by
      rw [hgen.coeff_eq_iff, one_smul]
    rw [he, map_one]
  have hcoeff (v : V) : (Scheme.ΓSpecIso (.of A)).hom
      (he'.coeff (Scheme.Modules.tensorSectionsUnit i L (ψ v))) = a v := by
    have hrel := bertiniTensorSectionsUnit_local_smul i L hiU (ψ v) (ψ v₁) (c v)
      (hgen.coeff_smul _).symm
    have hc : he'.coeff (Scheme.Modules.tensorSectionsUnit i L (ψ v)) =
        i.appLE U.1 ⊤ hiU (c v) := (he'.coeff_eq_iff _ _).mpr hrel.symm
    rw [hc, hiapp]
    change (Scheme.ΓSpecIso (.of A)).hom
      ((Scheme.ΓSpecIso (.of A)).inv (Ideal.Quotient.mk (nilradical R) (c v))) = a v
    simp only [Iso.inv_hom_id_apply]
    rfl
  have hiZ (v : V) :
      i ⁻¹' ((Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.support : Set Y) =
        PrimeSpectrum.zeroLocus ({a v} : Set A) := by
    change ρ ⁻¹' (U.2.fromSpec ⁻¹'
      ((Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.support : Set Y)) = _
    rw [affine_preimage_section_zeroLocus L U hgen]
    change (PrimeSpectrum.comap (Ideal.Quotient.mk (nilradical R))) ⁻¹'
      PrimeSpectrum.zeroLocus ({c v} : Set R) = _
    rw [PrimeSpectrum.preimage_comap_zeroLocus]
    simp only [Set.image_singleton]
    rfl
  have hiZ₂₃ : i ⁻¹'
      (((Scheme.Modules.homOfGlobalSection L (ψ v₂)).zeroLocus.support : Set Y) ∩
        (Scheme.Modules.homOfGlobalSection L (ψ v₃)).zeroLocus.support) =
      PrimeSpectrum.zeroLocus ({a v₂, a v₃} : Set A) := by
    rw [Set.preimage_inter, hiZ, hiZ, ← PrimeSpectrum.zeroLocus_union]
    rfl
  have hWmax' : Maximal
      (fun T : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A) ↦
        (T : Set (PrimeSpectrum A)) ⊆
          PrimeSpectrum.zeroLocus ((Ideal.span ({a v₂, a v₃} : Set A) : Ideal A) : Set A)) W' := by
    simp only [hiZ₂₃] at hWmax
    simp only [PrimeSpectrum.zeroLocus_span]
    exact hWmax
  obtain ⟨p, hp, hheight, hVp⟩ := prime_of_maximal_irreducible_zeroLocus A
    (Ideal.span ({a v₂, a v₃} : Set A)) W' hWmax'
  have hheight₂ : p.height = 2 := hheight.trans (hWcodim.trans hcodim)
  have hv123 : LinearIndependent k ![v₁, v₂, v₃] :=
    independent_triple_of_minimalPrime_height_two k A aL v₁ v₂ v₃ ha₁ p hp hheight₂
  obtain ⟨n, hn, b', hb'⟩ := exists_basis_extending_triple k ![v₁, v₂, v₃] hv123
  let g : Fin n → A := fun j ↦ aL (b' j.succ)
  have hg₀ : g ⟨0, Nat.zero_lt_of_lt hn⟩ = a v₂ := by
    have h := hb' 1
    simp only [Fin.isValue, Matrix.cons_val_one] at h
    exact congrArg aL h
  have hg₁ : g ⟨1, hn⟩ = a v₃ := by
    have h := hb' 2
    simp only [Fin.isValue, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
    exact congrArg aL h
  have hdim : ∃ C : Set (PrimeSpectrum.zeroLocus
      ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)),
      C ∈ irreducibleComponents (PrimeSpectrum.zeroLocus
        ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)) ∧
      topologicalKrullDim C + 2 = ringKrullDim A := by
    rw [hg₀, hg₁]
    have hmax : Maximal (fun T : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A) ↦
        (T : Set (PrimeSpectrum A)) ⊆ PrimeSpectrum.zeroLocus ({a v₂, a v₃} : Set A)) W' := by
      simpa only [PrimeSpectrum.zeroLocus_span] using hWmax'
    obtain ⟨C, hC, hdimC⟩ := component_of_maximal_irreducible_closed
      (PrimeSpectrum.isClosed_zeroLocus _) W' hmax
    refine ⟨C, hC, ?_⟩
    rw [hdimC, hVp, ← PrimeSpectrum.closure_singleton (⟨p, hp.isPrime⟩ : PrimeSpectrum A),
      PrimeSpectrum.topologicalKrullDim_closure_singleton]
    have : p.IsPrime := hp.isPrime
    have hd := finiteType_domain_quotient_dimension k A p
    rw [hheight₂] at hd
    exact hd
  let bU : Module.Basis (ULift.{u} (Fin r)) k V := b.reindex Equiv.ulift.symm
  obtain ⟨eK, eA, heA, hpoly⟩ :=
    Algebra.exists_bertiniBasisCoordinateChange k A bU b' aL
  have hnew : (∑ j : Fin (n + 1), MvPolynomial.C (aL (b' j)) * MvPolynomial.X j) =
      MvPolynomial.X 0 + ∑ j : Fin n, MvPolynomial.C (g j) * MvPolynomial.X j.succ := by
    rw [Fin.sum_univ_succ]
    have hb₀ : b' 0 = v₁ := hb' 0
    rw [hb₀, ha₁, map_one, one_mul]
  let F : MvPolynomial (ULift.{u} (Fin r)) A :=
    ∑ j, MvPolynomial.C (aL (bU j)) * MvPolynomial.X j
  let Q := Ideal.span ({F} : Set (MvPolynomial (ULift.{u} (Fin r)) A))
  let P : Ideal (MvPolynomial (Fin (n + 1)) A) := Ideal.span
    {MvPolynomial.X 0 + ∑ j : Fin n, MvPolynomial.C (g j) * MvPolynomial.X j.succ}
  have hPQ : P = Q.map eA.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z ↦ Ideal.span {z}) (hpoly.trans hnew).symm
  let eQ := Ideal.quotientEquivAlg Q P eA hPQ
  obtain ⟨eE, heE⟩ := Algebra.exists_bertiniIncidenceElimination A n g
  let E := eQ.trans eE
  let s : ULift.{u} (Fin r) → Γ(L, ⊤) := fun j ↦ ψ (b j.down)
  let s' := fun j ↦ Scheme.Modules.tensorSectionsUnit i L (s j)
  obtain ⟨eH, heH⟩ : ∃ eH :
      (bertiniUniversalIdeal (i ≫ Y ↘ Spec (.of k)) L' s').subscheme ≅
        Spec (.of (MvPolynomial (ULift.{u} (Fin r)) A ⧸ Q)),
      eH.inv ≫ bertiniUniversalProjection (i ≫ Y ↘ Spec (.of k)) L' s' =
        Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk Q).comp (MvPolynomial.map (algebraMap k A)))) := by
    rw [hiover]
    have hF : (∑ j, MvPolynomial.C
        ((Scheme.ΓSpecIso (.of A)).hom (he'.coeff (s' j))) * MvPolynomial.X j) = F := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hcoeff]
      simp only [bU, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.ulift_apply]
      rfl
    have hh := exists_bertiniAffineIncidenceChart k A L' he' s'
    rw [hF] at hh
    exact hh
  let eTot := eH ≪≫ Scheme.Spec.mapIso E.toRingEquiv.toCommRingCatIso.symm.op
  let m := bertiniIncidenceBaseChange (Y ↘ Spec (.of k)) i L s
  let j := eTot.inv ≫ m
  let c := Scheme.Spec.mapIso eK.toRingEquiv.toCommRingCatIso.symm.op
  refine ⟨.of A, inferInstance, hftA, hdom, n, hn, g, hdim, hKgeom, j, c, ?_, ?_, ?_⟩
  · have hH :=
      irreducibleSpace_bertiniUniversalIncidence k Y L V ψ v₁ ⟨x, hx₁⟩ hbase bU
    have hbUs : (fun j ↦ ψ (bU j)) = s := by
      funext j
      dsimp only [bU, s]
      rw [Module.Basis.reindex_apply]
      rfl
    rw [hbUs] at hH
    let := hH
    let hnpoly : Nonempty (Spec (.of (MvPolynomial (Fin n) A))) := by
      change Nonempty (PrimeSpectrum (MvPolynomial (Fin n) A))
      infer_instance
    have hirange : Set.range i = (U.1 : Set Y) := by
      change Set.range (U.2.fromSpec ∘ ρ) = _
      rw [Set.range_comp, hρ.surjective.range_eq, Set.image_univ]
      exact IsAffineOpen.range_fromSpec U.2
    have hrange : Set.range j =
        ((bertiniUniversalIdeal (Y ↘ Spec (.of k)) L s).subschemeι ≫
          pullback.snd (Spec.map (CommRingCat.ofHom
            (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin r)) k)))
            (Y ↘ Spec (.of k))) ⁻¹' (U.1 : Set Y) := by
      dsimp only [j]
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        (show Function.Surjective eTot.inv from
          (Scheme.homeoOfIso eTot.symm).surjective).range_eq, Set.image_univ,
        range_bertiniIncidenceBaseChange, hirange]
    rw [isDominant_iff]
    change Dense (Set.range j)
    rw [hrange]
    apply (U.1.isOpen.preimage (Scheme.Hom.continuous _)).dense
    rw [← hrange]
    obtain ⟨t⟩ := hnpoly
    exact ⟨j t, t, rfl⟩
  · have hiS : SurjectiveOnStalks i := by dsimp only [i]; infer_instance
    have hm : SurjectiveOnStalks m := MorphismProperty.of_isPullback
      (isPullback_bertiniIncidenceBaseChange (Y ↘ Spec (.of k)) i L s).flip hiS
    dsimp only [j]
    infer_instance
  · have hmproj : m ≫ bertiniUniversalProjection (Y ↘ Spec (.of k)) L s =
        bertiniUniversalProjection (i ≫ Y ↘ Spec (.of k)) L' s' :=
      bertiniIncidenceBaseChange_projection (Y ↘ Spec (.of k)) i L s
    change (eTot.inv ≫ m) ≫ bertiniUniversalProjection (Y ↘ Spec (.of k)) L s ≫
      c.hom = _
    simp only [Category.assoc]
    rw [← Category.assoc m, hmproj]
    change (Spec.map E.toRingEquiv.toCommRingCatIso.hom ≫ eH.inv) ≫
      bertiniUniversalProjection (i ≫ Y ↘ Spec (.of k)) L' s' ≫ c.hom = _
    rw [Category.assoc, ← Category.assoc eH.inv, heH]
    change Spec.map E.toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk Q).comp (MvPolynomial.map (algebraMap k A)))) ≫
        Spec.map eK.toRingEquiv.toCommRingCatIso.inv = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    unfold bertiniEliminatedProjection
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    change E (Ideal.Quotient.mk Q (MvPolynomial.map (algebraMap k A) (eK.symm t))) = _
    have hE (p : MvPolynomial (ULift.{u} (Fin r)) A) :
        E (Ideal.Quotient.mk Q p) =
          MvPolynomial.aeval
            (Fin.cases (-∑ j : Fin n, MvPolynomial.C (g j) * MvPolynomial.X j)
              MvPolynomial.X) (eA p) := by
      dsimp only [E, AlgEquiv.trans_apply, eQ]
      rw [Ideal.quotientEquivAlg_mk]
      exact heE _
    rw [hE, heA, eK.apply_symm_apply]
    exact MvPolynomial.eval₂_map (algebraMap k A) _ MvPolynomial.C t

end AlgebraicGeometry
