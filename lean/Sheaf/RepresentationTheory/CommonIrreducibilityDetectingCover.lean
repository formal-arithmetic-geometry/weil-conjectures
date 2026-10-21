/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.GaloisLisseCorrespondenceData
public import Sheaf.Paper.LisseAdicFiberFunctors
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.RepresentationTheory.Irreducible
public import Sheaf.RepresentationTheory.LAdic
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
import Sheaf.Paper.GaloisLisseRepresentations
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.RepresentationTheory.ProfiniteStableLattice
import WeilConjectures.RepresentationTheory.FiniteMatrixWitness
import Mathlib.RingTheory.Localization.Module
import Mathlib.CategoryTheory.Simple
import Sheaf.RepresentationTheory.LAdicSubrepresentation
import WeilConjectures.Mathlib.RepresentationTheory.Irreducible
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups

/-! # A common finite etale cover detecting irreducibility

Source: blueprint main-20261015, sec-deligne-laumon-general,
proof of lem-zl-curve-testing-irreducibility, first six sentences
(blueprint: lem-zl-common-irreducibility-detecting-cover).

The model structure merely bundles the existential coefficient, representation and lattice
witnesses. Its vector space is in coordinates; no basis of a given stalk is prescribed.
The stalk action is specified through the existing evaluation-normalized correspondence.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- The finite coefficient model, stable full lattice, uniformizer and positive reduction
level in the detecting-cover assertion. All fields are actual data or their properties.
Source: blueprint main-20261015, proof of lem-zl-curve-testing-irreducibility,
first six sentences (blueprint: lem-zl-common-irreducibility-detecting-cover). -/
structure IrreducibilityDetectingModel (l : ℕ) [Fact l.Prime]
    (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]
    (G : ProfiniteGrp.{u}) where
  /-- Finite extension inside the fixed algebraic closure. -/
  E : Padic.FiniteCoefficientFields l K
  /-- Dimension of the coordinate vector space. -/
  rank : ℕ
  /-- The finite-dimensional representation. -/
  ρ : G →* ((Fin rank → E.val) ≃ₗ[E.val] (Fin rank → E.val))
  /-- Joint continuity for the canonical l-adic vector-space topology. -/
  continuous : Representation.IsContinuousCoefficient l E.val G (Fin rank → E.val) ρ
  /-- Integral lattice in the coordinate vector space. -/
  lattice : Submodule (Padic.coefficientExtensionIntegers l E.val) (Fin rank → E.val)
  /-- Finite generation over the integers. -/
  finite : lattice.FG
  /-- Freeness over the integers. -/
  free : Module.Free (Padic.coefficientExtensionIntegers l E.val) lattice
  /-- Fullness over the coefficient field. -/
  full : Submodule.span E.val (lattice : Set (Fin rank → E.val)) = ⊤
  /-- Stability under every group element. -/
  stable : ∀ g : G, (ρ g) '' (lattice : Set (Fin rank → E.val)) = lattice
  /-- A uniformizer, rather than an arbitrary element of the integers. -/
  uniformizer : Padic.coefficientExtensionIntegers l E.val
  /-- The uniformizer generates the maximal ideal. -/
  generates : Ideal.span ({uniformizer} : Set (Padic.coefficientExtensionIntegers l E.val)) =
    Padic.coefficientExtensionMaximalIdeal l E.val
  /-- The reduction level. -/
  N : ℕ
  /-- The reduction level is positive. -/
  positive : 1 ≤ N

private theorem simple_of_mono_dichotomy
    {C : Type*} [Category C] [HasZeroMorphisms C] (F : C)
    (hF : ¬ IsZero F ∧ ∀ (A : C) (f : A ⟶ F), Mono f → IsZero A ∨ IsIso f) :
    Simple F where
  mono_isIso_iff_nonzero {A} f hf := by
    constructor
    · intro hi hz
      have h : 𝟙 F = 0 := by
        calc
          𝟙 F = inv f ≫ f := (IsIso.inv_hom_id f).symm
          _ = inv f ≫ 0 := congrArg (fun a ↦ inv f ≫ a) hz
          _ = 0 := comp_zero
      exact hF.1 ((IsZero.iff_id_eq_zero F).mpr h)
    · intro hn
      rcases hF.2 A f hf with ha | hi
      · exact False.elim (hn (ha.eq_of_src f 0))
      · exact hi

private theorem adic_rep_irreducible
    (l : ℕ) [Fact l.Prime] (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] (G : Type u) [Group G] [TopologicalSpace G]
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    (R : galoisAdicRepresentations l K P δ) [HasZeroMorphisms
      (galoisAdicRepresentations l K P δ)] [Simple R] : R.obj.ρ.IsIrreducible := by
  classical
  let ι := ObjectProperty.ι (fun X : Rep.{u + 1} K G ↦
    Representation.IsLAdic l K P X.V
      ((galoisRepLinearAction K X).comp δ.symm.toMonoidHom))
  have hn : Nontrivial R.obj.V := by
    by_contra h
    have hs : Subsingleton R.obj.V := not_nontrivial_iff_subsingleton.mp h
    exact Simple.not_isZero R
      (IsZero.of_full_of_faithful_of_isZero ι R ((Rep.isZero_iff K G _).mpr hs))
  refine Representation.isIrreducible_iff.mpr ⟨hn, ?_⟩
  intro U hU
  let σ := R.obj.ρ.subrepresentation U hU
  let A₀ := Rep.of σ
  have ha : Representation.IsLAdic l K P U
      ((galoisRepLinearAction K A₀).comp δ.symm.toMonoidHom) := by
    apply Representation.isLAdic_subrepresentation l K P R.obj.V
      ((galoisRepLinearAction K R.obj).comp δ.symm.toMonoidHom) R.property U
    intro g v
    rfl
  let A : galoisAdicRepresentations l K P δ := ⟨A₀, ha⟩
  let f₀ : A₀ ⟶ R.obj := Rep.ofHom ⟨U.subtype, by intro g; ext v; rfl⟩
  have : Mono f₀ := (Rep.mono_iff_injective _).mpr Subtype.val_injective
  let f : A ⟶ R := ObjectProperty.homMk f₀
  have : Mono f := ι.mono_of_mono_map (by change Mono f₀; infer_instance)
  by_cases hi : IsIso f
  · right
    have : IsIso f₀ := ι.map_isIso f
    have hf : Function.Surjective f₀.hom := (Rep.epi_iff_surjective _).mp inferInstance
    exact top_unique fun v _ ↦ by
      obtain ⟨w, hw⟩ := hf v
      exact hw ▸ w.property
  · left
    have hf : f = 0 := mono_to_simple_zero_of_not_iso hi
    have hu (v : U) : (v : R.obj.V) = 0 := by
      have h := congrArg (fun a : A ⟶ R ↦ ((ι.map a).hom v)) hf
      exact h.trans (by change ((ι.map (0 : A ⟶ R)).hom v) = 0; simp)
    exact le_bot_iff.mp fun v hv ↦ hu ⟨v, hv⟩

private theorem scalarExtension_tmul
    {E K G V : Type*} [Field E] [Field K] [Algebra E K] [Group G]
    [AddCommGroup V] [Module E V] (ρ : G →* (V ≃ₗ[E] V))
    (g : G) (a : K) (v : V) :
    Representation.coefficientScalarExtension E K G V ρ g (a ⊗ₜ[E] v) =
      a ⊗ₜ[E] ρ g v := rfl

private theorem scalarExtension_toLinearMap
    {E K G V : Type*} [Field E] [Field K] [Algebra E K] [Group G]
    [AddCommGroup V] [Module E V] (ρ : G →* (V ≃ₗ[E] V)) :
    (Module.End.baseChangeHom E K V).toMonoidHom.comp
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) =
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
        (Representation.coefficientScalarExtension E K G V ρ) := by
  ext g v
  rfl

private theorem continuous_coefficient_conj
    (l : ℕ) [Fact l.Prime] {E : Type*} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (G P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    {V W : Type*} [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]
    (τ : P →* (W ≃ₗ[E] W)) (hτ : Representation.IsContinuousCoefficient l E P W τ)
    (b : V ≃ₗ[E] W) (σ : G →* (V ≃ₗ[E] V))
    (hs : ∀ g v, σ g v = b.symm (τ (δ g) (b v))) :
    Representation.IsContinuousCoefficient l E G V σ := by
  have : FiniteDimensional E W := hτ.1
  have : FiniteDimensional E V := Module.Finite.equiv b.symm
  refine ⟨inferInstance, ?_⟩
  let : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : TopologicalSpace W := moduleTopology E W
  let : TopologicalSpace V := moduleTopology E V
  have : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup E W
  have : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup E V
  have : ContinuousSMul E W := IsModuleTopology.toContinuousSMul E W
  have : ContinuousSMul E V := IsModuleTopology.toContinuousSMul E V
  have hb : Continuous (b : V → W) :=
    IsModuleTopology.continuous_of_linearMap b.toLinearMap
  have hbi : Continuous (b.symm : W → V) :=
    IsModuleTopology.continuous_of_linearMap b.symm.toLinearMap
  have hc := hbi.comp (hτ.2.comp
    ((δ.continuous.comp continuous_fst).prodMk (hb.comp continuous_snd)))
  exact hc.congr (fun p ↦ (hs p.1 p.2).symm)

private theorem ladic_coordinate_model
    (l : ℕ) [Fact l.Prime] (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] (G : ProfiniteGrp.{u}) (P : ProfiniteGrp.{u})
    (δ : G ≃ₜ* P) (V : Type (u + 1)) [AddCommGroup V] [Module K V]
    (ρ : G →* (V ≃ₗ[K] V))
    (hρ : Representation.IsLAdic l K P V (ρ.comp δ.symm.toMonoidHom)) :
    ∃ (E : Padic.FiniteCoefficientFields l K) (n : ℕ)
      (σ : G →* ((Fin n → E.val) ≃ₗ[E.val] (Fin n → E.val))),
      Representation.IsContinuousCoefficient l E.val G (Fin n → E.val) σ ∧
      ∃ e : (K ⊗[E.val] (Fin n → E.val)) ≃ₗ[K] V,
        ∀ (g : G) (v : K ⊗[E.val] (Fin n → E.val)),
          e (Representation.coefficientScalarExtension E.val K G _ σ g v) = ρ g (e v) := by
  classical
  obtain ⟨_, E, hE, W, τ, hτ, heq, e, he⟩ := hρ
  have := hE
  let := Module.compHom V (algebraMap E K)
  have : FiniteDimensional E W := hτ.1
  let n := Module.finrank E W
  let b : (Fin n → E) ≃ₗ[E] W := (Module.finBasis E W).equivFun.symm
  let σ : G →* ((Fin n → E) ≃ₗ[E] (Fin n → E)) :=
    { toFun g := (b.trans (τ (δ g))).trans b.symm
      map_one' := by ext v; simp
      map_mul' g h := by ext v; simp }
  have hc : Representation.IsContinuousCoefficient l E G (Fin n → E) σ :=
    continuous_coefficient_conj l G P δ τ hτ b σ (fun _ _ ↦ rfl)
  refine ⟨⟨E, hE⟩, n, σ, hc, (b.baseChange E K _ _).trans e, ?_⟩
  intro g v
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul a v =>
    change e (b.baseChange E K _ _
      (Representation.coefficientScalarExtension E K G _ σ g (a ⊗ₜ[E] v))) = _
    rw [scalarExtension_tmul, LinearEquiv.baseChange_tmul]
    change e (a ⊗ₜ[E] b (σ g v)) = ρ g (e (a ⊗ₜ[E] b v))
    rw [he, he]
    have hbσ : b (σ g v) = τ (δ g) (b v) := b.apply_symm_apply _
    rw [hbσ]
    change a • (τ (δ g) (b v) : V) = ρ g (a • (b v : V))
    rw [heq]
    change a • ρ (δ.symm (δ g)) (b v : V) = _
    rw [δ.symm_apply_apply, map_smul]

private theorem lattice_field_basis
    {E : Type*} [Field E] (O : Subring E) [IsFractionRing O E]
    {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (L : Submodule O V) [Module.Free O L] [Module.Finite O L]
    (hr : Module.finrank O L = Module.finrank E V) :
    ∃ b : Module.Basis (Fin (Module.finrank O L)) E V,
      (∀ i, b i ∈ L) ∧
      ∀ v : L, ∀ i, b.repr (v : V) i = algebraMap O E ((Module.finBasis O L).repr v i) := by
  classical
  let c := Module.finBasis O L
  have hli : LinearIndependent O (fun i ↦ (c i : V)) :=
    c.linearIndependent.map' L.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliE : LinearIndependent E (fun i ↦ (c i : V)) :=
    hli.localization E (nonZeroDivisors O)
  let b : Module.Basis (Fin (Module.finrank O L)) E V :=
    .mk hliE (hliE.span_eq_top_of_card_eq_finrank' (by simpa using hr)).ge
  have hb (i) : b i = (c i : V) := Module.Basis.mk_apply _ _ _
  refine ⟨b, fun i ↦ by rw [hb]; exact (c i).property, ?_⟩
  intro v i
  have hv : (v : V) = ∑ j, (algebraMap O E (c.repr v j)) • b j := by
    calc
      (v : V) = ∑ j, (c.repr v j) • (c j : V) := by
        have h := congrArg (fun a : L ↦ (a : V)) (c.sum_repr v)
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using h.symm
      _ = _ := Finset.sum_congr rfl (fun j _ ↦ by
        rw [hb, IsScalarTower.algebraMap_smul E])
  rw [hv]
  exact congrFun (b.repr_sum_self (fun j ↦ algebraMap O E (c.repr v j))) i

private theorem principal_power_smul_top
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (π : R) (N : ℕ) (v : V) :
    v ∈ Ideal.span ({π} : Set R) ^ N • (⊤ : Submodule R V) ↔
      ∃ w : V, v = π ^ N • w := by
  rw [Ideal.span_singleton_pow]
  constructor
  · intro hv
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro a ha w hw
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
      refine ⟨b • w, ?_⟩
      rw [hb, mul_smul]
    · intro v w hv hw
      obtain ⟨v', rfl⟩ := hv
      obtain ⟨w', rfl⟩ := hw
      exact ⟨v' + w', (smul_add _ _ _).symm⟩
  · rintro ⟨w, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) (by trivial)

private theorem reduction_kernel
    {R : Type*} [CommRing R] [Nontrivial R] (I : Ideal R)
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Free R V] [Module.Finite R V]
    (τ : G →* (V ≃ₗ[R] V))
    (hc : letI := I.adicModuleTopology V
      Continuous (fun p : G × V ↦ τ p.1 p.2)) (N : ℕ) :
    ∃ S : Subgroup G, S.Normal ∧ IsOpen (S : Set G) ∧
      ∀ g : G, g ∈ S ↔ ∀ v : V, τ g v - v ∈ I ^ N • (⊤ : Submodule R V) := by
  classical
  let J : Submodule R V := I ^ N • ⊤
  let ρ : Representation R G V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp τ
  have hj : ∀ g : G, J ≤ J.comap (ρ g) := by
    intro g v hv
    change τ g v ∈ J
    change v ∈ I ^ N • (⊤ : Submodule R V) at hv
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro r hr v hv
      simpa using Submodule.smul_mem_smul hr (show τ g v ∈ (⊤ : Submodule R V) from trivial)
    · intro v w hv hw
      simpa using J.add_mem hv hw
  let β := ρ.quotient J hj
  let S := β.asGroupHom.ker
  have hs (g : G) : g ∈ S ↔ ∀ v : V, τ g v - v ∈ J := by
    change β.asGroupHom g = 1 ↔ _
    rw [← Units.val_inj, Representation.asGroupHom_apply]
    constructor
    · intro h v
      apply (Submodule.Quotient.eq J).mp
      exact DFunLike.congr_fun h (J.mkQ v)
    · intro h
      apply LinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := J.mkQ_surjective v
      exact (Submodule.Quotient.eq J).mpr (h w)
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace V := I.adicModuleTopology V
  let B := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis V)
  have : IsTopologicalAddGroup V := B.toAddGroupFilterBasis.isTopologicalAddGroup
  let SB := I.ringFilterBasis.submodulesBasisIsBasis (I.adic_module_basis V)
  have hopenJ : IsOpen (J : Set V) := (SB.openAddSubgroup N).isOpen
  let b := Module.finBasis R V
  have hb (g : G) : g ∈ S ↔ ∀ i, τ g (b i) - b i ∈ J := by
    rw [hs]
    refine ⟨fun h i ↦ h _, fun h v ↦ ?_⟩
    have hmap : ∀ i, β g (J.mkQ (b i)) = J.mkQ (b i) := by
      intro i
      exact (Submodule.Quotient.eq J).mpr (h i)
    apply (Submodule.Quotient.eq J).mp
    change β g (J.mkQ v) = J.mkQ v
    rw [← b.sum_repr v]
    simp only [map_sum, map_smul, hmap]
  have he : (S : Set G) = ⋂ i, {g : G | τ g (b i) - b i ∈ J} := by
    ext g
    simpa using hb g
  refine ⟨S, inferInstance, ?_, hs⟩
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact hopenJ.preimage ((hc.comp (continuous_id.prodMk continuous_const)).sub continuous_const)


private theorem detecting_lattice
    (l : ℕ) [Fact l.Prime] (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] (G : ProfiniteGrp.{u})
    (E : Type*) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [Algebra E K] (n : ℕ)
    (ρ : G →* ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    (hc : Representation.IsContinuousCoefficient l E G (Fin n → E) ρ)
    (hi : Representation.IsIrreducible
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
        (Representation.coefficientScalarExtension E K G _ ρ))) :
    ∃ (L : Submodule (Padic.coefficientExtensionIntegers l E) (Fin n → E))
      (π : Padic.coefficientExtensionIntegers l E) (N : ℕ) (S : Subgroup G),
      L.FG ∧ Module.Free (Padic.coefficientExtensionIntegers l E) L ∧
      Submodule.span E (L : Set (Fin n → E)) = ⊤ ∧
      (∀ g : G, (ρ g) '' (L : Set (Fin n → E)) = L) ∧
      Ideal.span ({π} : Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E ∧ 1 ≤ N ∧
      S.Normal ∧ IsOpen (S : Set G) ∧
      (∀ g : G, g ∈ S ↔ ∀ v : Fin n → E, v ∈ L →
        ∃ w ∈ L, ρ g v - v = π.val ^ N • w) ∧
      ∀ H : Subgroup G, (∀ g : G, ∃ h ∈ H, g⁻¹ * h ∈ S) →
        Representation.IsIrreducible
          (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
            ((Representation.coefficientScalarExtension E K G _ ρ).comp H.subtype)) := by
  classical
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ_[l]
  let O := Padic.coefficientExtensionIntegers l E
  let m := Padic.coefficientExtensionMaximalIdeal l E
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsLocalRing O := hdvr.2.2.2.1
  have : IsFractionRing O E := hdvr.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing O := hdvr.2.2.2.2.2.2.2.2.1
  have hm : IsLocalRing.maximalIdeal O = m :=
    hdvr.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal O)
  have hgen : ∃ π : O, Ideal.span ({π} : Set O) = m :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨π, hπ⟩ := hgen
  let : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : TopologicalSpace (Fin n → E) := moduleTopology E (Fin n → E)
  obtain ⟨L, hfg, hfull, hfree, hrank, hstable, htop, a, hca, ha⟩ :=
    Padic.exists_stable_lattice l E G (Fin n → E) ρ hc.2
  have := hfree
  have : Module.Finite O L := Module.Finite.of_fg hfg
  obtain ⟨b, hb, hbr⟩ := lattice_field_basis O L hrank
  let σ : Representation E G (Fin n → E) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  have hcoeff (g : G) (i j) :
      LinearMap.toMatrix b b (σ g) i j ∈ (algebraMap O E).range := by
    have hv : ρ g (b j) ∈ L := by
      exact (hstable g).subset ⟨b j, hb j, rfl⟩
    rw [LinearMap.toMatrix_apply]
    exact ⟨(Module.finBasis O L).repr ⟨ρ g (b j), hv⟩ i, (hbr _ i).symm⟩
  have hib : Representation.IsIrreducible
      ((Module.End.baseChangeHom E K (Fin n → E)).toMonoidHom.comp σ) := by
    rw [scalarExtension_toLinearMap]
    exact hi
  obtain ⟨N, hN, hdetect⟩ :=
    Representation.exists_forall_isIrreducible_baseChange_of_congr (O := O) (K := K)
      σ b hcoeff hib
  have hmap (g : G) : L.map ((ρ g).restrictScalars O).toLinearMap = L := by
    apply SetLike.coe_injective
    exact hstable g
  let τ : G →* (L ≃ₗ[O] L) :=
    { toFun g := ((ρ g).restrictScalars O).ofSubmodules L L (hmap g)
      map_one' := by
        apply LinearEquiv.ext
        intro v
        apply Subtype.ext
        change ρ 1 (v : Fin n → E) = v
        simp
      map_mul' g h := by
        apply LinearEquiv.ext
        intro v
        apply Subtype.ext
        change ρ (g * h) (v : Fin n → E) = ρ g (ρ h v)
        rw [map_mul]
        rfl }
  have hτ : letI := m.adicModuleTopology L
      Continuous (fun p : G × L ↦ τ p.1 p.2) := by
    let : TopologicalSpace L := m.adicModuleTopology L
    exact hca.congr (fun p ↦ Subtype.ext (ha p))
  obtain ⟨S, hnormal, hopen, hS⟩ := reduction_kernel m τ hτ N
  have hpow (v : L) : v ∈ m ^ N • (⊤ : Submodule O L) ↔
      ∃ w ∈ L, (v : Fin n → E) = π.val ^ N • w := by
    rw [← hπ, principal_power_smul_top]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, w.property, rfl⟩
    · rintro ⟨w, hw, hv⟩
      exact ⟨⟨w, hw⟩, Subtype.ext hv⟩
  have hSk (g : G) : g ∈ S ↔ ∀ v : Fin n → E, v ∈ L →
      ∃ w ∈ L, ρ g v - v = π.val ^ N • w := by
    rw [hS]
    constructor
    · intro h v hv
      exact (hpow _).mp (h ⟨v, hv⟩)
    · intro h v
      exact (hpow _).mpr (h v v.property)
  refine ⟨L, π, N, S, hfg, hfree, hfull, hstable, hπ, hN, hnormal, hopen, hSk, ?_⟩
  intro H hH
  have hd := hdetect H (fun g ↦ ?_) K
  · change Representation.IsIrreducible
      ((Module.End.baseChangeHom E K (Fin n → E)).toMonoidHom.comp
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (ρ.comp H.subtype))) at hd
    rw [scalarExtension_toLinearMap] at hd
    exact hd
  · obtain ⟨h, hh, hk⟩ := hH g
    refine ⟨h, hh, fun i j ↦ ?_⟩
    obtain ⟨w, hw, hdiff⟩ := (hSk (g⁻¹ * h)).mp hk (b j) (hb j)
    have hw' : ρ g w ∈ L := by
      exact (hstable g).subset ⟨w, hw, rfl⟩
    have hd : ρ h (b j) - ρ g (b j) = π.val ^ N • ρ g w := by
      have h := congrArg (ρ g) hdiff
      simpa only [map_sub, map_smul, ← LinearEquiv.mul_apply, ← map_mul,
        mul_inv_cancel_left] using h
    refine ⟨π ^ N * (Module.finBasis O L).repr ⟨ρ g w, hw'⟩ i, ?_, ?_⟩
    · rw [hm, ← hπ, Ideal.span_singleton_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
    · simp only [LinearMap.toMatrix_apply]
      change b.repr (ρ h (b j)) i - b.repr (ρ g (b j)) i = _
      rw [← Finsupp.sub_apply, ← map_sub, hd, map_smul, Finsupp.smul_apply,
        hbr ⟨ρ g w, hw'⟩ i]
      simp only [map_mul, map_pow, smul_eq_mul]
      rfl

private theorem finite_quotient_cover
    (X : Scheme.{u}) [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber x) G]
    (Q : Type u) [Group Q] [Finite Q] (q : G →* Q)
    (hq : @Continuous G Q inferInstance ⊥ q) (hs : Function.Surjective q) :
    ∃ T : X.FiniteEtale, ConnectedSpace T.obj.left ∧
      ∃ e : ((FiniteEtale.fiber x).obj T) ≃ Q,
        ∀ (g : G) (t : (FiniteEtale.fiber x).obj T), e (g • t) = q g * e t := by
  let : TopologicalSpace Q := ⊥
  have : DiscreteTopology Q := ⟨rfl⟩
  let : MulAction G Q := MulAction.compHom Q q
  have hopen (a : Q) : IsOpen {g : G | g • a = a} := by
    change IsOpen {g : G | q g * a = a}
    have he : {g : G | q g * a = a} = q ⁻¹' {1} := by
      ext g
      simp
    rw [he]
    exact (isOpen_discrete _).preimage hq
  obtain ⟨T, e, he⟩ := FiniteEtale.exists_fiber_equiv x G hopen
  have : Nonempty ((FiniteEtale.fiber x).obj T) := ⟨e.symm 1⟩
  have : MulAction.IsPretransitive G ((FiniteEtale.fiber x).obj T) := ⟨by
    intro a b
    obtain ⟨g, hg⟩ := hs (e b * (e a)⁻¹)
    refine ⟨g, e.injective ?_⟩
    rw [he]
    change q g * e a = e b
    rw [hg, inv_mul_cancel_right]⟩
  have : IsConnected T := FiniteEtale.isConnected_of_isPretransitive x G T
  exact ⟨T, FiniteEtale.connectedSpace_of_isConnected T, e, he⟩

/-- A finite family of irreducible lisse sheaves has a common detecting cover, including
the empty family. Irreducibility of sheaves is expressed by nonzeroness and the dichotomy
for every lisse subobject. The kernel formula is written elementwise: triviality on
`L / uniformizer^N L` means that every `ρ(g)v - v` is `uniformizer^N w` with `w ∈ L`.
The correspondence witnesses identify the action with the natural geometric stalk action.

Source: blueprint main-20261015, proof of lem-zl-curve-testing-irreducibility,
first six sentences (blueprint: lem-zl-common-irreducibility-detecting-cover).

Proof: use the Galois--lisse correspondence to obtain finite coefficient models and
canonical equivariant stalk comparisons. Simplicity is preserved by the equivalence;
invariant-subspace descent makes every vector subrepresentation an object of the same
category, so the scalar-extended models are irreducible. The given group is already
profinite. Choose stable free lattices and use their integral bases in the finite-matrix
witness theorem. The kernel of each lattice quotient action is open: membership can be
tested on finitely many basis vectors, and the lattice action is continuous for its adic
topology. The quotient by the intersection of these open normal kernels is finite by
compactness. Realize its regular action as a finite etale cover; its transitive nonempty
fibre makes the cover connected. Finally, if H surjects onto the quotient, each group
element has the same reduction as an element of H. Applying the finite-matrix witness to
these congruences gives irreducibility under H. The constructions include the empty family. -/
theorem exists_common_irreducibility_detecting_cover
    (X : Scheme.{u}) [ConnectedSpace X] [IsNoetherian X] [X.IsSeparated]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (l : ℕ) [Fact l.Prime] [∀ z : X, Invertible (l : X.residueField z)]
    (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber x) G]
    (r : ℕ) (F : Fin r → LisseAlgebraicSheaf l X K)
    (hF : ∀ j : Fin r, ¬ IsZero (F j) ∧
      ∀ (A : LisseAlgebraicSheaf l X K) (f : A ⟶ F j), Mono f → IsZero A ∨ IsIso f) :
    ∃ (c : GaloisLisseFiniteCorrespondence x G)
      (d : GaloisLisseAdicCorrespondence x G c l K)
      (M : Fin r → IrreducibilityDetectingModel l K G),
      (∀ j : Fin r, ∃ e : (K ⊗[(M j).E.val] (Fin (M j).rank → (M j).E.val)) ≃ₗ[K]
          ((lisseAlgebraicFiberFunctor l X x K).obj (F j)),
        ∀ (g : G) (v : K ⊗[(M j).E.val] (Fin (M j).rank → (M j).E.val)),
          e (Representation.coefficientScalarExtension (M j).E.val K G
            (Fin (M j).rank → (M j).E.val) (M j).ρ g v) =
          d.τA.hom.app (F j) (((d.eA.functor.obj (F j)).obj.ρ g)
            (d.τA.inv.app (F j) (e v)))) ∧
      ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q) (q : G →* Q),
        @Continuous G Q inferInstance ⊥ q ∧ Function.Surjective q ∧
        (∀ g : G, q g = 1 ↔ ∀ (j : Fin r) (v : Fin (M j).rank → (M j).E.val),
          v ∈ (M j).lattice → ∃ w ∈ (M j).lattice,
            (M j).ρ g v - v = ((M j).uniformizer.val ^ (M j).N) • w) ∧
        (∃ T : X.FiniteEtale, ConnectedSpace T.obj.left ∧
          ∃ e : ((FiniteEtale.fiber x).obj T) ≃ Q,
            ∀ (g : G) (t : (FiniteEtale.fiber x).obj T), e (g • t) = q g * e t) ∧
        ∀ H : Subgroup G, q '' (H : Set G) = Set.univ → ∀ j : Fin r,
          Representation.IsIrreducible
            (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
              ((Representation.coefficientScalarExtension (M j).E.val K G
                (Fin (M j).rank → (M j).E.val) (M j).ρ).comp H.subtype))  := by
  classical
  obtain ⟨c, hc⟩ := galois_lisse_representations x G
  obtain ⟨d⟩ := hc l K
  have : Abelian (LisseAlgebraicSheaf l X K) := d.algebraicSheavesAbelian.some
  have : Abelian (galoisAdicRepresentations l K d.P d.δ) :=
    d.algebraicRepresentationsAbelian.some
  have hsimple (j : Fin r) : Simple (F j) := simple_of_mono_dichotomy (F j) (hF j)
  have hirr (j : Fin r) : (d.eA.functor.obj (F j)).obj.ρ.IsIrreducible := by
    have := hsimple j
    have := simple_obj d.eA.functor (F j)
    exact adic_rep_irreducible l K G d.P d.δ _
  have hmodels (j : Fin r) := ladic_coordinate_model l K G d.P d.δ
    (d.eA.functor.obj (F j)).obj.V (galoisRepLinearAction K (d.eA.functor.obj (F j)).obj)
    (d.eA.functor.obj (F j)).property
  choose E n ρ hcont e he using hmodels
  have hcoord (j : Fin r) : Representation.IsIrreducible
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
        (Representation.coefficientScalarExtension (E j).val K G _ (ρ j))) := by
    let er : Representation.Equiv
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
        (Representation.coefficientScalarExtension (E j).val K G _ (ρ j)))
        (d.eA.functor.obj (F j)).obj.ρ := .mk (e j) (by
          intro g
          apply LinearMap.ext
          intro v
          exact he j g v)
    exact er.isIrreducible_iff.mpr (hirr j)
  have hlattices (j : Fin r) := detecting_lattice l K G (E j).val (n j) (ρ j) (hcont j) (hcoord j)
  choose L π N S hfg hfree hfull hstable hπ hN hnormal hopen hSk hdetect using hlattices
  let M : Fin r → IrreducibilityDetectingModel l K G := fun j ↦
    { E := E j
      rank := n j
      ρ := ρ j
      continuous := hcont j
      lattice := L j
      finite := hfg j
      free := hfree j
      full := hfull j
      stable := hstable j
      uniformizer := π j
      generates := hπ j
      N := N j
      positive := hN j }
  refine ⟨c, d, M, ?_, ?_⟩
  · intro j
    let ej := (e j).trans (d.τA.app (F j)).toLinearEquiv
    refine ⟨ej, ?_⟩
    intro g v
    change d.τA.hom.app (F j) (e j
      (Representation.coefficientScalarExtension (E j).val K G _ (ρ j) g v)) = _
    rw [he]
    congr 1
    change (d.eA.functor.obj (F j)).obj.ρ g (e j v) =
      (d.eA.functor.obj (F j)).obj.ρ g
        (d.τA.inv.app (F j) (d.τA.hom.app (F j) (e j v)))
    have ht := ConcreteCategory.congr_hom (d.τA.hom_inv_id_app (F j)) (e j v)
    change d.τA.inv.app (F j) (d.τA.hom.app (F j) (e j v)) = e j v at ht
    rw [ht]
  · let S₀ : Subgroup G := ⨅ j, S j
    have : S₀.Normal := Subgroup.normal_iInf_normal hnormal
    have hS₀ : IsOpen (S₀ : Set G) := by
      change IsOpen (↑(⨅ j, S j) : Set G)
      rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite hopen
    have : Finite (G ⧸ S₀) := S₀.quotient_finite_of_isOpen hS₀
    let q : G →* (G ⧸ S₀) := QuotientGroup.mk' S₀
    have hq : @Continuous G (G ⧸ S₀) inferInstance ⊥ q := by
      have : DiscreteTopology (G ⧸ S₀) := QuotientGroup.discreteTopology hS₀
      convert (QuotientGroup.continuous_mk (N := S₀)) using 1
      · exact DiscreteTopology.eq_bot.symm
      · rfl
    have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective S₀
    refine ⟨G ⧸ S₀, inferInstance, inferInstance, q, hq, hsurj, ?_,
      finite_quotient_cover X x G _ q hq hsurj, ?_⟩
    · intro g
      change (g : G ⧸ S₀) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_iInf]
      exact forall_congr' fun j ↦ hSk j g
    · intro H hH j
      apply hdetect j H
      intro g
      have hmem : q g ∈ q '' (H : Set G) := by rw [hH]; trivial
      obtain ⟨h, hh, heq⟩ := hmem
      refine ⟨h, hh, ?_⟩
      have hk : g⁻¹ * h ∈ S₀ := (QuotientGroup.eq_one_iff _).mp (by
        change q (g⁻¹ * h) = 1
        rw [map_mul, map_inv, heq, inv_mul_cancel])
      exact (Subgroup.mem_iInf.mp hk) j

end AlgebraicGeometry.Scheme
