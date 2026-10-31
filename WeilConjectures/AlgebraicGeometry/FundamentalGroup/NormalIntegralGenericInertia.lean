/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalPiOneExactSequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Limits
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import WeilConjectures.FieldTheory.GaloisTowerInertiaSurjective
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.RingTheory.InertiaInvariantsEtale
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.FieldTheory.Galois.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension
import WeilConjectures.AlgebraicGeometry.StrictLocalInertiaIdentification
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.NormalUnramifiedGaloisPresentation
import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability
import WeilConjectures.FieldTheory.OpenSubgroupFixedField
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered
import WeilConjectures.RingTheory.StrictHenselizationLocalMaximalIdeal
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-! # The generic Galois presentation with arbitrary strict henselizations

Source: Stacks Project, pione.tex, Tags 0BTD, 0BSW and 0BNE
(blueprint: lem-dl-a1-normal-integral-generic-inertia).

The rings `H x` are specified by the recorded pointed-etale colimit presentation,
not by an assumed normality or inertia property. Compatibility of a fraction-ring
embedding is expressed on the stalk: its fraction field is canonically `X.functionField`.
The fundamental group uses the standard small `IsFundamentalGroup` model;
`exists_fiber_flc_equivalence` identifies it with the recorded FLC-stalk version.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete Pointwise

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- Steps 1 and 9: transfer normality from the small pointed-etale colimit. -/
private theorem presentation_normal
    (A K C : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} A K C) :
    (IsDomain C ∧ IsIntegrallyClosed C) ∧ Function.Injective (algebraMap A C) := by
  classical
  open CategoryTheory.Limits in
  have hC : Algebra.IsStrictHenselization A K C :=
    ⟨P.cocone, ⟨P.isColimit⟩, ⟨P.identification⟩⟩
  obtain ⟨hloc, _⟩ := Algebra.strictHenselization_local_maximalIdeal A K C hC
  let := hloc
  obtain ⟨hsmall, hfilt⟩ := Algebra.pointedEtale_small_filtered A K
  let := hsmall
  let := hfilt
  let I := ObjectProperty.FullSubcategory
    (fun T : Over (CommAlgCat.of A K) ↦ Algebra.Etale A T.left)
  let S := CategoryTheory.equivSmallModel.{u} I
  let : IsFiltered (SmallModel.{u} I) := IsFiltered.of_equivalence S
  let B := S.inverse ⋙ Algebra.strictHenselizationPointedDiagram A K
  let hc := P.isColimit.whiskerEquivalence S.symm
  let : HasColimit B := ⟨⟨P.cocone.whisker S.inverse, hc⟩⟩
  let i := (colimit.isColimit B).coconePointUniqueUpToIso hc ≪≫ P.identification
  let ea : ↥(colimit B) ≃ₐ[A] C := CommAlgCat.algEquivOfIso i
  let ei : ↥(colimit B) ≃+* C := ea.toRingEquiv
  let : IsLocalRing ↥(colimit B) := ei.symm.isLocalRing
  have hA (p : Ideal A) [p.IsPrime] :
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
    ⟨inferInstance, isIntegrallyClosed_of_isLocalization _ p.primeCompl
      p.primeCompl_le_nonZeroDivisors⟩
  obtain ⟨⟨hd, hn⟩, hinj⟩ :=
    CommAlgCat.isDomain_isIntegrallyClosed_injective_of_etale_colimit A hA B
      (fun j ↦ (S.inverse.obj j).property)
  let : IsDomain ↥(colimit B) := hd
  let : IsIntegrallyClosed ↥(colimit B) := hn
  refine ⟨⟨MulEquiv.isDomain _ ei.symm.toMulEquiv,
    IsIntegrallyClosed.of_equiv ei⟩, ?_⟩
  intro a b hab
  apply hinj
  apply ea.injective
  simpa only [AlgEquiv.commutes] using hab

/-- Steps 1 and 9: fraction-ring compatibility and the two conjugacies. -/
private theorem presentation_embeddings
    (A F K C Ω : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C]
    [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} A K C) :
    (∃ i : FractionRing C →+* Ω, ∀ r : A,
      i (algebraMap C (FractionRing C) (algebraMap A C r)) =
        algebraMap F Ω (algebraMap A F r)) ∧
    ∀ i j : FractionRing C →+* Ω,
      (∀ r : A, i (algebraMap C (FractionRing C) (algebraMap A C r)) =
        algebraMap F Ω (algebraMap A F r)) →
      (∀ r : A, j (algebraMap C (FractionRing C) (algebraMap A C r)) =
        algebraMap F Ω (algebraMap A F r)) →
      ∃ g : Ω ≃ₐ[F] Ω, ∀ h : Ω ≃ₐ[F] Ω,
        h ∈ fixingSubgroup (Ω ≃ₐ[F] Ω) (Set.range i) ↔
          g⁻¹ * h * g ∈ fixingSubgroup (Ω ≃ₐ[F] Ω) (Set.range j) := by
  classical
  obtain ⟨hCnormal, hinj⟩ := presentation_normal A K C P
  let := hCnormal.1
  let E := FractionRing C
  have hAE : Function.Injective (algebraMap A E) :=
    (IsFractionRing.injective C E).comp hinj
  let k : F →+* E := IsFractionRing.lift hAE
  let : Algebra F E := k.toAlgebra
  have hk (r : A) : k (algebraMap A F r) = algebraMap A E r :=
    IsFractionRing.lift_algebraMap hAE r
  let : IsScalarTower A F E := IsScalarTower.of_algebraMap_eq (fun r ↦ (hk r).symm)
  let : Algebra A Ω := ((algebraMap F Ω).comp (algebraMap A F)).toAlgebra
  let : IsScalarTower A F Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hAΩ : Function.Injective (algebraMap A Ω) :=
    (algebraMap F Ω).injective.comp (IsFractionRing.injective A F)
  have hAB : Function.Injective (algebraMap A (integralClosure A Ω)) := by
    intro a b hab
    apply hAΩ
    exact congrArg (fun z : integralClosure A Ω ↦ (z : Ω)) hab
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := integralClosure A Ω) (IsLocalRing.maximalIdeal A)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hAB]; exact bot_le)
  let := hQmax
  have hC : Algebra.IsStrictHenselization A K C :=
    ⟨P.cocone, ⟨P.isColimit⟩, ⟨P.identification⟩⟩
  obtain ⟨_, ⟨e⟩, ⟨_, _, e₀, _, _, hI, hconj⟩, _⟩ :=
    _root_.strictLocalInertiaIdentification.{u, u, u} A F K C E Ω hC ⟨inferInstance, inferInstance⟩
      hCnormal hinj Q hQ
  constructor
  · refine ⟨e.toRingHom, fun r ↦ ?_⟩
    change e (algebraMap A E r) = _
    rw [← hk, ← AlgHom.commutes e]
    rfl
  · intro i j hi hj
    have heq (f : E →+* Ω)
        (hf : ∀ r : A, f (algebraMap C E (algebraMap A C r)) =
          algebraMap F Ω (algebraMap A F r)) :
        f.comp k = algebraMap F Ω := by
      apply IsFractionRing.ringHom_ext (A := A)
      intro r
      simpa only [RingHom.comp_apply, hk,
        IsScalarTower.algebraMap_apply A C E] using hf r
    let ei : E →ₐ[F] Ω := { __ := i, commutes' := RingHom.congr_fun (heq i hi) }
    let ej : E →ₐ[F] Ω := { __ := j, commutes' := RingHom.congr_fun (heq j hj) }
    obtain ⟨gi, hgi⟩ := hconj ei
    obtain ⟨gj, hgj⟩ := hconj ej
    refine ⟨gi * gj⁻¹, fun h ↦ ?_⟩
    have hsecond := hgj (gj * (gi⁻¹ * h * gi) * gj⁻¹)
    rw [show gj⁻¹ * (gj * (gi⁻¹ * h * gi) * gj⁻¹) * gj = gi⁻¹ * h * gi by
      group] at hsecond
    have hh := (hgi h).trans hsecond.symm
    simpa only [IntermediateField.fixingSubgroup, AlgHom.coe_fieldRange,
      mul_inv_rev, inv_inv, mul_assoc, ei, ej, AlgHom.coe_mk] using hh


/-- Step 2: transport the specified action along the canonical geometric fibre map. -/
private theorem generic_map
    (X : Scheme.{u}) [IsIntegral X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (Ω Ωbar : Type u) [Field Ω] [Field Ωbar]
    [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]
    [Algebra Ω Ωbar] [IsAlgClosure Ω Ωbar] [IsAlgClosed Ωbar]
    [Algebra X.functionField Ωbar] [IsScalarTower X.functionField Ω Ωbar]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ Q, MulAction G ((fiber
      (pointOfAlgebra (K := X.functionField) Ωbar X.fromSpecFunctionField)).obj Q)]
    [IsFundamentalGroup (fiber
      (pointOfAlgebra (K := X.functionField) Ωbar X.fromSpecFunctionField)) G] :
    ∃ a : (Ω ≃ₐ[X.functionField] Ω) →* G,
      (∀ (σ : Ω ≃ₐ[X.functionField] Ω) (σbar : Ωbar ≃ₐ[X.functionField] Ωbar),
        (∀ z : Ω, σbar (algebraMap Ω Ωbar z) = algebraMap Ω Ωbar (σ z)) →
        a σ = galoisToFundamentalGroup (K := X.functionField)
          X.fromSpecFunctionField (Iso.refl _) G σbar) ∧
      Continuous a ∧ Function.Surjective a ∧
      ∀ (L : IntermediateField X.functionField Ω)
        [FiniteDimensional X.functionField L] [IsGalois X.functionField L],
        (∃ ρ : G →* (L ≃ₐ[X.functionField] L), Continuous ρ ∧
          ∀ (σ : Ω ≃ₐ[X.functionField] Ω) (z : L), (ρ (a σ) z : Ω) = σ z) ↔
          IsUnramified (X.fromNormalizationIn L) := by
  classical
  let : IsSepClosed Ω := IsSepClosure.sep_closed X.functionField
  let s := pointOfAlgebra (K := X.functionField) Ω X.fromSpecFunctionField
  let t := pointOfAlgebra (K := X.functionField) Ωbar X.fromSpecFunctionField
  let β := Spec.map (CommRingCat.ofHom (algebraMap Ω Ωbar))
  have hβ : β ≫ s = t := by
    dsimp [β, s, t, pointOfAlgebra]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext z
    exact (IsScalarTower.algebraMap_apply X.functionField Ω Ωbar z).symm
  let η : fiber s ⟶ fiber t := {
    app := fun P ↦ FintypeCat.homMk fun z ↦ fiberMk t P (β ≫ z.left) (by
      rw [Category.assoc, fiber_left_comp, hβ])
    naturality := by
      intro P Q f
      ext z
      apply fiber_ext
      change (β ≫ z.left) ≫ f.hom.left = β ≫ (z.left ≫ f.hom.left)
      exact Category.assoc _ _ _ }
  let : IsIso η := isIso_of_fiberFunctor (fiber s) (fiber t) η
  let τ := asIso η
  let act (P : X.FiniteEtale) : MulAction G ((fiber s).obj P) := {
    smul := fun g z ↦ τ.inv.app P (g • τ.hom.app P z)
    one_smul := fun z ↦ by
      change τ.inv.app P ((1 : G) • τ.hom.app P z) = z
      rw [one_smul]
      exact ConcreteCategory.congr_hom (τ.hom_inv_id_app P) z
    mul_smul := fun g h z ↦ by
      change τ.inv.app P ((g * h) • τ.hom.app P z) =
        τ.inv.app P (g • τ.hom.app P (τ.inv.app P (h • τ.hom.app P z)))
      rw [mul_smul]
      congr 1
      congr 1
      exact (ConcreteCategory.congr_hom (τ.inv_hom_id_app P) _).symm }
  let := act
  have hact (P : X.FiniteEtale) (g : G) (z : (fiber s).obj P) :
      τ.hom.app P (g • z) = g • τ.hom.app P z := by
    exact ConcreteCategory.congr_hom (τ.inv_hom_id_app P) _
  let : IsFundamentalGroup (fiber s) G := {
    naturality := by
      intro g P Q f z
      apply (ConcreteCategory.bijective_of_isIso (τ.hom.app Q)).1
      rw [hact]
      have hn (w : (fiber s).obj P) :
          τ.hom.app Q ((fiber s).map f w) = (fiber t).map f (τ.hom.app P w) :=
        ConcreteCategory.congr_hom (τ.hom.naturality f) w
      rw [hn, hn, hact, IsNaturalSMul.naturality]
    transitive_of_isGalois := by
      intro P hP
      let := hP
      let := IsFundamentalGroup.transitive_of_isGalois (F := fiber t) (G := G) P
      refine ⟨fun z w ↦ ?_⟩
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (τ.hom.app P z) (τ.hom.app P w)
      exact ⟨g, (ConcreteCategory.bijective_of_isIso (τ.hom.app P)).1 ((hact P g z).trans hg)⟩
    continuous_smul := by
      intro P
      let := IsFundamentalGroup.continuous_smul (F := fiber t) (G := G) P
      refine ⟨?_⟩
      change Continuous fun p : G × (fiber s).obj P ↦
        τ.inv.app P (p.1 • τ.hom.app P p.2)
      exact continuous_of_discreteTopology.comp
        (continuous_smul.comp (continuous_fst.prodMk
          (continuous_of_discreteTopology.comp continuous_snd)))
    non_trivial' := by
      intro g hg
      apply IsFundamentalGroup.non_trivial (F := fiber t) g
      intro P z
      obtain ⟨w, rfl⟩ := (ConcreteCategory.bijective_of_isIso (τ.hom.app P)).2 z
      rw [← hact, hg] }
  obtain ⟨_, q, hq, hcont, hsurj, _, hcriterion⟩ :=
    normal_unramified_galois_presentation hX (Ω := Ω) G
  refine ⟨q, ?_, hcont, hsurj, hcriterion⟩
  intro σ σbar hext
  apply (toAutMulEquiv (fiber t) G).injective
  ext P z
  obtain ⟨w, rfl⟩ := (ConcreteCategory.bijective_of_isIso (τ.hom.app P)).2 z
  change q σ • τ.hom.app P w = _
  rw [← hact]
  change q = galoisToFundamentalGroup (K := X.functionField)
    X.fromSpecFunctionField (Iso.refl _) G at hq
  have hqsmul : q σ • w =
      (galoisToAut (K := X.functionField) X.fromSpecFunctionField σ).hom.app P w := by
    rw [hq]
    exact galoisToFundamentalGroup_smul (K := X.functionField)
      X.fromSpecFunctionField (Iso.refl _) G σ P w
  rw [hqsmul]
  have hbarsmul := galoisToFundamentalGroup_smul (K := X.functionField) X.fromSpecFunctionField
    (Iso.refl _) G σbar P (τ.hom.app P w)
  change _ = (galoisToFundamentalGroup (K := X.functionField)
    X.fromSpecFunctionField (Iso.refl _) G σbar) • τ.hom.app P w
  change (galoisToFundamentalGroup (K := X.functionField)
    X.fromSpecFunctionField (Iso.refl _) G σbar) • τ.hom.app P w =
    (galoisToAut (K := X.functionField) X.fromSpecFunctionField σbar).hom.app P
      (τ.hom.app P w) at hbarsmul
  rw [hbarsmul]
  apply fiber_ext
  change β ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ w.left =
    Spec.map (CommRingCat.ofHom σbar.toRingHom) ≫ β ≫ w.left
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext z
  exact (hext z).symm

/-- Step 3: use the splitting clause of the stated local fundamental-group sequence. -/
private theorem presentation_splitting
    (A K C : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} A K C)
    (F E : Type u) [Field F] [Field E]
    [Algebra A F] [IsFractionRing A F] [Algebra C E] [IsFractionRing C E]
    (i : F →+* E)
    (hi : i.comp (algebraMap A F) = (algebraMap C E).comp (algebraMap A C))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of E)) :
    ∀ Y : (Spec (.of A)).FiniteEtale, ∃ n : ℕ,
      Nonempty (Over.mk (pullback.snd Y.obj.hom
        (Spec.map (CommRingCat.ofHom i) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A F)))) ≅
        Over.mk (Sigma.desc (fun _ : Fin n ↦ 𝟙 (Spec (.of E))))) := by
  classical
  obtain ⟨G_E, aE, hE⟩ := exists_isFundamentalGroup s
  let := aE
  let := hE
  let sF := s ≫ Spec.map (CommRingCat.ofHom i)
  obtain ⟨G_F, aF, hF⟩ := exists_isFundamentalGroup sF
  let := aF
  let := hF
  let sA := sF ≫ Spec.map (CommRingCat.ofHom (algebraMap A F))
  obtain ⟨G_A, aA, hA⟩ := exists_isFundamentalGroup sA
  let := aA
  let := hA
  let b := fundamentalGroupMap (pullbackFiberIso (Spec.map (CommRingCat.ofHom i)) s) G_E G_F
  let c := fundamentalGroupMap
    (pullbackFiberIso (Spec.map (CommRingCat.ofHom (algebraMap A F))) sF) G_F G_A
  exact (localPiOneExactSequence A K C P F E i hi s G_E G_F G_A b c rfl rfl).2.2.2.2.1

/-- Step 3: a point into a split cover selects a single component. -/
private theorem split_cover_invariant
    {B X Y : Scheme.{u}} (b : B ⟶ X) (f : Y ⟶ X) (n : ℕ)
    (e : Over.mk (pullback.snd f b) ≅
      Over.mk (Sigma.desc (fun _ : Fin n ↦ 𝟙 B)))
    {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ B)
    (z : Spec (.of Ω) ⟶ Y) (hz : z ≫ f = t ≫ b)
    (α : Spec (.of Ω) ⟶ Spec (.of Ω)) (hα : α ≫ t = t) : α ≫ z = z := by
  let w := pullback.lift z t hz
  obtain ⟨i, v, hv⟩ := exists_comp_sigmaι_eq_of_subsingleton (w ≫ e.hom.left)
  have hv' : v = t := by
    calc
      v = v ≫ Sigma.ι (fun _ : Fin n ↦ B) i ≫
          Sigma.desc (fun _ : Fin n ↦ 𝟙 B) := by simp
      _ = w ≫ e.hom.left ≫ Sigma.desc (fun _ : Fin n ↦ 𝟙 B) := by
        rw [← Category.assoc, hv, Category.assoc]
      _ = w ≫ pullback.snd f b := congrArg (fun q ↦ w ≫ q) (Over.w e.hom)
      _ = t := pullback.lift_snd _ _ _
  have hw : α ≫ w = w := by
    apply (cancel_mono e.hom.left).mp
    calc
      (α ≫ w) ≫ e.hom.left = α ≫ (v ≫ Sigma.ι (fun _ : Fin n ↦ B) i) := by
        rw [Category.assoc, ← hv]
      _ = v ≫ Sigma.ι (fun _ : Fin n ↦ B) i := by
        rw [hv', ← Category.assoc, hα]
      _ = w ≫ e.hom.left := hv
  have := congrArg (fun q ↦ q ≫ pullback.fst f b) hw
  simpa only [Category.assoc, w, pullback.lift_fst] using this

/-- Step 3: an automorphism fixing the strict-local fraction field fixes every fibre. -/
private theorem presentation_fixes_generic_cover
    (A F K C Ω Ωbar : Type u)
    [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [IsDomain C] [Algebra A C]
    [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
    [Field Ωbar] [IsSepClosed Ωbar] [Algebra Ω Ωbar]
    [Algebra F Ωbar] [IsScalarTower F Ω Ωbar]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} A K C)
    (hinj : Function.Injective (algebraMap A C))
    (i : FractionRing C →+* Ω)
    (hi : ∀ r : A, i (algebraMap C (FractionRing C) (algebraMap A C r)) =
      algebraMap F Ω (algebraMap A F r))
    (X : Scheme.{u}) (a : Spec (.of A) ⟶ X) (η : Spec (.of F) ⟶ X)
    (hη : Spec.map (CommRingCat.ofHom (algebraMap A F)) ≫ a = η)
    (σ : Ω ≃ₐ[F] Ω) (σbar : Ωbar ≃ₐ[F] Ωbar)
    (hext : ∀ z : Ω, σbar (algebraMap Ω Ωbar z) = algebraMap Ω Ωbar (σ z))
    (hσ : σ ∈ fixingSubgroup (Ω ≃ₐ[F] Ω) (Set.range i))
    (Y : X.FiniteEtale) (z : (fiber (pointOfAlgebra Ωbar η)).obj Y) :
    Spec.map (CommRingCat.ofHom σbar.toRingHom) ≫ z.left = z.left := by
  classical
  let E := FractionRing C
  have hAE : Function.Injective (algebraMap A E) :=
    (IsFractionRing.injective C E).comp hinj
  let k : F →+* E := IsFractionRing.lift hAE
  have hk (r : A) : k (algebraMap A F r) = algebraMap A E r :=
    IsFractionRing.lift_algebraMap hAE r
  have hk' : k.comp (algebraMap A F) = (algebraMap C E).comp (algebraMap A C) :=
    RingHom.ext hk
  have hik : i.comp k = algebraMap F Ω := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro r
    change i (k (algebraMap A F r)) = _
    rw [hk, IsScalarTower.algebraMap_apply A C E]
    exact hi r
  let j := (algebraMap Ω Ωbar).comp i
  let tE := Spec.map (CommRingCat.ofHom j)
  let b := Spec.map (CommRingCat.ofHom k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A F))
  let tA := tE ≫ b
  have htF : tE ≫ Spec.map (CommRingCat.ofHom k) =
      Spec.map (CommRingCat.ofHom (algebraMap F Ωbar)) := by
    rw [← Spec.map_comp]
    congr 1
    ext r
    change algebraMap Ω Ωbar (i (k r)) = algebraMap F Ωbar r
    have hik_apply : i (k r) = algebraMap F Ω r := RingHom.congr_fun hik r
    rw [hik_apply, ← IsScalarTower.algebraMap_apply F Ω Ωbar]
  have htA : tA ≫ a = pointOfAlgebra Ωbar η := by
    dsimp only [tA, b]
    rw [Category.assoc, Category.assoc, hη, ← Category.assoc, htF]
  let YA := (pullback a).obj Y
  let zA : Spec (.of Ωbar) ⟶ YA.obj.left :=
    pullback.lift z.left tA ((fiber_left_comp _ z).trans htA.symm)
  obtain ⟨n, ⟨e⟩⟩ := presentation_splitting A K C P F E k hk' tE YA
  have hα : Spec.map (CommRingCat.ofHom σbar.toRingHom) ≫ tE = tE := by
    rw [← Spec.map_comp]
    congr 1
    ext r
    change σbar (algebraMap Ω Ωbar (i r)) = algebraMap Ω Ωbar (i r)
    rw [hext]
    congr 1
    exact (mem_fixingSubgroup_iff _).mp hσ (i r) ⟨r, rfl⟩
  have hzA : zA ≫ YA.obj.hom = tE ≫ b := pullback.lift_snd _ _ _
  have h := split_cover_invariant b YA.obj.hom n e tE zA hzA
    (Spec.map (CommRingCat.ofHom σbar.toRingHom)) hα
  have hp := congrArg (fun q ↦ q ≫ pullback.fst Y.obj.hom a) h
  simpa only [Category.assoc, zA, pullback.lift_fst] using hp


/-- Steps 4 and 8: finite Galois quotients detect the closed normal subgroup. -/
private theorem kernel_eq_inertia_closure
    (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (a : (Ω ≃ₐ[F] Ω) →* G) (ha : Continuous a)
    (ι : Type w) (J : ι → Subgroup (Ω ≃ₐ[F] Ω))
    (hkill : ∀ i, J i ≤ a.ker)
    (hfactor : ∀ (L : IntermediateField F Ω)
      [FiniteDimensional F L] [IsGalois F L],
      (∀ i, J i ≤ L.fixingSubgroup) →
      ∃ ρ : G →* (L ≃ₐ[F] L),
        ∀ (σ : Ω ≃ₐ[F] Ω) (z : L), (ρ (a σ) z : Ω) = σ z) :
    a.ker = (Subgroup.normalClosure (⋃ i, (J i : Set (Ω ≃ₐ[F] Ω)))).topologicalClosure := by
  classical
  let N := (Subgroup.normalClosure (⋃ i, (J i : Set (Ω ≃ₐ[F] Ω)))).topologicalClosure
  have hNclosed : IsClosed (N : Set (Ω ≃ₐ[F] Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  let : N.Normal := Subgroup.is_normal_topologicalClosure _
  have hJN (i : ι) : J i ≤ N := by
    intro σ hσ
    apply Subgroup.le_topologicalClosure
    exact Subgroup.subset_normalClosure (Set.mem_iUnion.mpr ⟨i, hσ⟩)
  have hNker : N ≤ a.ker := by
    apply Subgroup.topologicalClosure_minimal
    · apply Subgroup.normalClosure_le_normal
      intro σ hσ
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hσ
      exact hkill i hi
    · exact isClosed_eq ha continuous_const
  have hfinite (W : Subgroup (Ω ≃ₐ[F] Ω)) [W.Normal]
      (hW : IsOpen (W : Set (Ω ≃ₐ[F] Ω))) (hNW : N ≤ W) : a.ker ≤ W := by
    obtain ⟨hfin, _, hfix, _⟩ :=
      (openSubgroup_fixedField_finite_separable.{u, u, u} F Ω).1 W hW
    let L := IntermediateField.fixedField W
    let : FiniteDimensional F L := hfin
    have hLfix : L.fixingSubgroup = W := hfix
    let : L.fixingSubgroup.Normal := hLfix.symm ▸ (inferInstance : W.Normal)
    let : IsGalois F L := (InfiniteGalois.normal_iff_isGalois L).mp inferInstance
    obtain ⟨ρ, hρ⟩ := hfactor L (fun i ↦ by rw [hLfix]; exact (hJN i).trans hNW)
    intro σ hσ
    rw [← hLfix, IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    have hσ' : a σ = 1 := hσ
    have heq := hρ σ ⟨z, hz⟩
    simpa only [hσ', map_one, AlgEquiv.one_apply, Subtype.coe_mk] using heq.symm
  apply le_antisymm ?_ hNker
  intro σ hσ
  by_contra hnot
  let U : Set (Ω ≃ₐ[F] Ω) := (σ • (N : Set (Ω ≃ₐ[F] Ω)))ᶜ
  have hU : IsOpen U :=
    ((Homeomorph.mulLeft σ).isClosedMap _ hNclosed).isOpen_compl
  have h1 : 1 ∈ U := by
    rintro ⟨n, hn, (heq : σ * n = 1)⟩
    rw [← inv_eq_iff_mul_eq_one] at heq
    exact hnot (inv_mem_iff.mp (heq ▸ hn))
  obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  let W : Subgroup (Ω ≃ₐ[F] Ω) := (V : Subgroup (Ω ≃ₐ[F] Ω)) ⊔ N
  have hWopen : IsOpen (W : Set (Ω ≃ₐ[F] Ω)) :=
    Subgroup.isOpen_mono le_sup_left V.isOpen
  have hσW : σ ∈ W := hfinite W hWopen le_sup_right hσ
  obtain ⟨v, hv, n, hn, hvn⟩ := Subgroup.mem_sup_of_normal_left.mp hσW
  rw [← eq_mul_inv_iff_mul_eq] at hvn
  exact hV (hvn ▸ hv) (mem_leftCoset σ (inv_mem_iff.mpr hn))


/-- Step 5: lift a prime and restrict its inertia down the Galois tower. -/
private theorem affine_inertia_trivial
    (X : Scheme.{u}) [IsIntegral X]
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]
    (K H : X → Type u) [∀ x, Field (K x)]
    [∀ x, Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x)) (K x)]
    [∀ x, IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)) (K x)]
    [∀ x, Algebra (X.presheaf.stalk x) (K x)]
    [∀ x, IsScalarTower (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) (K x)]
    [∀ x, CommRing (H x)] [∀ x, IsDomain (H x)]
    [∀ x, Algebra (X.presheaf.stalk x) (H x)]
    (P : ∀ x, Algebra.StrictHenselizationPresentationIn.{u, u}
      (X.presheaf.stalk x) (K x) (H x))
    (hinj : ∀ x, Function.Injective (algebraMap (X.presheaf.stalk x) (H x)))
    (j : (x : X) → FractionRing (H x) →+* Ω)
    (hj : ∀ x (r : X.presheaf.stalk x),
      j x (algebraMap (H x) (FractionRing (H x)) (algebraMap _ (H x) r)) =
        algebraMap X.functionField Ω (algebraMap _ X.functionField r))
    (L : IntermediateField X.functionField Ω)
    [FiniteDimensional X.functionField L] [IsGalois X.functionField L]
    (hfix : ∀ x, fixingSubgroup (Ω ≃ₐ[X.functionField] Ω) (Set.range (j x)) ≤
      L.fixingSubgroup)
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    [Algebra Γ(X, U) Ω] [IsScalarTower Γ(X, U) X.functionField Ω]
    [Algebra Γ(X, U) L] [IsScalarTower Γ(X, U) X.functionField L]
    [IsScalarTower Γ(X, U) L Ω]
    (q : Ideal (integralClosure Γ(X, U) L)) [q.IsPrime] :
    q.inertia (L ≃ₐ[X.functionField] L) = ⊥ := by
  classical
  let A := Γ(X, U)
  let : IsFractionRing A X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsIntegrallyClosed A := X.isIntegrallyClosed_of_isIntegrallyClosed_stalk hnormal U
  let B := integralClosure A L
  let D := integralClosure A Ω
  let f : B →ₐ[A] D := (IsScalarTower.toAlgHom A L Ω).mapIntegralClosure
  let : Algebra B D := f.toRingHom.toAlgebra
  let : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  let : Algebra.IsIntegral B D := Algebra.IsIntegral.tower_top (R := A) (S := B) (T := D)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply (algebraMap L Ω).injective
    exact congrArg (fun z : D ↦ (z : Ω)) hab
  obtain ⟨r, hrprime, hrq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (R := B) (S := D) q
    (by
      change RingHom.ker f.toRingHom ≤ q
      rw [(RingHom.injective_iff_ker_eq_bot f.toRingHom).mp hf]
      exact bot_le)
  change r.comap f.toRingHom = q at hrq
  let := hrprime
  let x : X := (Spec.map (CommRingCat.ofHom (algebraMap A D)) ≫ hU.fromSpec)
    ⟨r, hrprime⟩
  let Aₓ := X.presheaf.stalk x
  let E := FractionRing (H x)
  have hAE : Function.Injective (algebraMap Aₓ E) :=
    (IsFractionRing.injective (H x) E).comp (hinj x)
  let k : X.functionField →+* E := IsFractionRing.lift hAE
  let : Algebra X.functionField E := k.toAlgebra
  have hk (a : Aₓ) : k (algebraMap Aₓ X.functionField a) = algebraMap Aₓ E a :=
    IsFractionRing.lift_algebraMap hAE a
  let : IsScalarTower Aₓ X.functionField E :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (hk a).symm
  have hjk : (j x).comp k = algebraMap X.functionField Ω := by
    apply IsFractionRing.ringHom_ext (A := Aₓ)
    intro a
    change j x (k (algebraMap Aₓ X.functionField a)) = _
    rw [hk, IsScalarTower.algebraMap_apply Aₓ (H x) E]
    exact hj x a
  let e : E →ₐ[X.functionField] Ω := { __ := j x, commutes' := RingHom.congr_fun hjk }
  obtain ⟨g, hg⟩ := X.strictLocalInertiaIdentification hnormal Ω x (K x) (H x) (P x)
    E e U hU ⟨r, hrprime⟩ rfl
  have hR : r.inertia (Ω ≃ₐ[X.functionField] Ω) ≤ L.fixingSubgroup := by
    intro σ hσ
    have hmem := hfix x ((hg σ).mp hσ)
    have hnorm := (InfiniteGalois.normal_iff_isGalois L).mpr
      (inferInstance : IsGalois X.functionField L)
    simpa [mul_assoc] using hnorm.conj_mem _ hmem g
  have hmap := Ideal.separableClosure_inertia_map (F := X.functionField)
    (L := L) (M := Ω) r
  rw [hrq] at hmap
  rw [← hmap, Subgroup.map_eq_bot_iff, L.restrictNormalHom_ker]
  exact hR

/-- Step 6: transport the inertia-invariant neighbourhoods through explicit ring isomorphisms. -/
private theorem etale_of_trivial_inertia
    (A R : Type u) [CommRing A] [CommRing R] [Algebra A R] [FaithfulSMul A R]
    (G : Type v) [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G A R]
    [Algebra.IsInvariant A R G]
    (htriv : ∀ q : Ideal R, q.IsPrime → q.inertia G = ⊥) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
  classical
  let C := FixedPoints.subring R G
  let f : A →+* C := (algebraMap A R).codRestrict C (fun a g ↦ smul_algebraMap g a)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply FaithfulSMul.algebraMap_injective A R
      exact congrArg (fun z : C ↦ (z : R)) hab
    · intro c
      obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) c.val c.property
      exact ⟨a, Subtype.ext ha⟩
  let eA : A ≃+* C := RingEquiv.ofBijective f hf
  let ψ := Spec.map (CommRingCat.ofHom eA.toRingHom)
  let fX := Spec.map (CommRingCat.ofHom (algebraMap A R))
  let : IsIso ψ := by
    change IsIso (Spec.map eA.toCommRingCatIso.hom)
    infer_instance
  have hU (q : Spec (.of R)) : ∃ (Z : Scheme.{u}) (b : Z ⟶ Spec (.of R)),
      IsOpenImmersion b ∧ q ∈ Set.range b ∧ Etale (b ≫ fX) := by
    let I := FixedPoints.subring R (q.asIdeal.inertia G)
    have hI : Function.Bijective I.subtype := by
      refine ⟨Subtype.val_injective, fun r ↦ ⟨⟨r, ?_⟩, rfl⟩⟩
      intro g
      have hg : g.val = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← htriv q.asIdeal q.isPrime]
        exact g.property
      change g.val • r = r
      rw [hg, one_smul]
    let eI : I ≃+* R := RingEquiv.ofBijective I.subtype hI
    let φ := Spec.map (CommRingCat.ofHom eI.toRingHom)
    let inc : C →+* I := Subring.inclusion (fun _ hx g ↦ hx g.val)
    let : IsIso φ := by
      change IsIso (Spec.map eI.toCommRingCatIso.hom)
      infer_instance
    have hdiag : φ ≫ Spec.map (CommRingCat.ofHom inc) ≫ ψ = fX := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
    have hcalc : inv φ ≫ fX = Spec.map (CommRingCat.ofHom inc) ≫ ψ := by
      rw [← hdiag, IsIso.inv_hom_id_assoc]
    obtain ⟨U, hmem, het⟩ := Ideal.exists_etale_open_inertiaInvariants R G q.asIdeal
    refine ⟨U.toScheme, U.ι ≫ inv φ, inferInstance, ?_, ?_⟩
    · refine ⟨⟨φ q, hmem⟩, ?_⟩
      change inv φ (φ q) = q
      exact congrArg (fun f : Spec (.of R) ⟶ Spec (.of R) ↦ f q)
        (IsIso.hom_inv_id φ)
    · let := het
      rw [Category.assoc, hcalc, ← Category.assoc]
      infer_instance
  choose Z b hopen hmem het using hU
  let (q : Spec (.of R)) : IsOpenImmersion (b q) := hopen q
  let 𝒰 : (Spec (.of R)).OpenCover := {
    I₀ := Spec (.of R)
    X := Z
    f := b
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun q ↦ ⟨q, hmem q⟩, inferInstance⟩ }
  exact IsZariskiLocalAtSource.of_openCover (P := @Etale) 𝒰 het

/-- Step 6: the full fixed subring is the integrally closed base ring. -/
private theorem integralClosure_etale_of_trivial_inertia
    (A F L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field F] [Field L] [Algebra A F] [IsFractionRing A F]
    [Algebra F L] [Algebra A L] [IsScalarTower A F L]
    [FiniteDimensional F L] [IsGalois F L]
    (htriv : ∀ q : Ideal (integralClosure A L), q.IsPrime →
      q.inertia (L ≃ₐ[F] L) = ⊥) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L)))) := by
  let R := integralClosure A L
  let : Algebra.IsInvariant A R (L ≃ₐ[F] L) := {
    isInvariant := by
      intro b hb
      have hfixed : (b : L) ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[F] L)) := by
        intro g
        exact congrArg (fun r : R ↦ (r : L)) (hb g.val)
      rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hfixed
      obtain ⟨z, hz⟩ := hfixed
      have hint : _root_.IsIntegral A z := by
        apply (isIntegral_algebraMap_iff (algebraMap F L).injective).mp
        rw [hz]
        exact b.property
      obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
      refine ⟨a, Subtype.ext ?_⟩
      change algebraMap A L a = b.val
      rw [IsScalarTower.algebraMap_apply A F L, ha, hz] }
  let : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective A R).mpr (by
    intro a b hab
    apply IsFractionRing.injective A F
    apply (algebraMap F L).injective
    have hab' : algebraMap A L a = algebraMap A L b :=
      congrArg (fun z : R ↦ (z : L)) hab
    simpa only [← IsScalarTower.algebraMap_apply A F L] using hab')
  exact etale_of_trivial_inertia A R (L ≃ₐ[F] L) htriv

/-- Step 6: glue the affine integral-closure calculation over the normalization. -/
private theorem normalization_etale_of_affine_integralClosure
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (h : ∀ (U : X.Opens) [Nonempty U] (_ : IsAffineOpen U)
      [Algebra Γ(X, U) L] [IsScalarTower Γ(X, U) X.functionField L],
      Algebra.Etale Γ(X, U) (integralClosure Γ(X, U) L)) :
    Etale (X.fromNormalizationIn L) := by
  classical
  let φ := X.fromSpecOfAlgebraFunctionField L
  have hlocal (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
      Etale ((φ.fromNormalization ⁻¹ᵁ U).ι ≫ φ.fromNormalization) := by
    let := (φ.app U).hom.toAlgebra
    have hηU : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
        obtain ⟨x⟩ := (inferInstance : Nonempty U)
        exact ⟨x.val, trivial, x.property⟩)
    have hxU : φ (IsLocalRing.closedPoint L) ∈ U := by
      rw [Hom.comp_apply, Spec_closedPoint]
      convert hηU
      exact fromSpecStalk_closedPoint
    have hφU : φ ⁻¹ᵁ U = ⊤ := preimage_eq_top_of_closedPoint_mem φ hxU
    let θ : Γ(Spec (.of L), φ ⁻¹ᵁ U) ≅ .of L :=
      (Spec (.of L)).presheaf.mapIso (eqToIso hφU.symm).op ≪≫ Scheme.ΓSpecIso (.of L)
    have hθφ : φ.app U ≫ θ.hom =
        X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L) := by
      have h1 := germ_stalkClosedPointTo φ U hxU
      have h2 := germ_stalkClosedPointTo_Spec_fromSpecStalk
        (CommRingCat.ofHom (algebraMap X.functionField L)) U hxU
      exact h1.symm.trans h2
    let : Algebra Γ(X, U) L := (φ.app U ≫ θ.hom).hom.toAlgebra
    let : IsScalarTower Γ(X, U) X.functionField L :=
      IsScalarTower.of_algebraMap_eq' (by
        change (φ.app U ≫ θ.hom).hom = _
        rw [hθφ]
        rfl)
    let e : Γ(Spec (.of L), φ ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] L :=
      { θ.commRingCatIsoToRingEquiv with commutes' := fun _ ↦ rfl }
    let := h U hU
    have het : Algebra.Etale Γ(X, U)
        (integralClosure Γ(X, U) Γ(Spec (.of L), φ ⁻¹ᵁ U)) :=
      Algebra.Etale.of_equiv e.mapIntegralClosure.symm
    exact φ.etale_fromNormalization_of_isAffineOpen hU het
  have hnhd (y : φ.normalization) : ∃ U : X.Opens,
      φ.fromNormalization y ∈ U ∧ Etale ((φ.fromNormalization ⁻¹ᵁ U).ι ≫
        φ.fromNormalization) := by
    obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (U := ⊤) (x := φ.fromNormalization y) trivial
    let : Nonempty U := ⟨⟨φ.fromNormalization y, hy⟩⟩
    exact ⟨U, hy, hlocal U hU⟩
  choose U hy het using hnhd
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale)
    (fun y ↦ φ.fromNormalization ⁻¹ᵁ U y) ?_ het
  apply top_unique
  intro y _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩

/-- Steps 5 and 6: combine the affine calculation for every nonempty affine chart. -/
private theorem normalization_unramified_of_local_fixing
    (X : Scheme.{u}) [IsIntegral X]
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]
    (K H : X → Type u) [∀ x, Field (K x)]
    [∀ x, Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x)) (K x)]
    [∀ x, IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)) (K x)]
    [∀ x, Algebra (X.presheaf.stalk x) (K x)]
    [∀ x, IsScalarTower (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) (K x)]
    [∀ x, CommRing (H x)] [∀ x, IsDomain (H x)]
    [∀ x, Algebra (X.presheaf.stalk x) (H x)]
    (P : ∀ x, Algebra.StrictHenselizationPresentationIn.{u, u}
      (X.presheaf.stalk x) (K x) (H x))
    (hinj : ∀ x, Function.Injective (algebraMap (X.presheaf.stalk x) (H x)))
    (j : (x : X) → FractionRing (H x) →+* Ω)
    (hj : ∀ x (r : X.presheaf.stalk x),
      j x (algebraMap (H x) (FractionRing (H x)) (algebraMap _ (H x) r)) =
        algebraMap X.functionField Ω (algebraMap _ X.functionField r))
    (L : IntermediateField X.functionField Ω)
    [FiniteDimensional X.functionField L] [IsGalois X.functionField L]
    (hfix : ∀ x, fixingSubgroup (Ω ≃ₐ[X.functionField] Ω) (Set.range (j x)) ≤
      L.fixingSubgroup)
    : IsUnramified (X.fromNormalizationIn L) := by
  classical
  have het : Etale (X.fromNormalizationIn L) :=
    normalization_etale_of_affine_integralClosure X L (by
      intro U _ hU _ _
      let A := Γ(X, U)
      let : Algebra A Ω :=
        ((algebraMap X.functionField Ω).comp (algebraMap A X.functionField)).toAlgebra
      let : IsScalarTower A X.functionField Ω :=
        IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      let : IsScalarTower A L Ω := IsScalarTower.of_algebraMap_eq (fun r ↦ by
        change algebraMap X.functionField Ω (algebraMap A X.functionField r) = _
        rw [IsScalarTower.algebraMap_apply A X.functionField L,
          ← IsScalarTower.algebraMap_apply X.functionField L Ω])
      let : IsFractionRing A X.functionField :=
        functionField_isFractionRing_of_isAffineOpen X U hU
      let : IsIntegrallyClosed A :=
        X.isIntegrallyClosed_of_isIntegrallyClosed_stalk hnormal U
      have htriv (q : Ideal (integralClosure A L)) (hq : q.IsPrime) :
          q.inertia (L ≃ₐ[X.functionField] L) = ⊥ := by
        let := hq
        exact affine_inertia_trivial X hnormal Ω K H P hinj j hj L hfix U hU q
      have hspec := integralClosure_etale_of_trivial_inertia A X.functionField L htriv
      exact RingHom.etale_algebraMap.mp
        ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hspec))
  let := het
  exact ⟨inferInstance, inferInstance⟩

/-- The generic-point map is a continuous surjection whose kernel is the closed normal
closure of the local strict-henselian fixing groups, for every compatible choice of
embeddings. Each strict henselization is a normal domain and admits such an embedding.
The last clause gives conjugacy of the subgroups for any two compatible embeddings;
the kernel formula for every family gives independence of their closed normal closure.

Source: Stacks Project, Tag 0BTD (1) = (3), Tag 0BSW and Tag 0BNE
(blueprint: lem-dl-a1-normal-integral-generic-inertia).

`K x` is the chosen separable closure of the stalk residue field, and `P x` is precisely
its strict-henselization colimit presentation. `Ωbar` is an algebraic closure
containing the separable closure `Ω`. The equation with `galoisToFundamentalGroup` specifies the
map by the existing geometric generic fibre action of every extending automorphism.
`G` is an arbitrary small profinite model of this fibre-automorphism group,
with its specified fundamental action, following the project convention.
Such extensions exist uniquely, including over imperfect fields, since the remaining
extension from the separable closure to the algebraic closure is purely inseparable.
No arbitrary homomorphism or extra local normality hypothesis is supplied.

Proof (the nine steps recorded in the DAG node):
1. For each point x apply the pointed-etale filteredness, locality and etale-colimit normal-domain
   theorems to its specified strict-henselization presentation. This gives a normal domain H_x and
   injectivity of the stalk map. Construct the algebra F -> Frac(H_x) using the fraction-ring
   lift. Lying over in the integral closure of the normal local stalk supplies a maximal prime;
   the ring strict-local inertia theorem then gives an F-embedding Frac(H_x) -> Omega.
   Compatibility is checked on the stalk by the fraction-ring universal property.
   Uses: def-sc-ring-strict-henselization, lem-sc-pointed-etale-small-filtered, lem-sc-ring-
   strict-henselization-local-maximal-ideal, lem-weil-pbc-etale-colimit-normal-local-domain, lem-
   dl-a1-strict-local-inertia-identification, lem-weil-pbc-integral-injective-lying-over.
2. Precomposition by Spec(Omegabar) -> Spec(Omega) gives the canonical natural transformation
   between generic fibre functors. The existing source-library theorem isIso_of_fiberFunctor makes
   it an isomorphism. Transport the given G-action through this specified isomorphism and verify
   naturality, transitivity, continuity and faithfulness. Apply the normal-unramified Galois
   presentation for Omega to obtain a continuous surjection a and its finite-Galois factorization
   criterion. The commuting square for an automorphism of Omegabar extending sigma identifies
   a(sigma) with the stipulated geometric generic action. Thus the original G and its original
   action are retained.
   Uses: lem-dl-a1-normal-unramified-galois-presentation.
3. For a strict-local fraction field E_x, choose existing small fundamental-group models at its
   specified geometric point and invoke the local-pi1 sequence's splitting clause. Every finite
   etale cover of the stalk splits after base change to E_x. A geometric point into a split finite
   coproduct selects one component since Spec(Omegabar) is a singleton; hence any automorphism
   fixing the map to E_x fixes that point. Extend sigma in Aut(Omega/F) to Omegabar by the proved
   automorphism-extension theorem. If sigma fixes the embedded E_x, the extension fixes the map to
   E_x. Pulling an arbitrary finite etale cover of X back to the stalk and using the generic-point
   factorization therefore shows that a(sigma) acts trivially on every fibre. Faithfulness gives
   a(sigma)=1. Closedness of the kernel follows from continuity and the Hausdorff property of G,
   obtained from its homeomorphism to the fibre-automorphism group. Its normality gives N <=
   ker(a).
   Uses: lem-dl-a1-local-pi1-exact-sequence, lem-galois-pi1-functoriality, lem-exc-galois-
   automorphism-extension.
4. For an open normal subgroup W containing N, the open-subgroup fixed-field theorem supplies the
   finite separable intermediate field L=Omega^W and L.fixingSubgroup=W. Mathlib's infinite Galois
   correspondence identifies normality of this fixing subgroup with L/F being Galois. It suffices
   to factor restriction to Gal(L/F) through a.
   Uses: lem-exc-etale-open-subgroup-fixed-field.
5. On every nonempty affine open Spec(A), put B=integralClosure(A,L), D=integralClosure(A,Omega).
   The inclusion B -> D is injective and integral, so each prime q of B lifts to a prime r of D.
   The scheme strict-local inertia identification identifies the inertia of r, up to conjugacy,
   with the fixing subgroup of the chosen E_x-embedding at its image x. This fixing subgroup lies
   in L.fixingSubgroup; the latter is normal, so the inertia of r does as well. The separable-
   closure inertia-tower image equality and the kernel of restriction then imply that the inertia
   of q in Gal(L/F) is trivial.
   Uses: lem-weil-pbc-integral-injective-lying-over, lem-dl-a1-strict-local-inertia-
   identification, lem-dl-a1-galois-tower-inertia-surjective.
6. The fixed subring of B under Gal(L/F) is A: a fixed element belongs to F by finite Galois
   theory and then to A by integral closedness. Construct the resulting ring isomorphism
   explicitly. For each prime q, trivial inertia gives an explicit isomorphism B^(I_q) ~= B by the
   subtype map. Transport the open etale neighbourhood furnished by the inertia-invariants theorem
   through these two ring isomorphisms. These neighbourhoods cover Spec(B), so A -> B is etale.
   Apply the affine description of relative normalization and its etale restriction lemma, then
   glue over affine opens of X. This proves that X.normalizationIn(L) -> X is etale and hence
   unramified; no finiteness of normalization is assumed.
   Uses: lem-dl-a1-inertia-invariants-etale, lem-weil-pbc-relative-normalization.
7. Apply the finite-Galois factorization criterion of the normal-unramified presentation directly
   to this particular L and the unramified normalization just proved. Obtain rho:G -> Gal(L/F)
   with rho(a(sigma))(z)=sigma(z) for all z in L. Therefore every element of ker(a) fixes L and
   belongs to W. A separate extension of deck automorphisms is unnecessary.
   Uses: lem-dl-a1-normal-unramified-galois-presentation.
8. For sigma outside the closed normal subgroup N, the complement of the left coset sigma*N is an
   open neighbourhood of 1. Mathlib's profinite open-normal neighbourhood basis supplies an open
   normal V inside this complement. The subgroup W=V*N is open and normal and contains N, so the
   previous step puts every element of ker(a) in W. If sigma lay in ker(a), write sigma=v*n with v
   in V and n in N. Then v=sigma*n^(-1) lies in sigma*N, contradicting the choice of V. Thus
   ker(a) <= N, proving equality.
9. Convert any two stalk-compatible ring embeddings i,j of Frac(H_x) to F-algebra homomorphisms
   using the fraction-ring universal property. The strict-local inertia theorem conjugates each of
   their fixing subgroups to that of a common distinguished embedding. Compose the two
   conjugacies, with conjugating element g_i*g_j^(-1), and verify the displayed equivalence by
   group identities. The kernel equality was proved for every compatible family, so its closed
   normal closure is independent of the choices.
   Uses: lem-dl-a1-strict-local-inertia-identification.
-/
theorem normalIntegral_generic_inertia
    (X : Scheme.{u}) [IsIntegral X]
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (Ω Ωbar : Type u) [Field Ω] [Field Ωbar]
    [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]
    [Algebra Ω Ωbar] [IsAlgClosure Ω Ωbar] [IsAlgClosed Ωbar]
    [Algebra X.functionField Ωbar] [IsScalarTower X.functionField Ω Ωbar]
    (K H : X → Type u) [∀ x, Field (K x)]
    [∀ x, Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x)) (K x)]
    [∀ x, IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)) (K x)]
    [∀ x, Algebra (X.presheaf.stalk x) (K x)]
    [∀ x, IsScalarTower (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) (K x)]
    [∀ x, CommRing (H x)] [∀ x, Algebra (X.presheaf.stalk x) (H x)]
    (P : ∀ x, Algebra.StrictHenselizationPresentationIn.{u, u}
      (X.presheaf.stalk x) (K x) (H x))
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ Q, MulAction G ((fiber
      (pointOfAlgebra (K := X.functionField) Ωbar X.fromSpecFunctionField)).obj Q)]
    [IsFundamentalGroup (fiber
      (pointOfAlgebra (K := X.functionField) Ωbar X.fromSpecFunctionField)) G] :
    (∀ x, IsDomain (H x) ∧ IsIntegrallyClosed (H x) ∧
      ∃ i : FractionRing (H x) →+* Ω, Function.Injective i ∧
        ∀ r : X.presheaf.stalk x,
          i (algebraMap (H x) (FractionRing (H x)) (algebraMap _ (H x) r)) =
            algebraMap X.functionField Ω (algebraMap _ X.functionField r)) ∧
    ∃ a : (Ω ≃ₐ[X.functionField] Ω) →* G,
      (∀ (σ : Ω ≃ₐ[X.functionField] Ω) (σbar : Ωbar ≃ₐ[X.functionField] Ωbar),
        (∀ z : Ω, σbar (algebraMap Ω Ωbar z) = algebraMap Ω Ωbar (σ z)) →
          a σ = galoisToFundamentalGroup (K := X.functionField)
            X.fromSpecFunctionField (Iso.refl _) G σbar) ∧
      Continuous a ∧ Function.Surjective a ∧
      ∀ j : (x : X) → FractionRing (H x) →+* Ω,
        (∀ x, Function.Injective (j x)) →
        (∀ (x : X) (r : X.presheaf.stalk x),
          j x (algebraMap (H x) (FractionRing (H x)) (algebraMap _ (H x) r)) =
            algebraMap X.functionField Ω (algebraMap _ X.functionField r)) →
        a.ker = (Subgroup.normalClosure (⋃ x,
          (fixingSubgroup (Ω ≃ₐ[X.functionField] Ω) (Set.range (j x)) :
            Set (Ω ≃ₐ[X.functionField] Ω)))).topologicalClosure ∧
        ∀ (x : X) (i : FractionRing (H x) →+* Ω), Function.Injective i →
          (∀ r : X.presheaf.stalk x,
            i (algebraMap (H x) (FractionRing (H x)) (algebraMap _ (H x) r)) =
              algebraMap X.functionField Ω (algebraMap _ X.functionField r)) →
          ∃ g : Ω ≃ₐ[X.functionField] Ω,
            ∀ h : Ω ≃ₐ[X.functionField] Ω,
              h ∈ fixingSubgroup (Ω ≃ₐ[X.functionField] Ω) (Set.range i) ↔
                g⁻¹ * h * g ∈ fixingSubgroup (Ω ≃ₐ[X.functionField] Ω)
                  (Set.range (j x)) := by
  classical
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := hnormal x
  have hn (x : X) := presentation_normal (X.presheaf.stalk x) (K x) (H x) (P x)
  let (x : X) : IsDomain (H x) := (hn x).1.1
  have hemb (x : X) := presentation_embeddings (X.presheaf.stalk x)
    X.functionField (K x) (H x) Ω (P x)
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := (hemb x).1
    exact ⟨(hn x).1.1, (hn x).1.2, i, i.injective, hi⟩
  obtain ⟨a, hchar, ha, hsurj, hcriterion⟩ := generic_map X hnormal Ω Ωbar G
  refine ⟨a, hchar, ha, hsurj, ?_⟩
  intro j _ hj
  refine ⟨?_, fun x i _ hi ↦ (hemb x).2 i (j x) hi (hj x)⟩
  let : T2Space G := (toAutHomeo (fiber
    (pointOfAlgebra (K := X.functionField) Ωbar X.fromSpecFunctionField)) G).symm.t2Space
  apply kernel_eq_inertia_closure X.functionField Ω G a ha X
    (fun x ↦ fixingSubgroup (Ω ≃ₐ[X.functionField] Ω) (Set.range (j x)))
  · intro x σ hσ
    obtain ⟨σbar, hσbar⟩ := exists_algEquiv_extending_separableClosure
      X.functionField Ω Ωbar σ
    have hext (z : Ω) : σbar (algebraMap Ω Ωbar z) = algebraMap Ω Ωbar (σ z) :=
      (RingHom.congr_fun hσbar z).symm
    change a σ = 1
    rw [hchar σ σbar hext]
    apply IsFundamentalGroup.non_trivial (F := fiber
      (pointOfAlgebra (K := X.functionField) Ωbar X.fromSpecFunctionField))
    intro Y z
    have hsmul := galoisToFundamentalGroup_smul (K := X.functionField)
      X.fromSpecFunctionField (Iso.refl _) G σbar Y z
    change (galoisToFundamentalGroup (K := X.functionField)
      X.fromSpecFunctionField (Iso.refl _) G σbar) • z =
      (galoisToAut (K := X.functionField) X.fromSpecFunctionField σbar).hom.app Y z
      at hsmul
    rw [hsmul]
    apply fiber_ext
    change Spec.map (CommRingCat.ofHom σbar.toRingHom) ≫ z.left = z.left
    apply presentation_fixes_generic_cover (X.presheaf.stalk x) X.functionField
      (K x) (H x) Ω Ωbar (P x) (hn x).2 (j x) (hj x) X
      (X.fromSpecStalk x) X.fromSpecFunctionField ?_ σ σbar hext hσ Y z
    exact SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
  · intro L _ _ hfix
    have hunram := normalization_unramified_of_local_fixing X hnormal Ω K H P
      (fun x ↦ (hn x).2) j hj L hfix
    obtain ⟨ρ, _, hρ⟩ := (hcriterion L).mpr hunram
    exact ⟨ρ, hρ⟩

end AlgebraicGeometry.Scheme.FiniteEtale
