/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.StrictLocalClosedChartModels
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Canonical strict-local maps in closed affine quotient charts

Source: Stacks Project, Etale Cohomology, Tag 04HX and the paragraph after Tag 03PS;
Algebra, Tag 04GU (blueprint: lem-trf-strict-local-closed-chart-map).

The record below packages all the simultaneous chart and residue compatibilities,
including the local factorization through the actual ideal quotient.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The ring data in the closed-chart comparison, with their characterizing equations.
`S` is the local quotient of `R`; `α` and `β` are the structural chart maps. The record
retains presentations, so its residue maps are those induced by the pointed colimits.
Every algebra structure in the record is constrained by the displayed base equations.
Source: Stacks Project, Tags 04HX, 04GU and the elementary ideal-quotient construction
(blueprint: lem-trf-strict-local-closed-chart-map). -/
structure StrictLocalClosedChartRingData
    (A : Type u) [CommRing A] (I p : Ideal A) [p.IsPrime]
    (R S C D K Ω : Type u) [CommRing R] [IsLocalRing R] [Algebra A R]
    [CommRing S] [CommRing C] [CommRing D] [Field K] [Field Ω]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    (π : R →+* S) (α : A →+* C) (β : A ⧸ I →+* D)
    (ι : K →+* Ω) (εC : C →+* Ω) (εD : D →+* Ω) (uCD : C →+* D) where
  /-- The local structure on the localized quotient. -/
  [localS : IsLocalRing S]
  /-- Its algebra structure from the affine quotient chart. -/
  [chartS : Algebra (A ⧸ I) S]
  /-- The quotient chart and local quotient have the same map from A. -/
  chartS_eq : (algebraMap (A ⧸ I) S).comp (Ideal.Quotient.mk I) =
    π.comp (algebraMap A R)
  /-- S is the localization of A/I at the image of the complement of p. -/
  localizationS : IsLocalization (p.primeCompl.map (Ideal.Quotient.mk I)) S
  /-- The local structure on the ambient strict-local ring. -/
  [localC : IsLocalRing C]
  /-- The local structure on the closed-subscheme strict-local ring. -/
  [localD : IsLocalRing D]
  /-- The ambient local-base algebra structure. -/
  [baseC : Algebra R C]
  /-- The closed-subscheme local-base algebra structure. -/
  [baseD : Algebra S D]
  /-- The first structure extends the actual ambient chart map. -/
  baseC_eq : (algebraMap R C).comp (algebraMap A R) = α
  /-- The second structure extends the actual quotient chart map. -/
  baseD_eq : (algebraMap S D).comp (algebraMap (A ⧸ I) S) = β
  /-- The ambient structure map is local. -/
  baseC_local : IsLocalHom (algebraMap R C)
  /-- The closed-subscheme structure map is local. -/
  baseD_local : IsLocalHom (algebraMap S D)
  /-- The ambient action on the common separable closure. -/
  [closureR : Algebra R K]
  /-- The ambient action factors through its given residue embedding. -/
  [towerR : IsScalarTower R (IsLocalRing.ResidueField R) K]
  /-- The common separable closure as an S-algebra. -/
  [closureS : Algebra S K]
  /-- Its algebra structure from the residue field of S. -/
  [residueS : Algebra (IsLocalRing.ResidueField S) K]
  /-- It is a separable closure of that residue field. -/
  [separableS : IsSepClosure (IsLocalRing.ResidueField S) K]
  /-- The S-action factors through its residue field. -/
  [towerS : IsScalarTower S (IsLocalRing.ResidueField S) K]
  /-- Both local bases act through the same embedding into K. -/
  closureS_eq : (algebraMap S K).comp π = algebraMap R K
  /-- The defining pointed-etale colimit of the ambient ring. -/
  presentationC : Algebra.StrictHenselizationPresentationIn.{u, u} R K C
  /-- The defining pointed-etale colimit of the closed-subscheme ring. -/
  presentationD : Algebra.StrictHenselizationPresentationIn.{u, u} S K D
  /-- Strict henselianity of the ambient ring. -/
  strictC : IsStrictlyHenselianLocalRing C
  /-- Strict henselianity of the closed-subscheme ring. -/
  strictD : IsStrictlyHenselianLocalRing D
  /-- Its specified residue identification with K. -/
  residueC : IsLocalRing.ResidueField C ≃+* K
  /-- The other specified residue identification with the same K. -/
  residueD : IsLocalRing.ResidueField D ≃+* K
  /-- The identification is induced by the ambient pointed colimit. -/
  residueC_eq : residueC.toRingHom.comp (IsLocalRing.residue C) = presentationC.residueMap
  /-- The other identification is induced by the closed pointed colimit. -/
  residueD_eq : residueD.toRingHom.comp (IsLocalRing.residue D) = presentationD.residueMap
  /-- The ambient geometric evaluation is the specified residue map into Ω. -/
  evaluationC : ι.comp presentationC.residueMap = εC
  /-- The closed geometric evaluation is the specified residue map into Ω. -/
  evaluationD : ι.comp presentationD.residueMap = εD
  /-- The base residue embedding is the specified one. -/
  residueC_base : presentationC.residueMap.comp (algebraMap R C) = algebraMap R K
  /-- The quotient-base residue embedding is the specified one. -/
  residueD_base : presentationD.residueMap.comp (algebraMap S D) = algebraMap S K
  /-- Locality of the prescribed canonical map. -/
  map_local : IsLocalHom uCD
  /-- Its R-algebra equation, with D acted on through R to S. -/
  map_base : uCD.comp (algebraMap R C) = (algebraMap S D).comp π
  /-- Its residue map is the identity of the common K. -/
  map_residue : presentationD.residueMap.comp uCD = presentationC.residueMap
  /-- The extended chart ideal is annihilated. -/
  ideal_killed : I.map α ≤ RingHom.ker uCD
  /-- The induced S-algebra structure on the actual quotient Q = C/IC. -/
  [quotientAlgebra : Algebra S (C ⧸ I.map α)]
  /-- This action is induced by the ambient R-action. -/
  quotientAlgebra_eq : (algebraMap S (C ⧸ I.map α)).comp π =
    (Ideal.Quotient.mk (I.map α)).comp (algebraMap R C)
  /-- The local structure on Q. -/
  [localQ : IsLocalRing (C ⧸ I.map α)]
  /-- The induced S-algebra homomorphism. -/
  desc : (C ⧸ I.map α) →ₐ[S] D
  /-- It factors the prescribed map. -/
  desc_eq : desc.toRingHom.comp (Ideal.Quotient.mk (I.map α)) = uCD
  /-- It is the unique S-algebra map with this factorization. -/
  desc_unique : ∀ v : (C ⧸ I.map α) →ₐ[S] D,
    v.toRingHom.comp (Ideal.Quotient.mk (I.map α)) = uCD → v = desc
  /-- The factor map is local. -/
  desc_local : IsLocalHom desc.toRingHom
  /-- Its maximal-ideal inverse image is the image of the ambient maximal ideal. -/
  maximalIdeal_comap : (IsLocalRing.maximalIdeal D).comap desc.toRingHom =
    (IsLocalRing.maximalIdeal C).map (Ideal.Quotient.mk (I.map α))
  /-- That image is exactly the maximal ideal of Q. -/
  maximalIdeal_quotient :
    (IsLocalRing.maximalIdeal C).map (Ideal.Quotient.mk (I.map α)) =
      IsLocalRing.maximalIdeal (C ⧸ I.map α)

/-- The canonical strict-local map has simultaneous quotient-chart models, with the
same separable residue closure, and descends uniquely and locally through IC.
The pullback square says that the chosen quotient chart is exactly the inverse image
of the ambient affine open. The equation for xA specifies the prime and its geometric
residue embedding. The map in the ring-data record is the full-faithful Spec preimage
of the existing canonical strict-local morphism, so it is not an arbitrary map.
Source: Stacks Project, Etale Cohomology, Tag 04HX and the paragraph after Tag 03PS;
Algebra, Tag 04GU (blueprint: lem-trf-strict-local-closed-chart-map).

Proof:
1. Use lem-weil-pbc-strict-henselization-triples over R and S and the common K.
A pointed etale map to K is the same as its kernel prime and induced residue embedding,
with matching morphisms. Thus the triple colimits are the pointed presentations of
 def-sc-ring-strict-henselization. Apply lem-exc-affine-strict-local-ring-comparison to
the two affine opens. It identifies their chart maps, geometric evaluations and
strictly henselian local structures. Elements outside p become units, so
lem-weil-pbc-ring-localization-universal-property extends the chart maps uniquely to
the local bases; the comparison isomorphisms respect these extensions.
2. Functoriality gives the structural square for the prescribed map. Cancel the open
immersion and use affine faithfulness to identify its two A-maps. Localization
uniqueness gives the R-algebra equation. The residue identifications of functoriality
are those from evaluation: they agree on each pointed-neighbourhood colimit leg,
hence by colimit universality agree globally. Functoriality therefore gives id_K.
3. The chart equation kills each generator of IC, hence all finite sums of their
multiples. The quotient universal property defines the induced S-action and map
Q to D. Surjectivity of C to Q proves uniqueness of the S-algebra factorization.
4. Locality gives u inverse(m_D) = m_C, so IC is contained in m_C. The image of m_C
is maximal in Q; every element outside it lifts to a unit of C by
lem-weil-pbc-local-ring-unit-criterion, hence is a unit in Q. This is its unique
maximal ideal. Pulling m_D back along the factor map gives exactly that ideal. -/
theorem strictLocalClosedChartMap
    {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (A : CommRingCat.{u}) (I : Ideal A)
    (j : Spec A ⟶ W) [IsOpenImmersion j]
    (k : Spec (.of (A ⧸ I)) ⟶ Z) [IsOpenImmersion k]
    (hsquare : IsPullback k (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) i j)
    (x : Spec (.of Ω) ⟶ Spec (.of (A ⧸ I))) (p : Spec A)
    [Algebra p.asIdeal.ResidueField Ω]
    (hx : x ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      Spec.map ((Spec.residueFieldIso A p).hom ≫
        CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField Ω)) ≫
          (Spec A).fromSpecResidueField p) :
    ∃ (α : A →+* strictHenselizationRing ((x ≫ k) ≫ i))
      (β : (A ⧸ I) →+* strictHenselizationRing (x ≫ k)),
      Spec.map (CommRingCat.ofHom α) ≫ j =
        strictHenselizationStructuralMap ((x ≫ k) ≫ i) ∧
      Spec.map (CommRingCat.ofHom β) ≫ k = strictHenselizationStructuralMap (x ≫ k) ∧
      Nonempty (StrictLocalClosedChartRingData A I p.asIdeal
        (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸ I.map (algebraMap A
          (Localization.AtPrime p.asIdeal)))
        (strictHenselizationRing ((x ≫ k) ≫ i)) (strictHenselizationRing (x ≫ k))
        (separableClosure p.asIdeal.ResidueField Ω) Ω
        (Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime p.asIdeal))))
        α β (separableClosure p.asIdeal.ResidueField Ω).subtype
        (strictHenselizationPointEvaluation ((x ≫ k) ≫ i))
        (strictHenselizationPointEvaluation (x ≫ k))
        (Spec.preimage (strictHenselizationMap i (x ≫ k))).hom) := by
  classical
  obtain ⟨α, β, hα, hβ, ⟨d⟩⟩ := strictLocalClosedChartModels i A I j k hsquare x p hx
  let R := Localization.AtPrime p.asIdeal
  let S := R ⧸ I.map (algebraMap A R)
  let C := strictHenselizationRing ((x ≫ k) ≫ i)
  let D := strictHenselizationRing (x ≫ k)
  let π : R →+* S := Ideal.Quotient.mk (I.map (algebraMap A R))
  let u : C →+* D := (Spec.preimage (strictHenselizationMap i (x ≫ k))).hom
  let := d.localS
  let := d.chartS
  let := d.localC
  let := d.localD
  let := d.baseC
  let := d.baseD
  let := d.closureR
  let := d.towerR
  let := d.closureS
  let := d.residueS
  let := d.separableS
  let := d.towerS
  have hu : Spec.map (CommRingCat.ofHom u) = strictHenselizationMap i (x ≫ k) :=
    Spec.map_preimage _
  have hchart : u.comp α = β.comp (Ideal.Quotient.mk I) := by
    have he : Spec.map (CommRingCat.ofHom α ≫ CommRingCat.ofHom u) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ CommRingCat.ofHom β) := by
      apply (cancel_mono j).mp
      simp only [Spec.map_comp, Category.assoc]
      rw [hα, hu, strictHenselizationMap_over, ← hβ, Category.assoc, hsquare.w]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)
  have hbase : u.comp (algebraMap R C) = (algebraMap S D).comp π := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    rw [RingHom.comp_assoc, d.baseC_eq, hchart]
    rw [RingHom.comp_assoc, ← d.chartS_eq, ← RingHom.comp_assoc, d.baseD_eq]
  have hpoint : (strictHenselizationPointEvaluation (x ≫ k)).comp u =
      strictHenselizationPointEvaluation ((x ≫ k) ≫ i) := by
    have he := (Classical.choose_spec
      (strictHenselizationMap_existsUnique i (x ≫ k))).1.2
    change Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (x ≫ k))) ≫
      strictHenselizationMap i (x ≫ k) = _ at he
    rw [← hu] at he
    have he' : Spec.map (CommRingCat.ofHom u ≫
        CommRingCat.ofHom (strictHenselizationPointEvaluation (x ≫ k))) =
        Spec.map (CommRingCat.ofHom
          (strictHenselizationPointEvaluation ((x ≫ k) ≫ i))) := by
      simpa only [Spec.map_comp] using he
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective he')
  have hres : d.presentationD.residueMap.comp u = d.presentationC.residueMap := by
    apply RingHom.ext
    intro c
    apply (separableClosure p.asIdeal.ResidueField Ω).subtype.injective
    calc
      (separableClosure p.asIdeal.ResidueField Ω).subtype
          (d.presentationD.residueMap (u c)) =
          strictHenselizationPointEvaluation (x ≫ k) (u c) :=
        DFunLike.congr_fun d.evaluationD (u c)
      _ = strictHenselizationPointEvaluation ((x ≫ k) ≫ i) c :=
        DFunLike.congr_fun hpoint c
      _ = (separableClosure p.asIdeal.ResidueField Ω).subtype
          (d.presentationC.residueMap c) := (DFunLike.congr_fun d.evaluationC c).symm
  have hlocal : IsLocalHom u := by
    refine ⟨fun c hc ↦ ?_⟩
    have hzero : d.presentationC.residueMap c ≠ 0 := by
      rw [← DFunLike.congr_fun hres c]
      exact (hc.map d.presentationD.residueMap).ne_zero
    have hzero' : IsLocalRing.residue C c ≠ 0 := by
      intro hz
      apply hzero
      rw [← d.residueC_eq, RingHom.comp_apply, hz, map_zero]
    exact IsLocalRing.notMem_maximalIdeal.mp
      (fun hm ↦ hzero' ((Ideal.Quotient.eq_zero_iff_mem).mpr hm))
  have hkilled : I.map α ≤ RingHom.ker u := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change u (α a) = 0
    rw [← RingHom.comp_apply, hchart, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  let J := I.map α
  let Q := C ⧸ J
  let q : C →+* Q := Ideal.Quotient.mk J
  let v : Q →+* D := Ideal.Quotient.lift J u (fun c hc ↦ hkilled hc)
  have hv : v.comp q = u := Ideal.Quotient.lift_comp_mk _ _ _
  have hkillbase : I.map (algebraMap A R) ≤
      RingHom.ker (q.comp (algebraMap R C)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change q (algebraMap R C (algebraMap A R a)) = 0
    exact (congrArg q (DFunLike.congr_fun d.baseC_eq a)).trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem α ha))
  let σ : S →+* Q := Ideal.Quotient.lift _ (q.comp (algebraMap R C))
    (fun r hr ↦ hkillbase hr)
  let : Algebra S Q := σ.toAlgebra
  have hσ : (algebraMap S Q).comp π = q.comp (algebraMap R C) :=
    Ideal.Quotient.lift_comp_mk _ _ _
  have hvbase : v.comp (algebraMap S Q) = algebraMap S D := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, hσ, ← RingHom.comp_assoc, hv, hbase]
  let desc : Q →ₐ[S] D := { __ := v, commutes' := DFunLike.congr_fun hvbase }
  have : Nontrivial Q := v.domain_nontrivial
  let : IsLocalRing Q := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have hvlocal : IsLocalHom v := by
    refine ⟨fun z hz ↦ ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    apply q.isUnit_map
    apply isUnit_of_map_unit u c
    exact hz
  let := hvlocal
  have hm : (IsLocalRing.maximalIdeal C).map q = IsLocalRing.maximalIdeal Q :=
    IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective
  refine ⟨α, β, hα, hβ, ⟨{
    localS := d.localS
    chartS := d.chartS
    chartS_eq := d.chartS_eq
    localizationS := d.localizationS
    localC := d.localC
    localD := d.localD
    baseC := d.baseC
    baseD := d.baseD
    baseC_eq := d.baseC_eq
    baseD_eq := d.baseD_eq
    baseC_local := d.baseC_local
    baseD_local := d.baseD_local
    closureR := d.closureR
    towerR := d.towerR
    closureS := d.closureS
    residueS := d.residueS
    separableS := d.separableS
    towerS := d.towerS
    closureS_eq := d.closureS_eq
    presentationC := d.presentationC
    presentationD := d.presentationD
    strictC := d.strictC
    strictD := d.strictD
    residueC := d.residueC
    residueD := d.residueD
    residueC_eq := d.residueC_eq
    residueD_eq := d.residueD_eq
    evaluationC := d.evaluationC
    evaluationD := d.evaluationD
    residueC_base := d.residueC_base
    residueD_base := d.residueD_base
    map_local := hlocal
    map_base := hbase
    map_residue := hres
    ideal_killed := hkilled
    quotientAlgebra := inferInstance
    quotientAlgebra_eq := hσ
    localQ := inferInstance
    desc := desc
    desc_eq := hv
    desc_unique := ?_
    desc_local := hvlocal
    maximalIdeal_comap := (IsLocalRing.maximalIdeal_comap v).trans hm.symm
    maximalIdeal_quotient := hm }⟩⟩
  intro w hw
  apply AlgHom.coe_ringHom_injective
  exact Ideal.Quotient.ringHom_ext (hw.trans hv.symm)

end AlgebraicGeometry.Scheme
