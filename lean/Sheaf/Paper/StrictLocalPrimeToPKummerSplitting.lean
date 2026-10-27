/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Limits

import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteStrictHenselianAlgebraEtaleSection
import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.RingTheory.HenselianParameterRootRegularity
import Sheaf.RingTheory.ParameterRootBoundaryDvrs
import Sheaf.RingTheory.KummerNormalizationBoundaryEtale
import Sheaf.AlgebraicGeometry.Morphisms.PulledTorsorNormalizationModel
import Sheaf.AlgebraicGeometry.Morphisms.CodimensionOneNeighbourhoodEtaleExtension
import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleTorsorSectionTrivialization
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.FinRange
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.Algebra.CharP.Invertible

/-! # Strict-local prime-to-p torsors split on a finite parameter-root cover

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IX, Proposition 2.1(i)
and its strict-local normal form, printed pp.133--134.
(blueprint: lem-sfb-strict-local-prime-to-p-kummer-splitting)

The auxiliary constructions spell out the displayed quotient, its puncture, and its
canonical map. Equivariance is expressed on coproduct components and on the first
pullback projection; the over-base equation supplies the second projection.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The displayed simultaneous parameter-root quotient, including the empty variable set.
Source: ILO IX 2.1(i), printed p.133.
(blueprint: lem-sfb-strict-local-prime-to-p-kummer-splitting) -/
abbrev strictLocalParameterRootRing {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) :=
  MvPolynomial (Fin r) R ⧸ Ideal.span
    (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i)))

/-- The boundary puncture, with empty product equal to one.
Source: ILO IX 2.1(i), printed p.133.
(blueprint: lem-sfb-strict-local-prime-to-p-kummer-splitting) -/
noncomputable def strictLocalBoundaryPuncture {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) :
    Scheme.{u} :=
  Spec (.of (Localization.Away (∏ i, t i)))

/-- The root-level puncture localizes at the image of the original boundary product.
Source: ILO IX 2.1(i), printed p.133.
(blueprint: lem-sfb-strict-local-prime-to-p-kummer-splitting) -/
noncomputable def strictLocalParameterRootPuncture {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) : Scheme.{u} :=
  Spec (.of (Localization.Away
    (algebraMap R (strictLocalParameterRootRing t n) (∏ i, t i))))

/-- The map of punctures induced by the quotient's canonical R-algebra structure.
Source: ILO IX 2.1(i), printed p.133.
(blueprint: lem-sfb-strict-local-prime-to-p-kummer-splitting) -/
noncomputable def strictLocalParameterRootMap {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) :
    strictLocalParameterRootPuncture t n ⟶ strictLocalBoundaryPuncture t :=
  Spec.map (CommRingCat.ofHom (IsLocalization.Away.map
    (Localization.Away (∏ i, t i))
    (Localization.Away (algebraMap R (strictLocalParameterRootRing t n) (∏ i, t i)))
    (algebraMap R (strictLocalParameterRootRing t n)) (∏ i, t i)))

@[irreducible] private noncomputable def away_to_field {D F : Type u} [CommRing D] [Field F]
    (φ : D →+* F) (f : D) (hf : φ f ≠ 0) : Localization.Away f →+* F :=
  IsLocalization.Away.lift (S := Localization.Away f) (g := φ) f
    (isUnit_iff_ne_zero.mpr hf)

private theorem away_to_field_eq {D F : Type u} [CommRing D] [Field F]
    (φ : D →+* F) (f : D) (hf : φ f ≠ 0) (x : D) :
    away_to_field φ f hf (algebraMap D (Localization.Away f) x) = φ x := by
  unfold away_to_field
  exact IsLocalization.Away.lift_eq _ _ _

private theorem field_image_ne_zero {D F : Type u} [CommRing D] [CommRing F]
    [Algebra D F] [IsFractionRing D F] {x : D} (hx : x ≠ 0) :
    algebraMap D F x ≠ 0 := (IsFractionRing.to_map_eq_zero_iff).not.mpr hx

private noncomputable def localization_map {D C : Type u} [CommRing D] [CommRing C]
    (φ : D →+* C) (f : D) :
    Localization.Away f →+* Localization.Away (φ f) :=
  IsLocalization.Away.map _ _ φ f

private theorem localization_map_eq {D C : Type u} [CommRing D] [CommRing C]
    (φ : D →+* C) (f x : D) :
    localization_map φ f (algebraMap D (Localization.Away f) x) =
      algebraMap C (Localization.Away (φ f)) (φ x) := by
  unfold localization_map IsLocalization.Away.map
  exact IsLocalization.map_eq _ x

private theorem localization_map_tower {D C : Type u} [CommRing D] [CommRing C]
    [Algebra D C] (f : D) :
    let _ := (localization_map (algebraMap D C) f).toAlgebra
    IsScalarTower D (Localization.Away f) (Localization.Away (algebraMap D C f)) := by
  let _ := (localization_map (algebraMap D C) f).toAlgebra
  apply IsScalarTower.of_algebraMap_eq (R := D) (S := Localization.Away f)
  intro x
  exact (localization_map_eq (algebraMap D C) f x).symm

private theorem away_to_field_tower {D F : Type u} [CommRing D] [Field F]
    [Algebra D F] (f : D) (hf : algebraMap D F f ≠ 0) :
    let _ := (away_to_field (algebraMap D F) f hf).toAlgebra
    IsScalarTower D (Localization.Away f) F := by
  let _ := (away_to_field (algebraMap D F) f hf).toAlgebra
  apply IsScalarTower.of_algebraMap_eq (R := D) (S := Localization.Away f)
  intro x
  exact (away_to_field_eq (algebraMap D F) f hf x).symm

private theorem localization_comp_tower {D C F : Type u}
    [CommRing D] [CommRing C] [Field F] [Algebra D C] [Algebra C F]
    [Algebra D F] [IsScalarTower D C F] (f : D)
    (hf : algebraMap C F (algebraMap D C f) ≠ 0) :
    let _ := (localization_map (algebraMap D C) f).toAlgebra
    let _ := (away_to_field (algebraMap C F) (algebraMap D C f) hf).toAlgebra
    let _ := ((algebraMap (Localization.Away (algebraMap D C f)) F).comp
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap D C f)))).toAlgebra
    IsScalarTower D (Localization.Away f) F := by
  let _ := (localization_map (algebraMap D C) f).toAlgebra
  let _ := (away_to_field (algebraMap C F) (algebraMap D C f) hf).toAlgebra
  let _ := ((algebraMap (Localization.Away (algebraMap D C f)) F).comp
    (algebraMap (Localization.Away f) (Localization.Away (algebraMap D C f)))).toAlgebra
  apply IsScalarTower.of_algebraMap_eq (R := D) (S := Localization.Away f) (A := F)
  intro x
  simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  rw [localization_map_eq, away_to_field_eq]
  exact IsScalarTower.algebraMap_apply D C F x

private theorem localization_tower_compatible {D A K E : Type u}
    [CommRing D] [CommRing A] [CommRing K] [CommRing E]
    [Algebra D A] [Algebra D K] [Algebra D E] [Algebra A K]
    [Algebra A E] [Algebra K E] [IsScalarTower D A K] [IsScalarTower D K E]
    [IsScalarTower D A E] (f : D) [IsLocalization.Away f A] : IsScalarTower A K E := by
  apply IsScalarTower.of_algebraMap_eq (R := A) (S := K) (A := E)
  intro x
  have hmaps : (algebraMap K E).comp (algebraMap A K) = algebraMap A E := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext y
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply D A K,
      ← IsScalarTower.algebraMap_apply D K E, ← IsScalarTower.algebraMap_apply D A E]
  exact (RingHom.congr_fun hmaps x).symm

private theorem parameters_first {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {r : ℕ} (t : Fin r → R) (ht : Function.Injective t)
    (hparams : ∃ s : List R, IsLocalRing.IsRegularSystemOfParameters s ∧
      ∀ i : Fin r, t i ∈ s) :
    ∃ tail : List R, IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail) := by
  classical
  obtain ⟨s, hs, hts⟩ := hparams
  have hsub : List.Subperm (List.ofFn t) s := (List.nodup_ofFn.mpr ht).subperm (by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hts i)
  obtain ⟨l, hl, hsl⟩ := List.subperm_iff.mp hsub
  obtain ⟨tail, htail⟩ := hsl.exists_perm_append
  have hperm : s.Perm (List.ofFn t ++ tail) := hl.symm.trans htail
  refine ⟨tail, ?_, ?_⟩
  · rw [← hs.1]
    exact congrArg Ideal.span (Set.ext fun x ↦ hperm.mem_iff.symm)
  · rw [← hperm.length_eq]
    exact hs.2

private theorem root_regularity {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsStrictlyHenselianLocalRing R] {r : ℕ} (t : Fin r → R) (tail : List R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail))
    (n : ℕ) (hn : 0 < n) :
    ∃ (_ : IsRegularLocalRing (strictLocalParameterRootRing t n)),
      IsStrictlyHenselianLocalRing (strictLocalParameterRootRing t n) ∧
      Function.Injective (algebraMap R (strictLocalParameterRootRing t n)) := by
  let s := List.ofFn t ++ tail
  let d := s.length
  let a : Fin d → R := s.get
  have ha : IsLocalRing.IsRegularSystemOfParameters (List.ofFn a) := by
    simpa only [a, List.ofFn_get] using ht
  have hr : r ≤ d := by simp [d, s]
  have hfront : a ∘ Fin.castLE hr = t := by
    funext i
    simp [a, s, List.get_eq_getElem, List.getElem_append_left, i.isLt]
  obtain ⟨b, hb, hfin, hinj, hint, hreg, hhen, hdom, hdim, hmax, hpar,
    hfib, hres, hstrict, hzero⟩ :=
    Algebra.henselian_parameter_root_regularity R d a ha r hr n hn
  rw [hfront] at hreg hstrict hinj
  exact ⟨hreg, hstrict inferInstance, hinj⟩

private theorem regular_integrallyClosed (R : Type u) [CommRing R] [IsDomain R]
    [IsRegularRing R] : IsIntegrallyClosed R := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro q hq hmax
  exact (IsRegularRing.isNormalRing R q).2

private theorem change_base_iso {X Y Y' Z : Scheme.{u}}
    (p : X ⟶ Z) (j : Y ⟶ Z) (j' : Y' ⟶ Z) (e : Y ≅ Y')
    (he : e.hom ≫ j' = j) :
    ∃ e' : pullback p j ≅ pullback p j',
      e'.hom ≫ pullback.snd p j' = pullback.snd p j ≫ e.hom ∧
      e'.inv ≫ pullback.snd p j = pullback.snd p j' ≫ e.inv := by
  have hei : e.inv ≫ j = j' := by rw [← he]; simp
  let h := pullback.lift (f := p) (g := j') (pullback.fst p j) (pullback.snd p j ≫ e.hom)
    (by simp only [Category.assoc, he, pullback.condition])
  let k := pullback.lift (f := p) (g := j) (pullback.fst p j') (pullback.snd p j' ≫ e.inv)
    (by simp only [Category.assoc, hei, pullback.condition])
  refine ⟨⟨h, k, ?_, ?_⟩, ?_, ?_⟩
  · apply pullback.hom_ext <;> simp [h, k]
  · apply pullback.hom_ext <;> simp [h, k]
  · simp [h]
  · simp [k]

private theorem section_of_finite_etale_model
    (B A : Type u) [CommRing B] [IsDomain B] [IsStrictlyHenselianLocalRing B]
    [CommRing A] [Algebra B A] (f : B) (hf : f ≠ 0) [IsLocalization.Away f A]
    {H Z : Scheme.{u}} (p : H ⟶ Spec (.of B)) [IsFinite p] [Etale p]
    (π : Z ⟶ Spec (.of A)) [Surjective π]
    (e : pullback p (Spec.map (CommRingCat.ofHom (algebraMap B A))) ≅ Z)
    (he : e.hom ≫ π = pullback.snd p
      (Spec.map (CommRingCat.ofHom (algebraMap B A)))) :
    ∃ s : Spec (.of A) ⟶ Z, s ≫ π = 𝟙 _ := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap B A))
  have hinj : Function.Injective (algebraMap B A) :=
    IsLocalization.injective A (Submonoid.powers_le.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
  have : IsDominant j := ⟨by
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap B A)).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le⟩
  have : Surjective (pullback.snd p j) := by
    rw [← he]
    infer_instance
  have : IsDominant (pullback.fst p j ≫ p) := by
    rw [pullback.condition]
    infer_instance
  have : IsDominant p := IsDominant.of_comp (pullback.fst p j) p
  have : Surjective p := surjective_of_isDominant_of_isClosed_range p
    (p.isClosedMap.isClosed_range)
  obtain ⟨σ, hσ⟩ := Scheme.finite_strict_henselian_algebra_etale_section B B p p.surjective
  refine ⟨pullback.lift (j ≫ σ) (𝟙 _) (by simp [hσ, j]) ≫ e.hom, ?_⟩
  simp [Category.assoc, he, j]

open scoped TensorProduct in
private theorem split_from_boundary_index
    (R B : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [IsRegularRing B] [IsStrictlyHenselianLocalRing B]
    [IsIntegrallyClosed B] [Algebra R B] (hRB : Function.Injective (algebraMap R B))
    (f : R) (hf : f ≠ 0) (hfb : algebraMap R B f ≠ 0)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (G : Type v) [Group G] [Finite G]
    (hboundary : ∀ (q : Ideal B) (_ : q.IsPrime),
      q.height = 1 ∧ algebraMap R B f ∈ q →
      ∃ (p : Ideal R) (_ : p.IsPrime) (hc : p = q.comap (algebraMap R B))
        (_ : IsDiscreteValuationRing (Localization.AtPrime p))
        (_ : IsDiscreteValuationRing (Localization.AtPrime q)),
        RingHom.Finite (Localization.localRingHom p q (algebraMap R B) hc) ∧
        Function.Injective (Localization.localRingHom p q (algebraMap R B) hc) ∧
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
          (Localization.localRingHom p q (algebraMap R B) hc) =
          IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n ∧ Nat.card G ∣ n)
    (P : Scheme.GaloisCoverAction G (Spec (.of (Localization.Away f)))) :
    ∃ e : (∐ fun _ : G ↦ Spec (.of (Localization.Away (algebraMap R B f)))) ≅
        pullback P.π (Spec.map (CommRingCat.ofHom (localization_map (algebraMap R B) f))),
      e.hom ≫ pullback.snd P.π
        (Spec.map (CommRingCat.ofHom (localization_map (algebraMap R B) f))) =
          Sigma.desc (fun _ : G ↦ 𝟙 _) ∧
      ∀ g h : G,
        Sigma.ι (fun _ : G ↦ Spec (.of (Localization.Away (algebraMap R B f)))) g ≫
          e.hom ≫ pullback.fst P.π
            (Spec.map (CommRingCat.ofHom (localization_map (algebraMap R B) f))) ≫ P.smul h =
        Sigma.ι (fun _ : G ↦ Spec (.of (Localization.Away (algebraMap R B f)))) (h * g) ≫
          e.hom ≫ pullback.fst P.π
            (Spec.map (CommRingCat.ofHom (localization_map (algebraMap R B) f))) := by
  classical
  let A := Localization.Away f
  let A' := Localization.Away (algebraMap R B f)
  let K := FractionRing R
  let E := FractionRing B
  let : Field K := inferInstance
  let : Field E := inferInstance
  let : CommRing A := inferInstance
  let : CommRing A' := inferInstance
  let : Algebra R A := inferInstance
  let : Algebra B A' := inferInstance
  let : Algebra R A' := inferInstance
  let : Algebra R K := inferInstance
  let : Algebra B E := inferInstance
  let : Algebra R E := inferInstance
  have : IsFractionRing R K := inferInstance
  have : IsFractionRing B E := inferInstance
  have : IsScalarTower R B E := inferInstance
  have : IsScalarTower R B A' := inferInstance
  have hBEf : algebraMap B E (algebraMap R B f) ≠ 0 :=
    @field_image_ne_zero B E _ _ _ _ _ hfb
  let φBE : A' →+* E := away_to_field (algebraMap B E) (algebraMap R B f) hBEf
  let : Algebra A' E := φBE.toAlgebra
  have : IsScalarTower B A' E := away_to_field_tower (F := E) _ hBEf
  let : Algebra A A' := (localization_map (algebraMap R B) f).toAlgebra
  have : IsScalarTower R A A' := localization_map_tower (C := B) f
  let φRK : A →+* K := away_to_field (algebraMap R K) f
    (field_image_ne_zero hf)
  let : Algebra A K := φRK.toAlgebra
  have : IsScalarTower R A K := away_to_field_tower (F := K) _ _
  have hRE : Function.Injective (algebraMap R E) :=
    (IsFractionRing.injective B E).comp hRB
  let : Algebra K E := (IsFractionRing.lift hRE).toAlgebra
  have : IsScalarTower R K E := IsScalarTower.of_algebraMap_eq (R := R) (S := K) (A := E) fun x ↦ by
    change algebraMap R E x = IsFractionRing.lift (K := K) hRE (algebraMap R K x)
    exact (IsFractionRing.lift_algebraMap (K := K) hRE x).symm
  let : Algebra A E := ((algebraMap A' E).comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' E :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := A') (A := E) fun _ ↦ rfl
  have : IsScalarTower R A E := localization_comp_tower (F := E) f hBEf
  have : IsScalarTower A K E := localization_tower_compatible (D := R) (E := E) f
  obtain ⟨S, hSring, hAS, eS, heS, rest⟩ :=
    Scheme.pulled_torsor_normalization_model R B A A' K E hRB f hf G P
  let := hSring
  let := hAS
  obtain ⟨W, ι, hι, hact, rest⟩ := rest
  obtain ⟨eT, eK, heT, heTS, heK, heKS, rest⟩ := rest
  obtain ⟨jcount, acount, hjpos, hapos, L, hLfield, hKL, rest⟩ := rest
  let := hLfield
  let := hKL
  obtain ⟨F, hFfield, hEF, hBF, hBEF, rest⟩ := rest
  let := hFfield
  let := hEF
  let := hBF
  let := hBEF
  obtain ⟨dK, base, prod, fields, hL, hF, hbase, hprod, hfactor, hinjT,
    htotal, hnormalT, hclosedT, hfiniteCa, hfiniteC, hclosure, model, hmodel⟩ := rest
  let : Nonempty (Fin jcount) := ⟨⟨0, hjpos⟩⟩
  let : ∀ j, FiniteDimensional K (L j) := fun j ↦ (hL j).1
  let : ∀ j, IsGalois K (L j) := fun j ↦ (hL j).2.1
  let : ∀ a, FiniteDimensional E (F a) := fun a ↦ (hF a).1
  let : ∀ a, IsGalois E (F a) := fun a ↦ (hF a).2
  let C := ∀ a, integralClosure B (F a)
  let : Module.Finite B C := hfiniteC
  let qmap := Spec.map (CommRingCat.ofHom (algebraMap B C))
  let j := Spec.map (CommRingCat.ofHom (algebraMap B A'))
  let U : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen (algebraMap R B f)
  let eU : Spec (.of A') ≅ U.toScheme := IsOpenImmersion.isoOfRangeEq j U.ι (by
    rw [← Scheme.Hom.coe_opensRange]
    exact (congrArg SetLike.coe
      (Scheme.Hom.opensRange_localizationAway (R := .of B) (algebraMap R B f))).trans
        U.range_ι.symm)
  have heU : eU.hom ≫ U.ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have : Etale W.π := W.etale
  have : IsFinite W.π := W.isFinite
  have : Surjective W.π := W.surjective
  let eTW := eT ≪≫ ι.symm
  have heTW : eTW.hom ≫ W.π = Spec.map
      (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] S))) := by
    simp only [eTW, Iso.trans_hom]
    rw [← hι]
    simpa only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id_assoc] using heT
  let eCW := model ≪≫ eTW
  have heCW : eCW.hom ≫ W.π = pullback.snd qmap j := by
    simp only [eCW, Iso.trans_hom, Category.assoc, heTW, hmodel]
    rfl
  have : Etale (pullback.snd qmap j) := by
    rw [← heCW]
    infer_instance
  obtain ⟨ecU, hecU, hecUi⟩ := change_base_iso qmap j U.ι eU heU
  have : Etale (pullback.snd qmap U.ι) := by
    have hh : ecU.inv ≫ pullback.snd qmap j ≫ eU.hom = pullback.snd qmap U.ι := by
      rw [reassoc_of% hecUi]
      simp
    rw [← hh]
    infer_instance
  have hU : Etale (qmap ∣_ U) := by
    change Etale ((pullbackRestrictIsoRestrict qmap U).inv ≫ _)
    infer_instance
  have hneighbourhood (z : Spec (.of C))
      (hz : (qmap z).asIdeal.height = 1 ∧ algebraMap R B f ∈ (qmap z).asIdeal) :
      ∃ V : (Spec (.of C)).Opens, z ∈ V ∧ Etale (V.ι ≫ qmap) := by
    obtain ⟨p, hp, hc, hVdvr, hAdvr, hfinite', hinjective', hindex, hcard⟩ :=
      hboundary (qmap z).asIdeal (qmap z).isPrime hz
    subst p
    let := hVdvr
    let := hAdvr
    have hdegree : ∀ j, Module.finrank K (L j) ∣ n :=
      fun j ↦ dvd_trans (hL j).2.2 hcard
    have hboundaryEtale : ∃ g : C, g ∉ z.asIdeal ∧ Algebra.Etale B (Localization.Away g) := by
      have hheight' : (qmap z).asIdeal ≠ ⊥ ∧
          ∀ q : Ideal B, q.IsPrime → q < (qmap z).asIdeal → q = ⊥ := by
        refine ⟨Ideal.ne_bot_of_height_eq_one hz.1, ?_⟩
        intro q hq hlt
        have hlt' := Ideal.height_strict_mono_of_isPrime hlt
        rw [hz.1] at hlt'
        exact Ideal.height_eq_zero_iff_eq_bot.mp (Order.lt_one_iff.mp hlt')
      let : ∀ j, Algebra E (L j ⊗[K] E) := fun _ ↦ Algebra.TensorProduct.rightAlgebra
      let dec := (AlgEquiv.piCongrRight fun j ↦
        (Algebra.TensorProduct.commRight K E (L j)).symm).trans fields
      have hh := RingTheory.kummer_normalization_boundary_etale R B hRB K E
        (by ext x; exact (IsScalarTower.algebraMap_apply R K E x).symm) n hn hunit
        (Fin jcount) L hdegree (Fin acount) F
        (fun a ↦ by ext x; exact IsScalarTower.algebraMap_apply B E (F a) x)
        dec (qmap z).asIdeal hheight' hfinite' hinjective' hindex
      exact (hh.2.2.2 z.asIdeal rfl).2.2
    obtain ⟨g, hg, het⟩ := hboundaryEtale
    let V : (Spec (.of C)).Opens := PrimeSpectrum.basicOpen g
    let loc := Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away g)))
    have : Etale (loc ≫ qmap) := by
      rw [← Spec.map_comp]
      apply HasRingHomProperty.Spec_iff.mpr
      exact RingHom.etale_algebraMap.mpr het
    let eV : Spec (.of (Localization.Away g)) ≅ V.toScheme :=
      IsOpenImmersion.isoOfRangeEq loc V.ι (by
        rw [← Scheme.Hom.coe_opensRange]
        exact (congrArg SetLike.coe
          (Scheme.Hom.opensRange_localizationAway (R := .of C) g)).trans V.range_ι.symm)
    have heV : eV.hom ≫ V.ι = loc := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    refine ⟨V, hg, ?_⟩
    have hh : eV.inv ≫ loc ≫ qmap = V.ι ≫ qmap := by rw [← heV]; simp
    rw [← hh]
    infer_instance
  choose V hV hVet using hneighbourhood
  let O := qmap ⁻¹ᵁ U ⊔ ⨆ (z : Spec (.of C)) (hz), V z hz
  obtain ⟨Wopen, hWset, hUW, hWheight, hWfinite, hWet, ⟨H, πH, hHfinite,
    hHet, ⟨eHW, heHW⟩, eHU, heHU⟩, hWcodim⟩ :=
    Scheme.exists_finite_etale_model_of_codimension_one_neighbourhoods B C
      (algebraMap R B f) hfb hU V hV hVet O rfl
  change eHU.hom ≫ pullback.snd qmap U.ι = pullback.snd πH U.ι at heHU
  have := hHfinite
  have := hHet
  obtain ⟨ehU, hehU, hehUi⟩ := change_base_iso πH j U.ι eU heU
  let eHW' := ehU ≪≫ eHU ≪≫ ecU.symm ≪≫ eCW
  have heHW' : eHW'.hom ≫ W.π = pullback.snd πH j := by
    simp only [eHW', Iso.trans_hom, Iso.symm_hom, Category.assoc, heCW]
    rw [hecUi, reassoc_of% heHU, reassoc_of% hehU]
    simp
  obtain ⟨s, hs⟩ := section_of_finite_etale_model B A' (algebraMap R B f) hfb
    πH W.π eHW' heHW'
  obtain ⟨Q, eQ, hcl, heQ, heQi, hdisj, hcover, θ, hθ, hθπ, hθinv,
    hθlocal, hθmul, hθequiv, hθinvequiv⟩ :=
    finite_etale_torsor_section_trivialization G W.π W.smul W.smul_π
      W.one_smul W.mul_smul W.simply_transitive s hs
  change ∃ e : (∐ fun _ : G ↦ Spec (.of A')) ≅
      pullback P.π (Spec.map (CommRingCat.ofHom (algebraMap A A'))), _
  refine ⟨θ ≪≫ ι, ?_, ?_⟩
  · have hh := congrArg (fun k ↦ θ.hom ≫ k) hι
    simp only [RingHom.algebraMap_toAlgebra] at hh
    simpa only [Iso.trans_hom, Category.assoc, hθπ] using hh
  · intro g h
    have hh := congrArg (fun k ↦ k ≫ ι.hom ≫ pullback.fst P.π
      (Spec.map (CommRingCat.ofHom (algebraMap A A')))) (hθequiv h g)
    simp only [RingHom.algebraMap_toAlgebra] at hact hh
    simp only [Category.assoc, hact] at hh
    simpa only [Iso.trans_hom, Category.assoc] using hh

/-- A prime-to-characteristic finite group torsor on a strict-local parameter puncture
has an equivariant trivialization on a finite simultaneous root cover. No connectedness
of the torsor is required, and the empty boundary has the witness n = 1.
Source: ILO IX Proposition 2.1(i), strict-local normal form, printed pp.133--134.
(blueprint: lem-sfb-strict-local-prime-to-p-kummer-splitting)

1. Put $n=|G|$. Since a group contains its identity, $n\geq1$. The hypothesis $p\nmid |G|$ and
primality of $p$ give integers $a,b$ with $an+bp=1$. In the characteristic-$p$ ring $R$ this
reads $(a\cdot1_R)(n\cdot1_R)=1$, so $n$ is a unit in $R$, and $(n,p)=1$.

2. Write $B=R_n$ and extend the specified parameter list to $t_1,\ldots,t_d$, where $d=\dim R$.
Successive applications of [lem-weil-pbc-monic-quotient-free] to $T^n-t_i$ give the unique
expansion $\sum_a c_a x^a$ in $B$, with $0\leq a_i<n$. The successive one-variable presentations
equal the displayed multivariate quotient: both classify tuples satisfying the same equations.
Thus $B$ is finite free over $R$, and its coefficient of $1$ proves injectivity of $R\to B$. It
is integral by [lem-weil-pbc-finite-algebra-is-integral] and Noetherian by
[lem-weil-pbc-finite-algebra-noetherian].

3. Put $k=R/\mathfrak m$. The closed fibre is $B/\mathfrak
mB=k[x_1,\ldots,x_r]/(x_1^n,\ldots,x_r^n)$. Each prime contains all $x_i$, and the quotient by
those elements is $k$, so this nonzero fibre is local with residue field $k$. By
[lem-weil-pbc-finite-over-henselian-local-product], $B$ is a finite product of nonzero henselian
local $R$-algebras, with local structural maps. Each factor has nonzero reduction modulo
$\mathfrak m$. There is exactly one factor, since otherwise the local closed fibre would have a
nontrivial idempotent; in a local ring an idempotent $e$ has either $e$ or $1-e$ invertible and
is $1$ or $0$. Thus $B$ is henselian local with maximal ideal $\mathfrak n=\mathfrak
mB+(x_1,\ldots,x_r)$ and residue field $k$. The latter is separably closed, so $B$ is strictly
henselian by [def-weil-pbc-henselian-terminology].

4. The maximal ideal just obtained is $(x_1,\ldots,x_r,t_{r+1},\ldots,t_d)$, since $t_i=x_i^n$
for $i\leq r$. Its $d$ generators give $\dim B\leq d$ by
[lem-weil-pbc-noetherian-local-dimension-le-generators]. For every chain of primes of $R$,
[pqf-lem-lying-over] lifts its first prime through the injective integral map $R\to B$, and
repeated [pqf-lem-going-up] lifts the remaining chain. The lifted inclusions are strict because
their contractions are distinct. Hence $\dim B\geq\dim R=d$. Thus $B$ is regular local by
[def-weil-regular-scheme], and its displayed generators are a regular system of parameters by
[def-weil-pbc-regular-system-of-parameters]. By [lem-sc-regular-local-domain], both $R$ and $B$
are domains. Put $K=\operatorname{Frac}(R)$ and $E=\operatorname{Frac}(B)$, with the inclusion
induced by $R\hookrightarrow B$.

5. For each $i\leq r$, [lem-weil-pbc-regular-local-generators-regular-sequence], allowing a
permutation of the generators, makes both $R/(t_i)$ and $B/(x_i)$ regular local. They are
domains by [lem-sc-regular-local-domain], and $t_i,x_i$ are nonzerodivisors. Their quotient
presentations give $$B/(x_i)=(R/(t_i))[x_j:j\ne i]/(x_j^n-\bar t_j:j\ne i).$$ Repeated
[lem-weil-pbc-monic-quotient-free] makes this finite free over $R/(t_i)$ with a basis containing
$1$, so that map is injective. Consequently $\mathfrak p_i=(t_i)$ and $\mathfrak q_i=(x_i)$ are
prime and $\mathfrak q_i\cap R=\mathfrak p_i$. The displayed quotient identification follows by
imposing $x_i=0$, which also imposes $t_i=0$, and leaves exactly the other root equations.

6. Set $V_i=R_{\mathfrak p_i}$ and $A_i=B_{\mathfrak q_i}$. By
[lem-sbc-regular-principal-prime-localization-dvr] these are DVRs, with uniformizers $t_i,x_i$.
In fact $B\otimes_R V_i=A_i$. To see this, $B\otimes_R V_i$ is finite over $V_i$, hence integral
by [lem-weil-pbc-finite-algebra-is-integral]. Every maximal ideal contracts to the maximal ideal
of $V_i$ by [lem-weil-pbc-integral-maximal-contracts-maximal] and contains $x_i$ because
$x_i^n=t_i$. Its quotient by $x_i$ is the generic fibre of the finite free domain $B/(x_i)$ over
$R/(t_i)$. That fibre is a nonzero finite-dimensional domain over a field, hence a field:
multiplication by a nonzero element is an injective and therefore surjective linear
endomorphism. There is therefore exactly one maximal ideal, and localization at it is already
this ring, proving the equality with $A_i$. The map $V_i\to A_i$ is finite and injective, has
fraction fields $K\to E$, and satisfies $\mathfrak m_{V_i}A_i=(t_i)=(x_i^n)=\mathfrak
m_{A_i}^n$. Since $A_i$ is a DVR, $\mathfrak q_i$ has height one (prime chains correspond under
localization). Every height-one prime of $B$ containing $f=\prod_i x_i^n$ contains some $x_i$
and hence equals $\mathfrak q_i$.

7. Let $U_B=\operatorname{Spec}B[1/f]$, with exactly the $R$-algebra map in the statement, and
put $P_B=P\times_U U_B$. By [lem-sbc-galois-cover-base-change] it is a finite etale $G$-torsor,
including its action and simple transitivity. Apply [lem-sbc-field-torsor-galois-components]
first to $P_K$, obtaining its generic algebra $\prod_j L_j$, with $L_j/K$ finite Galois and
$[L_j:K]\mid n$. Apply it also to $(P_B)_E$, obtaining a finite product $D=\prod_a F_a$ of
finite Galois, in particular separable, extensions of $E$. These are the actual generic algebras
over their given structure maps. The fibre product gives $D=(\prod_j L_j)\otimes_K
E=\prod_j(L_j\otimes_K E)$; each field factor $F_a$ comes from one $j$, since the orthogonal
idempotents of a finite product map to $0$ or $1$ in a field. The torsor is nonempty, so
$D\ne0$.

8. By [lem-weil-pbc-regular-local-localization] and [lem-weil-pbc-regular-ring-normal], $B$ is a
normal Noetherian domain. For each $a$ let $C_a$ be its integral closure in $F_a$. The
finite-separable integral-closure theorem
[lem-weil-pbc-noetherian-normal-separable-integral-closure-finite] makes $C_a$ finite over $B$.
Put $C=\prod_a C_a$, a finite $B$-algebra embedded in $D$. This finiteness uses separability
over $E=\operatorname{Frac}(B)$, already supplied in step 7, and does not require excellence.
Localizations of $B[1/f]$ are localizations of $B$, so the same regularity and normality
statements also make $B[1/f]$ normal.

9. Write $T$ for the finite $B[1/f]$-algebra of the affine scheme $P_B$, using
[def-weil-finite-integral-morphism]. By [lem-sbc-finite-etale-open-generic-algebra], applied
with $X=\operatorname{Spec}B$ and open $U_B$, $T$ embeds in an $E$-algebra. Hence nonzero base
elements act injectively on $T$, and its canonical generic map $T\to T\otimes_{B[1/f]}E=D$ is
injective. This $D$ is the total quotient ring of $T$: if a nonzerodivisor $z\in T$ had a zero
coordinate in $D$, the nonzero idempotent on that coordinate would be $t/b$ for some $t\in T$
and nonzero base denominator $b$. Then $t\ne0$ but $zt=0$, a contradiction. Thus all
nonzerodivisors of $T$ are units of $D$; conversely every element of $D$ is already a fraction
with a nonzerodivisor base denominator. By [lem-weil-pbc-etale-over-normal-ring-normal], $T$ is
normal. Therefore [lem-weil-pbc-normal-ring-integrally-closed-total] makes it integrally closed
in this very $D$.

10. The finite-algebra theorem [lem-weil-pbc-finite-algebra-is-integral] makes $T$ integral over
$B[1/f]$. An element of $D$ integral over $B[1/f]$ is also integral over $T$, by its same monic
equation, and hence lies in $T$ by step 9. Thus $T$ is exactly the integral closure of $B[1/f]$
in $D$. Integral closure in a finite product is the product of the integral closures: project a
monic equation for one direction; for the other, multiply finitely many monic equations, one
annihilating each coordinate. Apply [lem-weil-pbc-integral-closure-commutes-localization] to
each $C_a\subset F_a$. It identifies $C[1/f]$ with $T$ as subalgebras of $D$, respecting their
structural maps. Consequently $\operatorname{Spec}C$ restricts over $U_B$ to the actual $P_B$.

11. For each $i,j$, apply [lem-sbc-dvr-galois-normalization-ramification-dvd] to the DVR $V_i$,
its fraction field $K$, and $L_j/K$. Step 7 gives the required Galois hypothesis and
$[L_j:K]\mid n$. At every prime above the maximal ideal of $V_i$, both the ramification index
and the residue degree of its integral closure in $L_j$ divide $n$. Step 1 makes $n$ a unit in
$V_i$. These are precisely the two divisibility assumptions in the DVR tame tensor-factor
theorem; no assertion about a multi-divisor cover has been taken from a single-divisor splitting
theorem.

12. Fix $i$ and a factor $F_a$ coming from $L_j$. Since $t_i$ is invertible in $L_j$ and
$A_i[1/t_i]=E$, one has $L_j\otimes_{V_i}A_i=L_j\otimes_K E$. Thus $F_a$ is a maximal field
quotient of the tensor algebra in [lem-sbc-dvr-tame-tensor-factor-unramified], with its
specified right-hand $A_i$-structure. The integral closure $S_a$ of $A_i$ in $F_a$ is finite by
[lem-weil-pbc-noetherian-normal-separable-integral-closure-finite], since $F_a/E$ is finite
separable. Step 6 gives the finite faithful map $V_i\to A_i$ and root index $n$; step 11 gives
both divisibilities, and $n>0$ is a unit. The cited DVR tensor-factor theorem therefore gives
$\Omega_{(S_a)_Q/A_i}=0$ at every prime above $\mathfrak m_{A_i}$. By
[lem-weil-pbc-integral-closure-commutes-localization], $S_a=C_a\otimes_B A_i$. Localizing once
more identifies these local rings with $(C_a)_{\mathfrak Q}$ for $\mathfrak Q$ above $\mathfrak
q_i$. Hence $\Omega_{(C_a)_{\mathfrak Q}/B_{\mathfrak q_i}}=0$ for all such $\mathfrak Q$.

13. The finite $B$-algebra $C$ is of finite type: its module generators also generate it as an
algebra. As $B$ is Noetherian, [lem-weil-pbc-finite-type-noetherian-finite-presentation] makes
it finitely presented. For a prime $\mathfrak Q$ of $C$ over $\mathfrak q_i$, its localization
is the localization of one $C_a\subset F_a$ (the product idempotents select exactly one factor).
This local ring is torsion-free over the DVR $A_i=B_{\mathfrak q_i}$, since it embeds in $F_a$.
A DVR is a PID by [def-sc-discrete-valuation-ring], so
[lem-weil-pbc-pid-torsion-free-module-flat] gives flatness of this local ring over $A_i$. Its
differentials over $A_i$ vanish by step 12. The base-change isomorphism
[lem-weil-pbc-kahler-differentials-base-change], followed by target localization
[lem-weil-pbc-kahler-differentials-localization], identifies this module with
$(\Omega_{C/B})_{\mathfrak Q}$. The equivalence (3)$\Rightarrow$(2) in
[lem-sc-etale-at-prime-flat-unramified-criterion] now gives a basic neighbourhood $D(g)$ of
$\mathfrak Q$ in $\operatorname{Spec}C$ whose map to $\operatorname{Spec}B$ is etale. Thus all
points over every height-one boundary prime have such a neighbourhood.

14. Let $N=\operatorname{Spec}C$. Its restriction over $U_B$ is etale by step 10. Composing with
the open immersion $U_B\hookrightarrow\operatorname{Spec}B$ remains etale by
[lem-weil-pbc-etale-composition-cancellation]. Let $O\subset N$ be the union of that inverse
image and all source-open neighbourhoods obtained in step 13. The restriction
$O\to\operatorname{Spec}B$ is etale, since this is checked on an open cover as in
[def-weil-etale-morphism]. The complement $Z=N\setminus O$ is closed. By
[lem-weil-pbc-finite-closed-map-finite-fibres] its image under the finite map
$N\to\operatorname{Spec}B$ is closed. Set
$W=\operatorname{Spec}B\setminus\operatorname{image}(Z)$. Then $W$ is open, contains $U_B$ and
every height-one point, and $N_W\to W$ is finite etale. Indeed the inverse image of $W$ lies in
$O$ and is a restriction of this finite map. The generic point belongs to $U_B$, since $B$ is a
domain and $f\ne0$.

15. Every point outside $W$ has height at least two, since $W$ contains the generic point and
every height-one point. Its local ring is $B_{\mathfrak q}$, regular by
[lem-weil-pbc-regular-local-localization]. The prime correspondence for localization identifies
its dimension with the supremum of lengths of prime chains below $\mathfrak q$, so that
dimension is at least two. The scheme $\operatorname{Spec}B$ is Noetherian. Apply
[lem-sbc-regular-codimension-two-etale-extension] to the open $W$ and the finite etale morphism
$N_W\to W$. It supplies a finite etale morphism $H\to\operatorname{Spec}B$ and an isomorphism
$H_W\cong N_W$ over $W$. Restricting to the specified open $U_B\subset W$ and using step 10
gives $H_{U_B}\cong P_B$ over $U_B$. This uses the general live extension theorem across a
regular codimension-two boundary, not the dropped finite-normalization purity node.

16. The finite map $H\to\operatorname{Spec}B$ is surjective. Its closed image, by
[lem-weil-pbc-finite-closed-map-finite-fibres], contains the generic point: over that point it
agrees with the nonempty torsor $(P_B)_E$. A closed subset of the spectrum of a domain
containing its generic point is the whole spectrum. The ring $B$ is strictly henselian by step
3. Apply [lem-sbc-finite-strict-henselian-algebra-etale-section] with $H=A=B$ in that node's
notation and with the present scheme $H$ as its etale scheme. It yields a section over
$\operatorname{Spec}B$. Restriction to $U_B$ and the isomorphism $H_{U_B}\cong P_B$ of step 15
give a section $s:U_B\to P_B$ of the actual pullback projection $\pi_n$.

17. Apply [lem-sbc-galois-cover-base-change] along the displayed map $U_n\to U$. Via its
cartesian square, the given pullback $P_n=P\times_U U_n$ carries the pulled-back $G$-action and
is a finite etale $G$-torsor. In particular every geometric fibre has simply transitive
$G$-action. The finite morphism $\pi_n$ is proper by [lem-weil-pbc-finite-proper], and hence
separated by [def-weil-proper-morphism]. For each $g\in G$, the map $s_g=g\cdot s$ is a section:
the action is over $U_n$, so $\pi_n\circ s_g=\pi_n\circ s=\mathrm{id}$.

18. By [lem-weil-pbc-etale-section-clopen-immersion], each $s_g$ identifies $U_n$ with an open
and closed subscheme $Q_g$ of $P_n$. These opens are pairwise disjoint and cover $P_n$. Indeed,
over any geometric point $\bar u$ the torsor condition of [def-sbc-normal-dominant-galois] says
that $g\mapsto g\cdot s(\bar u)$ is bijective onto the geometric fibre. Thus every geometric
point of $P_n$ lies in exactly one $Q_g$. A point in an intersection, or outside their union,
would lift to a geometric point there, contradicting that bijectivity. Consequently the inverse
maps $\pi_n|_{Q_g}:Q_g\to U_n$, followed by the $g$-indexed coprojection, glue on this disjoint
open cover to a morphism $P_n\to\coprod_g U_n$. It is inverse to the morphism $\theta:\coprod_g
U_n\to P_n$ whose $g$-component is $s_g$, since the two composites restrict to identities on
each of these open pieces. The coproduct and its components are those of
[lem-weil-pbc-scheme-coproduct-family].

19. The isomorphism $\theta$ is equivariant for the left regular action on the index set $G$.
For $h,g\in G$ its composite with $h$ on the target, restricted to the $g$-summand, is $h\cdot
s_g=(hg)\cdot s=s_{hg}$, exactly the composite of the $g$-summand with the permutation $g\mapsto
hg$ on the source followed by $\theta$. Equality on coproduct components gives equality of the
morphisms. The inverse of $\theta$ is therefore the required equivariant trivialization. This
argument uses the action law already part of the given torsor.

20. If $r=0$, the presentation has no variables or relations: $R_n=R$, and $f=1$, so
$U_n=\operatorname{Spec}R=U$ with identity structure map for every positive $n$. Steps 2-19
therefore already trivialize $P\to\operatorname{Spec}R$. Choosing $n=1$ gives the identical base
scheme and the same equivariant trivialization, and $(1,p)=1$. The trivial group case also has
$n=|G|=1$ and is included.
-/
theorem strictLocalPrimeToPKummerSplitting
    (p : ℕ) (hp : p.Prime) (R : Type u) [CommRing R] [CharP R p]
    [IsRegularLocalRing R] [IsStrictlyHenselianLocalRing R]
    (r : ℕ) (t : Fin r → R) (ht : Function.Injective t)
    (hparams : ∃ s : List R, IsLocalRing.IsRegularSystemOfParameters s ∧
      ∀ i : Fin r, t i ∈ s)
    (G : Type v) [Group G] [Finite G] (hG : ¬ p ∣ Nat.card G)
    (P : Scheme.GaloisCoverAction G (strictLocalBoundaryPuncture t)) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.Coprime n p ∧ (r = 0 → n = 1) ∧
      ∃ e : (∐ fun _ : G ↦ strictLocalParameterRootPuncture t n) ≅
          pullback P.π (strictLocalParameterRootMap t n),
        e.hom ≫ pullback.snd P.π (strictLocalParameterRootMap t n) =
          Sigma.desc (fun _ : G ↦ 𝟙 (strictLocalParameterRootPuncture t n)) ∧
        ∀ g h : G,
          Sigma.ι (fun _ : G ↦ strictLocalParameterRootPuncture t n) g ≫ e.hom ≫
              pullback.fst P.π (strictLocalParameterRootMap t n) ≫ P.smul h =
            Sigma.ι (fun _ : G ↦ strictLocalParameterRootPuncture t n) (h * g) ≫
              e.hom ≫ pullback.fst P.π (strictLocalParameterRootMap t n) := by
  classical
  obtain ⟨tail, htail⟩ := parameters_first t ht hparams
  let n := if r = 0 then 1 else Nat.card G
  have hn : 0 < n := by
    dsimp [n]
    split_ifs <;> simp [Nat.card_pos]
  have hcop : Nat.Coprime n p := by
    dsimp [n]
    split_ifs
    · exact Nat.coprime_one_left p
    · exact (hp.coprime_iff_not_dvd.mpr hG).symm
  have hunit : IsUnit (n : R) := by
    let := invertibleOfCoprime (R := R) hcop
    exact isUnit_of_invertible _
  refine ⟨n, hn, hcop, by intro hr; simp [n, hr], ?_⟩
  let B := strictLocalParameterRootRing t n
  obtain ⟨hBreg, hBstrict, hRB⟩ := root_regularity t tail htail n hn
  let := hBreg
  let := hBstrict
  have : IsDomain R := inferInstance
  have : IsDomain B := inferInstance
  have : IsRegularRing R :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal R)).2
  have : IsRegularRing B :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal B)).2
  have : IsIntegrallyClosed R := regular_integrallyClosed R
  have : IsIntegrallyClosed B := regular_integrallyClosed B
  let f := ∏ i, t i
  have hf : f ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi hzero
    have hsmul := (Algebra.parameter_root_boundary_quotients t tail htail n hn i).2.2.2.2.1
    have heq : (1 : R) = 0 := hsmul (by simp [hzero])
    exact one_ne_zero heq
  have hfb : algebraMap R B f ≠ 0 := fun h ↦ hf (hRB (h.trans (map_zero _).symm))
  apply split_from_boundary_index R B hRB f hf hfb n hn hunit G ?_ P
  intro q hq hz
  obtain ⟨hdomB, hRB', hboundary, hdvrs⟩ :=
    Algebra.parameter_root_boundary_dvrs t tail htail n hn
  obtain ⟨i, hi⟩ := (hboundary q hq).mp hz
  obtain ⟨hpi, hqi, hc, hVdvr, hAdvr, hheight, hVm, hAm, hequiv,
    hinjective, hfinite, hfrac, hindex1, hindex2, hindex3⟩ := hdvrs i
  subst q
  refine ⟨Algebra.parameterBaseBoundaryIdeal t i, hpi, hc, hVdvr, hAdvr,
    hfinite, hinjective, hindex1.trans (hindex2.trans hindex3), ?_⟩
  have hrne : r ≠ 0 := by intro hr; exact Fin.elim0 (hr ▸ i)
  simp [n, hrne]

end AlgebraicGeometry
