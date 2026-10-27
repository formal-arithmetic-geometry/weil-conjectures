/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RingHom.Flat
public import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
import Sheaf.AlgebraicGeometry.GeometricStrictLocalStalkPresentation
import Sheaf.AlgebraicGeometry.LocallyIndEtaleBaseChangeCharts
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import Sheaf.Paper.StrictHenselizationPointEvaluationProperties
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import WeilConjectures.RingTheory.StrictHenselizationNoetherian

/-! # Strict-local base change model of a smooth morphism

Source: Stacks Project, Tags 04HX, 08HV, 01VB, 01VF and 06LJ
(blueprint: lem-trf-smooth-strict-local-base-model).

The auxiliary definitions name the specified pullback point, its ordinary local ring,
its structural ring map, and the canonical strict-local projection. All are constructions
from the published strict henselization, geometric evaluation and scheme stalk APIs.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.SmoothStrictLocalBaseModel

variable {V S : Scheme.{u}} (f : V ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (v : Spec (.of Ω) ⟶ V)

/-- The base change `W = V ×_S Spec A`, where `A = Oˢʰ_(S,fv)`.
Source: Stacks Project, Tag 08HV
(blueprint: lem-trf-smooth-strict-local-base-model). -/
noncomputable abbrev baseChange : Scheme.{u} :=
  pullback f (strictHenselizationStructuralMap (v ≫ f))

/-- The projection `p : W → Spec A`.
Source: Stacks Project, Tag 01VB
(blueprint: lem-trf-smooth-strict-local-base-model). -/
noncomputable abbrev projection : baseChange f v ⟶ strictHenselizationScheme (v ≫ f) :=
  pullback.snd f (strictHenselizationStructuralMap (v ≫ f))

/-- The compatible geometric point `(v,a)`, with `a` the canonical closed geometric lift.
Source: Stacks Project, Tags 04HX and 08HV
(blueprint: lem-trf-smooth-strict-local-base-model). -/
noncomputable def geometricPoint : Spec (.of Ω) ⟶ baseChange f v :=
  pullback.lift v
    (Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (v ≫ f))))
    (strictHenselizationClosedLift_over (v ≫ f)).symm

/-- The image `w` of the specified geometric point of W.
Source: Stacks Project, Tag 04HX
(blueprint: lem-trf-smooth-strict-local-base-model). -/
noncomputable def point : baseChange f v :=
  geometricPoint f v (IsLocalRing.closedPoint Ω)

/-- The ordinary local ring `C = O_(W,w)`.
Source: Stacks Project, Tag 04HX
(blueprint: lem-trf-smooth-strict-local-base-model). -/
noncomputable abbrev ordinaryLocalRing : CommRingCat.{u} :=
  (baseChange f v).presheaf.stalk (point f v)

/-- The ordinary structural map `A → C`: localization to the base stalk, then the stalk map.
Source: Stacks Project, Tags 01VF and 01HV
(blueprint: lem-trf-smooth-strict-local-base-model). -/
noncomputable def ordinaryMap : strictHenselizationRing (v ≫ f) →+* ordinaryLocalRing f v :=
  (StructureSheaf.toStalk (strictHenselizationRing (v ≫ f))
    (projection f v (point f v)) ≫ (projection f v).stalkMap (point f v)).hom

/-- The canonical `φ : A → B`, obtained contravariantly from strict-henselization functoriality.
Source: Stacks Project, Tag 08HV and the paragraph after Tag 03PS
(blueprint: lem-trf-smooth-strict-local-base-model). -/
noncomputable def strictMap : strictHenselizationRing (v ≫ f) →+* strictHenselizationRing v :=
  (Spec.preimage (strictHenselizationMap f v)).hom

/-- The canonical projection `W_(w̄) → V_(v̄)`, with its target transported along the
pullback's first-projection equation. Source: Stacks Project, Tags 08HV and 0GIP
(blueprint: lem-trf-smooth-strict-local-base-model). -/
noncomputable def strictProjection :
    strictHenselizationScheme (geometricPoint f v) ⟶ strictHenselizationScheme v :=
  strictHenselizationMap (pullback.fst f (strictHenselizationStructuralMap (v ≫ f)))
    (geometricPoint f v) ≫
      eqToHom (congrArg strictHenselizationScheme
        (pullback.lift_fst v
          (Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (v ≫ f))))
          (strictHenselizationClosedLift_over (v ≫ f)).symm))

private theorem evaluation_isLocal
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) [IsLocalRing (strictHenselizationRing x)] :
    IsLocalHom (strictHenselizationPointEvaluation x) := by
  let : Algebra (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω :=
    (descResidueField (stalkClosedPointTo x)).hom.toAlgebra
  let ψ := strictHenselizationPointEvaluationToSep x rfl
  have : IsLocalHom ψ := IsLocalHom.of_surjective ψ
    (strictHenselizationPointEvaluationToSep_surjective x rfl)
  let ι := (IntermediateField.val
    (separableClosure (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω)).toRingHom
  have : IsLocalHom ι := inferInstance
  exact (inferInstance : IsLocalHom (ι.comp ψ))

private theorem evaluation_kernel
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) [IsLocalRing (strictHenselizationRing x)] :
    RingHom.ker (strictHenselizationPointEvaluation x) =
      IsLocalRing.maximalIdeal (strictHenselizationRing x) := by
  have := evaluation_isLocal x
  simpa only [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot] using
    IsLocalRing.maximalIdeal_comap (strictHenselizationPointEvaluation x)

private theorem evaluation_closedPoint
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) [IsLocalRing (strictHenselizationRing x)] :
    Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x))
        (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint (strictHenselizationRing x) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (strictHenselizationPointEvaluation x)
    (IsLocalRing.maximalIdeal Ω) =
      IsLocalRing.maximalIdeal (strictHenselizationRing x)
  simpa only [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot] using
    evaluation_kernel x

private theorem projection_point_closed
    [IsLocalRing (strictHenselizationRing (v ≫ f))] :
    projection f v (point f v) =
      IsLocalRing.closedPoint (strictHenselizationRing (v ≫ f)) := by
  have he := congrArg (fun g ↦ g (IsLocalRing.closedPoint Ω))
    (pullback.lift_snd v
      (Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (v ≫ f))))
      (strictHenselizationClosedLift_over (v ≫ f)).symm)
  exact he.trans (evaluation_closedPoint (v ≫ f))

private theorem ordinary_flat [Smooth f]
    [IsLocalRing (strictHenselizationRing (v ≫ f))] :
    RingHom.Flat (ordinaryMap f v) ∧ IsLocalHom (ordinaryMap f v) := by
  have hs : Smooth (projection f v) := inferInstance
  have ht : IsIso (StructureSheaf.toStalk (strictHenselizationRing (v ≫ f))
      (projection f v (point f v))) := by
    rw [projection_point_closed, ← stalkClosedPointIso_inv]
    infer_instance
  have hl : IsLocalHom (StructureSheaf.toStalk (strictHenselizationRing (v ≫ f))
      (projection f v (point f v))).hom := isLocalHom_of_isIso _
  constructor
  · exact (RingHom.Flat.of_bijective
      ((ConcreteCategory.isIso_iff_bijective _).mp ht)).comp
        (Flat.stalkMap (projection f v) (point f v))
  · change IsLocalHom (((projection f v).stalkMap (point f v)).hom.comp
      (StructureSheaf.toStalk (strictHenselizationRing (v ≫ f))
        (projection f v (point f v))).hom)
    infer_instance

private theorem pointedMap_evaluation
    {X Y : Scheme.{u}} (g : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫
      strictHenselizationMap g x =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (x ≫ g))) := by
  exact (Classical.choose_spec (strictHenselizationMap_existsUnique g x)).1.2

private theorem pointedMap_over_congr
    {X Y : Scheme.{u}} (g : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (h : x ≫ g = y) :
    (strictHenselizationMap g x ≫ eqToHom (congrArg strictHenselizationScheme h)) ≫
      strictHenselizationStructuralMap y = strictHenselizationStructuralMap x ≫ g := by
  subst y
  simpa only [eqToHom_refl, Category.comp_id] using strictHenselizationMap_over g x

private theorem pointedMap_evaluation_congr
    {X Y : Scheme.{u}} (g : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (h : x ≫ g = y) :
    Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫
      (strictHenselizationMap g x ≫ eqToHom (congrArg strictHenselizationScheme h)) =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation y)) := by
  subst y
  simpa only [eqToHom_refl, Category.comp_id] using pointedMap_evaluation g x

private theorem pointedMap_unique_congr
    {X Y : Scheme.{u}} (g : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (h : x ≫ g = y)
    (b c : strictHenselizationScheme x ⟶ strictHenselizationScheme y)
    (hb : b ≫ strictHenselizationStructuralMap y = strictHenselizationStructuralMap x ≫ g)
    (hpb : Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ b =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation y)))
    (hc : c ≫ strictHenselizationStructuralMap y = strictHenselizationStructuralMap x ≫ g)
    (hpc : Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ c =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation y))) : b = c := by
  subst y
  have hu := (Classical.choose_spec (strictHenselizationMap_existsUnique g x)).2
  exact (hu b ⟨hb, hpb⟩).trans (hu c ⟨hc, hpc⟩).symm

private theorem strictMap_local
    [IsLocalRing (strictHenselizationRing (v ≫ f))]
    [IsLocalRing (strictHenselizationRing v)] : IsLocalHom (strictMap f v) := by
  have he : (strictHenselizationPointEvaluation v).comp (strictMap f v) =
      strictHenselizationPointEvaluation (v ≫ f) := by
    apply CommRingCat.hom_ext_iff.mp
    apply Spec.map_injective
    change Spec.map (Spec.preimage (strictHenselizationMap f v) ≫
      CommRingCat.ofHom (strictHenselizationPointEvaluation v)) = _
    rw [Spec.map_comp, Spec.map_preimage]
    exact pointedMap_evaluation f v
  have := evaluation_isLocal (v ≫ f)
  have : IsLocalHom ((strictHenselizationPointEvaluation v).comp (strictMap f v)) :=
    he.symm ▸ ‹_›
  exact isLocalHom_of_comp (strictMap f v) (strictHenselizationPointEvaluation v)

private theorem strictRing_noetherian
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) [IsLocallyNoetherian X] :
    IsNoetherianRing (strictHenselizationRing x) := by
  let C : Type u := X.presheaf.stalk (x (IsLocalRing.closedPoint Ω))
  let : Algebra (IsLocalRing.ResidueField C) Ω :=
    (descResidueField (stalkClosedPointTo x)).hom.toAlgebra
  let K := separableClosure (IsLocalRing.ResidueField C) Ω
  let : Algebra C K := ((algebraMap (IsLocalRing.ResidueField C) K).comp
    (IsLocalRing.residue C)).toAlgebra
  have : IsScalarTower C (IsLocalRing.ResidueField C) K :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨H, hH, aH, P, hlocal, θ, _, _⟩ :=
    geometricStrictLocal_stalk_presentation x rfl
  have hP : Algebra.IsStrictHenselization C K H :=
    ⟨P.cocone, ⟨P.isColimit⟩, ⟨P.identification⟩⟩
  have : IsNoetherianRing H :=
    (Algebra.isNoetherianRing_iff_isStrictHenselization C K H hP).mp inferInstance
  exact isNoetherianRing_of_ringEquiv H θ.symm

private theorem indEtale_bijective {R T : Type u} [CommRing R] [CommRing T]
    (r : R →+* T) (h : Function.Bijective r) : r.IndEtale := by
  let := r.toAlgebra
  have : Algebra.Etale R T := (RingHom.Etale.of_bijective h).toAlgebra
  apply (Algebra.IndEtale.iff_ind_etale R T).mpr
  exact (CommAlgCat.etale R).le_ind _ ‹Algebra.Etale R T›

private theorem indEtale_across_iff {R T : Type u} [CommRing R] [CommRing T]
    (r : R →+* T) : r.IndEtaleAcrossUniverses ↔ r.IndEtale := by
  let a : R ≃+* ULift.{u} R := ULift.ringEquiv.symm
  let b : T ≃+* ULift.{u} T := ULift.ringEquiv.symm
  constructor
  · intro h
    have hh := (indEtale_bijective b.symm.toRingHom b.symm.bijective).comp
      (h.comp (indEtale_bijective a.toRingHom a.bijective))
    simpa only [a, b, RingEquiv.symm_symm, RingHom.comp_ulift_eq] using hh
  · intro h
    have hh := (indEtale_bijective b.toRingHom b.bijective).comp
      (h.comp (indEtale_bijective a.symm.toRingHom a.symm.bijective))
    exact hh

private theorem structural_charts
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ∀ z : strictHenselizationScheme x,
      ∃ (R T : CommRingCat.{u}) (r : R ⟶ T)
        (iT : Spec T ⟶ strictHenselizationScheme x) (iR : Spec R ⟶ X),
        IsOpenImmersion iT ∧ IsOpenImmersion iR ∧ z ∈ Set.range iT ∧
        Spec.map r ≫ iR = iT ≫ strictHenselizationStructuralMap x ∧
        r.hom.IndEtaleAcrossUniverses := by
  classical
  let : Algebra (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω :=
    (descResidueField (stalkClosedPointTo x)).hom.toAlgebra
  obtain ⟨hl, _, hc, _, _⟩ := strictHenselizationResidue x rfl
  have := hl
  obtain ⟨R, i, hi, y, hy⟩ := X.exists_Spec_apply_eq (x (IsLocalRing.closedPoint Ω))
  have := hi
  have hrange : Set.range (strictHenselizationStructuralMap x) ⊆ Set.range i := by
    have hclosed : IsLocalRing.closedPoint (strictHenselizationRing x) ∈
        (strictHenselizationStructuralMap x) ⁻¹ᵁ i.opensRange := by
      change strictHenselizationStructuralMap x _ ∈ Set.range i
      rw [hc]
      exact ⟨y, hy⟩
    have htop := (IsLocalRing.closedPoint_mem_iff _).mp hclosed
    rintro _ ⟨z, rfl⟩
    exact (show z ∈ (strictHenselizationStructuralMap x) ⁻¹ᵁ i.opensRange from
      htop ▸ trivial)
  let b := IsOpenImmersion.lift i (strictHenselizationStructuralMap x) hrange
  have hb : b ≫ i = strictHenselizationStructuralMap x :=
    IsOpenImmersion.lift_fac _ _ _
  let r := Spec.preimage b
  have hind : r.hom.IndEtale := smallStrictHenselization_indEtale_of_affine_chart
    x R i ⟨y, hy⟩ (Iso.refl _) r.hom (by
      change Spec.map (Spec.preimage b) ≫ i = 𝟙 _ ≫ _
      rw [Spec.map_preimage, Category.id_comp]
      exact hb)
  intro z
  exact ⟨R, strictHenselizationRing x, r, 𝟙 _, i, inferInstance, hi,
    ⟨z, rfl⟩, by
      change Spec.map (Spec.preimage b) ≫ i = 𝟙 _ ≫ _
      rw [Spec.map_preimage, Category.id_comp]
      exact hb,
    (indEtale_across_iff _).mpr hind⟩

private theorem strictProjection_isIso : IsIso (strictProjection f v) := by
  let j := strictHenselizationStructuralMap (v ≫ f)
  let e := pullbackSymmetry f j
  have hcharts := (locally_indEtale_base_change_charts j
    (structural_charts (v ≫ f)) f).2
  have hlocal : ∀ z : baseChange f v, ∃ (U : (baseChange f v).Opens) (T : V.Opens),
      z ∈ U ∧ IsAffine U.toScheme ∧ IsAffine T.toScheme ∧
      ∃ r : U.toScheme ⟶ T.toScheme,
        r ≫ T.ι = U.ι ≫ pullback.fst f j ∧ proAffineEtale r := by
    intro z
    obtain ⟨R, D, r, iD, iR, hD, hR, hz, hr, hind⟩ := hcharts (e.hom z)
    have := hD
    have := hR
    let i := iD ≫ e.inv
    have : IsOpenImmersion i := by dsimp [i]; infer_instance
    have hfac : Spec.map r ≫ iR = i ≫ pullback.fst f j := by
      dsimp only [i, e]
      rw [Category.assoc, pullbackSymmetry_inv_comp_fst]
      exact hr
    have hmem : z ∈ Set.range i := by
      obtain ⟨t, ht⟩ := hz
      refine ⟨t, ?_⟩
      change e.inv (iD t) = z
      rw [ht]
      exact congrArg (fun g : pullback f j ⟶ pullback f j ↦ g z) e.hom_inv_id
    let a := i.isoOpensRange.inv ≫ Spec.map r ≫ iR.isoOpensRange.hom
    refine ⟨i.opensRange, iR.opensRange, hmem, isAffineOpen_opensRange i,
      isAffineOpen_opensRange iR, a, ?_, ?_⟩
    · dsimp only [a]
      simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
      rw [hfac, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
    · dsimp only [a]
      rw [proAffineEtale.cancel_left_of_respectsIso,
        proAffineEtale.cancel_right_of_respectsIso]
      exact proAffineEtale_Spec_iff.mpr ((indEtale_across_iff _).mp hind)
  let q := pullback.fst f j
  have hfst : geometricPoint f v ≫ q = v := pullback.lift_fst v _ _
  obtain ⟨a, ha, hp, _⟩ := indEtale_strictLocal_invariance q hlocal
    (geometricPoint f v) v hfst.symm
  have hα := pointedMap_over_congr q (geometricPoint f v) v hfst
  have hε := pointedMap_evaluation_congr q (geometricPoint f v) v hfst
  have he : a.hom = strictProjection f v :=
    pointedMap_unique_congr q (geometricPoint f v) v hfst
      a.hom (strictProjection f v) ha hp hα hε
  exact he ▸ (inferInstance : IsIso a.hom)

/-- A smooth morphism has the canonical strict-local base change model, with its ordinary
flat local structural map and its specified residue-compatible algebraic comparison.
The existential algebra on Ω is fixed by the displayed geometric residue embedding;
the scalar tower fixes the C-algebra on that very relative separable closure. `P` is the
published universal pointed-etale colimit presentation, so H is Cˢʰ, not an arbitrary ring.
The structural and evaluation equations characterize θ as the affine local-ring comparison;
the spectrum equation then identifies β with the canonical strict-local projection.
Source: Stacks Project, Tags 04HX, 08HV, 01VB, 01VF and 06LJ
(blueprint: lem-trf-smooth-strict-local-base-model).

Proof:
1. Strict-henselization functoriality gives local A and B, their canonical geometric
   evaluations and the closed lift a. Thus the pullback point w lies over m_A. Apply
   the small strict-henselization ind-etale theorem to an affine chart on S: the structural
   map Spec A → S factors through that chart by an ind-etale ring map.
2. Base change its ind-etale charts by f. Apply strict-local invariance to the resulting
   projection to V, and use pointed uniqueness to identify the supplied isomorphism with
   strictProjection.
3. Apply geometricStrictLocal_stalk_presentation on W to obtain H, its presentation over
   C, and θ with the structural and evaluation equations. Compose θ with the ring
   equivalence opposite to strictProjection to obtain β. Full faithfulness of Spec gives
   the displayed spectrum equation.
4. Functoriality preserves the residue embeddings inside Ω. The two affine comparisons
   preserve structure maps and evaluations, hence β⁻¹ composed with A → C → H is a local
   map over S with the prescribed residue inclusion. Uniqueness in strict-henselization
   functoriality identifies it with φ. This gives the factorization and evaluation equations.
   The local geometric evaluations have field targets, so their kernels are m_A and m_B.
5. Smoothness is stable under base change (lem-pc-proper-base-change, smooth clause),
   and smooth maps are flat (lem-pc-smooth-flat). Their stalk maps are flat and local.
   Identify the stalk of Spec A at its closed point with A; this proves flatness and
   locality of ordinaryMap, without any Noetherian assumption.
6. If S and V are locally Noetherian, their ordinary stalks are Noetherian. The ordinary
   stalk presentations and lem-sc-strict-henselization-noetherian give Noetherianity
   of A and B. No prior step uses this additional hypothesis. -/
theorem smooth_strictLocal_base_model
    {V S : Scheme.{u}} (f : V ⟶ S) [Smooth f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) :
    Smooth (projection f v) ∧
    ∃ (_ : IsLocalRing (strictHenselizationRing (v ≫ f)))
      (_ : IsLocalRing (strictHenselizationRing v)),
      projection f v (point f v) = IsLocalRing.closedPoint (strictHenselizationRing (v ≫ f)) ∧
      RingHom.Flat (ordinaryMap f v) ∧ IsLocalHom (ordinaryMap f v) ∧
      IsLocalHom (strictMap f v) ∧
      RingHom.ker (strictHenselizationPointEvaluation (v ≫ f)) =
        IsLocalRing.maximalIdeal (strictHenselizationRing (v ≫ f)) ∧
      RingHom.ker (strictHenselizationPointEvaluation v) =
        IsLocalRing.maximalIdeal (strictHenselizationRing v) ∧
      (IsLocallyNoetherian S → IsLocallyNoetherian V →
        IsNoetherianRing (strictHenselizationRing (v ≫ f)) ∧
        IsNoetherianRing (strictHenselizationRing v)) ∧
      IsIso (strictProjection f v) ∧
      strictProjection f v ≫ strictHenselizationStructuralMap v =
        strictHenselizationStructuralMap (geometricPoint f v) ≫
          pullback.fst f (strictHenselizationStructuralMap (v ≫ f)) ∧
      ∃ (_ : Algebra (IsLocalRing.ResidueField (ordinaryLocalRing f v)) Ω),
        algebraMap (IsLocalRing.ResidueField (ordinaryLocalRing f v)) Ω =
          (descResidueField (stalkClosedPointTo (geometricPoint f v))).hom ∧
        ∃ (_ : Algebra (ordinaryLocalRing f v)
            (separableClosure (IsLocalRing.ResidueField (ordinaryLocalRing f v)) Ω))
          (_ : IsScalarTower (ordinaryLocalRing f v)
            (IsLocalRing.ResidueField (ordinaryLocalRing f v))
            (separableClosure (IsLocalRing.ResidueField (ordinaryLocalRing f v)) Ω))
          (H : Type u) (_ : CommRing H) (_ : Algebra (ordinaryLocalRing f v) H)
          (P : Algebra.StrictHenselizationPresentationIn (ordinaryLocalRing f v)
            (separableClosure (IsLocalRing.ResidueField (ordinaryLocalRing f v)) Ω) H)
          (_ : IsLocalRing H)
          (θ : strictHenselizationRing (geometricPoint f v) ≃+* H)
          (β : strictHenselizationRing v ≃+* H),
          IsLocalHom β.toRingHom ∧
          β.toRingHom.comp (strictMap f v) =
            (algebraMap (ordinaryLocalRing f v) H).comp (ordinaryMap f v) ∧
          (separableClosure (IsLocalRing.ResidueField (ordinaryLocalRing f v)) Ω).subtype.comp
              (P.residueMap.comp β.toRingHom) = strictHenselizationPointEvaluation v ∧
          Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
              strictHenselizationStructuralMap (geometricPoint f v) =
            Spec.map (CommRingCat.ofHom (algebraMap (ordinaryLocalRing f v) H)) ≫
              (baseChange f v).fromSpecStalk (point f v) ∧
          (separableClosure (IsLocalRing.ResidueField (ordinaryLocalRing f v)) Ω).subtype.comp
              (P.residueMap.comp θ.toRingHom) =
            strictHenselizationPointEvaluation (geometricPoint f v) ∧
          Spec.map (CommRingCat.ofHom β.toRingHom) =
            Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ strictProjection f v := by
  obtain ⟨hA, _⟩ := AlgebraicGeometry.strictHenselizationLocalStructure (v ≫ f)
  obtain ⟨hB, _⟩ := AlgebraicGeometry.strictHenselizationLocalStructure v
  have := hA
  have := hB
  obtain ⟨hflat, hlocal⟩ := ordinary_flat f v
  refine ⟨inferInstance, hA, hB, projection_point_closed f v, hflat, hlocal, strictMap_local f v,
    evaluation_kernel (v ≫ f), evaluation_kernel v, ?_, ?_, ?_, ?_⟩
  · intro hS hV
    have := hS
    have := hV
    exact ⟨strictRing_noetherian (v ≫ f), strictRing_noetherian v⟩
  · exact strictProjection_isIso f v
  · exact pointedMap_over_congr _ _ _
      (pullback.lift_fst v _ _)
  · let C : Type u := (baseChange f v).presheaf.stalk
      ((geometricPoint f v) (IsLocalRing.closedPoint Ω))
    let aΩ : Algebra (IsLocalRing.ResidueField C) Ω :=
      (descResidueField (stalkClosedPointTo (geometricPoint f v))).hom.toAlgebra
    let K := separableClosure (IsLocalRing.ResidueField C) Ω
    let aK : Algebra C K := ((algebraMap (IsLocalRing.ResidueField C) K).comp
      (IsLocalRing.residue C)).toAlgebra
    have hCK : IsScalarTower C (IsLocalRing.ResidueField C) K :=
      IsScalarTower.of_algebraMap_eq' rfl
    obtain ⟨H, hH, aH, P, hLH, θ, hθbase, hθeval⟩ :=
      geometricStrictLocal_stalk_presentation (geometricPoint f v) rfl
    have hα : IsIso (strictProjection f v) := strictProjection_isIso f v
    let γ₀ : strictHenselizationRing v ≅ strictHenselizationRing (geometricPoint f v) :=
      (Scheme.Spec.preimageIso
        (X := Opposite.op (strictHenselizationRing (geometricPoint f v)))
        (Y := Opposite.op (strictHenselizationRing v))
        (asIso (strictProjection f v))).unop
    let γ := γ₀.commRingCatIsoToRingEquiv
    let β := γ.trans θ
    have hγ : Spec.map (CommRingCat.ofHom γ.toRingHom) = strictProjection f v := by
      change Spec.map (Spec.preimage (strictProjection f v)) = strictProjection f v
      exact Spec.map_preimage _
    have hβ : Spec.map (CommRingCat.ofHom β.toRingHom) =
        Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ strictProjection f v := by
      change Spec.map (CommRingCat.ofHom γ.toRingHom ≫
        CommRingCat.ofHom θ.toRingHom) = _
      rw [Spec.map_comp, hγ]
    let ε : H →+* Ω := K.subtype.comp P.residueMap
    have hθε : ε.comp θ.toRingHom =
        strictHenselizationPointEvaluation (geometricPoint f v) := hθeval
    have hβε : ε.comp β.toRingHom = strictHenselizationPointEvaluation v := by
      apply CommRingCat.hom_ext_iff.mp
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom β.toRingHom ≫ CommRingCat.ofHom ε) = _
      rw [Spec.map_comp, hβ, ← Category.assoc, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom (ε.comp θ.toRingHom)) ≫ _ = _
      rw [hθε]
      exact pointedMap_evaluation_congr _ _ _ (pullback.lift_fst v _ _)
    have hord : Spec.map (CommRingCat.ofHom (ordinaryMap f v)) =
        (baseChange f v).fromSpecStalk (point f v) ≫ projection f v := by
      change Spec.map (StructureSheaf.toStalk (strictHenselizationRing (v ≫ f))
        (projection f v (point f v)) ≫ (projection f v).stalkMap (point f v)) = _
      rw [Spec.map_comp, ← Spec.fromSpecStalk_eq']
      exact Scheme.SpecMap_stalkMap_fromSpecStalk (projection f v) (x := point f v)
    have hθbase' : Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
        strictHenselizationStructuralMap (geometricPoint f v) =
        Spec.map (CommRingCat.ofHom (algebraMap C H)) ≫
          (baseChange f v).fromSpecStalk (point f v) := hθbase
    let d := (algebraMap C H).comp (ordinaryMap f v)
    have hd : Spec.map (CommRingCat.ofHom d) =
        Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
          strictHenselizationStructuralMap (geometricPoint f v) ≫ projection f v := by
      change Spec.map (CommRingCat.ofHom (ordinaryMap f v) ≫
        CommRingCat.ofHom (algebraMap C H)) = _
      rw [Spec.map_comp, hord]
      simpa only [Category.assoc] using congrArg (fun g => g ≫ projection f v) hθbase'.symm
    let βIso : strictHenselizationRing v ≅ CommRingCat.of H :=
      { hom := CommRingCat.ofHom β.toRingHom
        inv := CommRingCat.ofHom β.symm.toRingHom
        hom_inv_id := by ext z; exact β.symm_apply_apply z
        inv_hom_id := by ext z; exact β.apply_symm_apply z }
    let bIso : Spec (CommRingCat.of H) ≅ strictHenselizationScheme v :=
      Scheme.Spec.mapIso βIso.op
    let h := bIso.inv ≫ Spec.map (CommRingCat.ofHom d)
    have hb : h ≫ strictHenselizationStructuralMap (v ≫ f) =
        strictHenselizationStructuralMap v ≫ f := by
      apply (cancel_epi bIso.hom).1
      change bIso.hom ≫ (bIso.inv ≫ Spec.map (CommRingCat.ofHom d)) ≫ _ = _
      rw [Category.assoc, bIso.hom_inv_id_assoc, hd]
      have hw := pullback.condition (f := f) (g := strictHenselizationStructuralMap (v ≫ f))
      have ho := pointedMap_over_congr
        (pullback.fst f (strictHenselizationStructuralMap (v ≫ f)))
        (geometricPoint f v) v (pullback.lift_fst v _ _)
      change _ = Spec.map (CommRingCat.ofHom β.toRingHom) ≫ _
      rw [hβ]
      have ho' : strictProjection f v ≫ strictHenselizationStructuralMap v =
          strictHenselizationStructuralMap (geometricPoint f v) ≫
            pullback.fst f (strictHenselizationStructuralMap (v ≫ f)) := ho
      let t : Spec (CommRingCat.of H) ⟶
          strictHenselizationScheme (geometricPoint f v) :=
        Spec.map (CommRingCat.ofHom θ.toRingHom)
      change t ≫ strictHenselizationStructuralMap (geometricPoint f v) ≫
          projection f v ≫ strictHenselizationStructuralMap (v ≫ f) =
        (t ≫ strictProjection f v) ≫ strictHenselizationStructuralMap v ≫ f
      simp only [Category.assoc]
      rw [← Category.assoc (strictProjection f v)
        (strictHenselizationStructuralMap v) f, ho', Category.assoc, hw]
    have hp : Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation v)) ≫ h =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (v ≫ f))) := by
      have he : Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation v)) =
          Spec.map (CommRingCat.ofHom ε) ≫ bIso.hom := by
        rw [← hβε]
        change Spec.map (CommRingCat.ofHom β.toRingHom ≫ CommRingCat.ofHom ε) =
          Spec.map (CommRingCat.ofHom ε) ≫ Spec.map (CommRingCat.ofHom β.toRingHom)
        exact Spec.map_comp _ _
      rw [he]
      change (Spec.map (CommRingCat.ofHom ε) ≫ bIso.hom) ≫
        (bIso.inv ≫ Spec.map (CommRingCat.ofHom d)) = _
      rw [Category.assoc, ← Category.assoc bIso.hom bIso.inv,
        bIso.hom_inv_id, Category.id_comp, hd, ← Category.assoc,
        ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom (ε.comp θ.toRingHom)) ≫ _ = _
      rw [hθε, ← Category.assoc,
        strictHenselizationClosedLift_over]
      exact pullback.lift_snd _ _ _
    have heq : h = strictHenselizationMap f v :=
      (Classical.choose_spec (strictHenselizationMap_existsUnique f v)).2 h ⟨hb, hp⟩
    have hfactor : β.toRingHom.comp (strictMap f v) = d := by
      suffices hh : (CommRingCat.ofHom (β.toRingHom.comp (strictMap f v)) :
          strictHenselizationRing (v ≫ f) ⟶ CommRingCat.of H) = CommRingCat.ofHom d from
        congrArg CommRingCat.Hom.hom hh
      apply Spec.map_injective
      change Spec.map (Spec.preimage (strictHenselizationMap f v) ≫
        CommRingCat.ofHom β.toRingHom) = _
      rw [Spec.map_comp, Spec.map_preimage, ← heq]
      change bIso.hom ≫ (bIso.inv ≫ Spec.map (CommRingCat.ofHom d)) = _
      exact bIso.hom_inv_id_assoc _
    exact ⟨aΩ, rfl, aK, hCK, H, hH, aH, P, hLH, θ, β,
      IsLocalHom.of_surjective β.toRingHom β.surjective,
      hfactor, hβε, hθbase, hθeval, hβ⟩

end AlgebraicGeometry.Scheme.SmoothStrictLocalBaseModel
