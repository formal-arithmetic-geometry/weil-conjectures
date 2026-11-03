/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationCanonicalMap
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed

/-! # The strict-local comparison on an ind-etale affine chart

Source: Stacks Project, Tags 04HX, 04GU, 097K and 097M
(blueprint: lem-trf-strict-local-comparison-ind-etale).

The strict-local rings are the chosen small pointed-neighbourhood colimits.
The named ring map `h` is fixed by requiring its spectrum to be the existing
canonical pointed strict-local map. No assumption is made outside the chosen charts.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- In one universe, canonical ULift transport preserves ind-etaleness. -/
private theorem indEtaleAcross_iff {R D : Type u} [CommRing R] [CommRing D]
    (f : R →+* D) : f.IndEtaleAcrossUniverses ↔ f.IndEtale := by
  have hi : RingHom.RespectsIso (@RingHom.IndEtale.{u}) :=
    RingHom.IndEtale.isStableUnderBaseChange.localizationPreserves.away.respectsIso
  constructor
  · intro h
    exact hi.2 _ (ULift.ringEquiv.symm : R ≃+* ULift.{u} R)
      (hi.1 _ (ULift.ringEquiv : ULift.{u} D ≃+* D) h)
  · intro h
    exact hi.1 _ (ULift.ringEquiv.symm : D ≃+* ULift.{u} D)
      (hi.2 _ (ULift.ringEquiv : ULift.{u} R ≃+* R) h)

/-- The residue description also makes the canonical point evaluation local. -/
private theorem strictLocal_point_data
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    ∃ (_ : IsLocalRing (strictHenselizationRing y)),
      IsStrictlyHenselianLocalRing (strictHenselizationRing y) ∧
      strictHenselizationStructuralMap y (IsLocalRing.closedPoint (strictHenselizationRing y)) =
        y (IsLocalRing.closedPoint Ω) ∧
      IsLocalHom (strictHenselizationPointEvaluation y) := by
  let : Algebra (Y.residueField (y (IsLocalRing.closedPoint Ω))) Ω :=
    (descResidueField (stalkClosedPointTo y)).hom.toAlgebra
  obtain ⟨hl, hs, hc, _, σ, hσ, _⟩ := strictHenselizationResidue y rfl
  let := hl
  let ψ := (((IntermediateField.val
    (separableClosure (Y.residueField (y (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
      σ.toRingHom).comp (IsLocalRing.residue (strictHenselizationRing y)))
  have he : Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation y)) := by
    obtain ⟨hlim⟩ := (strictHenselization_properties y).2.2
    apply hlim.hom_ext
    intro j
    apply (cancel_mono (Spec (Opposite.unop ((equivSmallModel.{u}
      (strictHenselizationNeighbourhoods y)).inverse.obj
        j.unop.unop).1.left)).isoSpec.inv).1
    exact (hσ.1 j.unop.unop).trans
      (strictHenselizationPointEvaluation_pointed y j.unop.unop).symm
  have hψ : ψ = strictHenselizationPointEvaluation y :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective he)
  refine ⟨hl, hs, hc, ?_⟩
  rw [← hψ]
  infer_instance

/-- Every point of a local spectrum generalizes its closed point, so a map whose closed
point lies in an open affine chart factors through that chart. -/
private theorem affineFactor_of_closedPoint
    {Y : Scheme.{u}} (R D : CommRingCat.{u}) [IsLocalRing D]
    (i : Spec R ⟶ Y) [IsOpenImmersion i] (j : Spec D ⟶ Y)
    (hc : j (IsLocalRing.closedPoint D) ∈ Set.range i) :
    ∃ a : R →+* D, Spec.map (CommRingCat.ofHom a) ≫ i = j := by
  have hrange : Set.range j ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map j.continuous).mem_open
      (IsOpenImmersion.isOpen_range i) hc
  let l := IsOpenImmersion.lift i j hrange
  refine ⟨(Spec.preimage l).hom, ?_⟩
  change Spec.map (Spec.preimage l) ≫ i = j
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac i j hrange

/-- The canonical comparison is ind-etale when the map on the chosen affine open
neighbourhoods is ind-etale. The two existential clauses assert the chart
factorizations; the universal clause applies to every pair of their ring maps.
Source: Stacks Project, Tag 04HX (`lemma-describe-etale-local-ring`), Tag 04GU
(`lemma-strictly-henselian-functorial`), Tag 097K (`lemma-composition-ind-etale`)
and Tag 097M (`lemma-ind-etale-permanence`)
(blueprint: lem-trf-strict-local-comparison-ind-etale).

Proof:
1. The residue clause of strict-henselization functoriality makes the two rings strictly
henselian and identifies the images of their closed points. Every point of a local spectrum
generalizes its closed point, so each structural map lands in its prescribed open chart.
The open-immersion lifting property and the spectrum correspondence give the ring maps.
2. Compose both candidate maps to the first chart with its open immersion. The canonical
structural square and the chart equations identify these composites. Cancel the open
immersion and use spectrum faithfulness to obtain `h.comp a = b.comp f` for every pair.
3. Apply `smallStrictHenselization_indEtale_of_affine_chart` to each factorization,
using the identity spectrum isomorphism and the chosen small strict-local rings.
4. Composition makes `b.comp f` ind-etale. The compatibility equation makes `h` an
A-algebra map between ind-etale A-algebras; relative permanence makes it ind-etale.
Transport along the canonical ULift ring equivalences gives the universe-independent clauses.
5. Limit extensionality identifies canonical point evaluation with the local residue
formula. The canonical pointed equation makes evaluation after `h` local, hence `h` is
local. Strict henselianity and the structural square were supplied above. -/
theorem strictLocalComparison_indEtale
    {S T : Scheme.{u}} (g : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (A B : CommRingCat.{u}) (iU : Spec A ⟶ S) (iV : Spec B ⟶ T)
    [IsOpenImmersion iU] [IsOpenImmersion iV]
    (hs : (t ≫ g) (IsLocalRing.closedPoint Ω) ∈ Set.range iU)
    (ht : t (IsLocalRing.closedPoint Ω) ∈ Set.range iV)
    (f : A →+* B)
    (hf : Spec.map (CommRingCat.ofHom f) ≫ iU = iV ≫ g)
    (hind : f.IndEtaleAcrossUniverses)
    (h : strictHenselizationRing (t ≫ g) ⟶ strictHenselizationRing t)
    (hh : Spec.map h = strictHenselizationMap g t) :
    (∃ a : A →+* strictHenselizationRing (t ≫ g),
      Spec.map (CommRingCat.ofHom a) ≫ iU = strictHenselizationStructuralMap (t ≫ g)) ∧
    (∃ b : B →+* strictHenselizationRing t,
      Spec.map (CommRingCat.ofHom b) ≫ iV = strictHenselizationStructuralMap t) ∧
    (∀ (a : A →+* strictHenselizationRing (t ≫ g))
        (b : B →+* strictHenselizationRing t),
      Spec.map (CommRingCat.ofHom a) ≫ iU = strictHenselizationStructuralMap (t ≫ g) →
      Spec.map (CommRingCat.ofHom b) ≫ iV = strictHenselizationStructuralMap t →
      h.hom.comp a = b.comp f ∧
      a.IndEtaleAcrossUniverses ∧ b.IndEtaleAcrossUniverses ∧
      (b.comp f).IndEtaleAcrossUniverses ∧ h.hom.IndEtaleAcrossUniverses) ∧
    IsStrictlyHenselianLocalRing (strictHenselizationRing (t ≫ g)) ∧
    IsStrictlyHenselianLocalRing (strictHenselizationRing t) ∧
    IsLocalHom h.hom ∧
    Spec.map h ≫ strictHenselizationStructuralMap (t ≫ g) =
      strictHenselizationStructuralMap t ≫ g := by
  obtain ⟨hS, hsS, hcS, heS⟩ := strictLocal_point_data (t ≫ g)
  obtain ⟨hT, hsT, hcT, heT⟩ := strictLocal_point_data t
  let := hS
  let := hT
  have hbase : Spec.map h ≫ strictHenselizationStructuralMap (t ≫ g) =
      strictHenselizationStructuralMap t ≫ g := by
    rw [hh]
    exact strictHenselizationMap_over g t
  have hpoint : Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation t)) ≫
      Spec.map h =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (t ≫ g))) := by
    rw [hh]
    exact (Classical.choose_spec (strictHenselizationMap_existsUnique g t)).1.2
  have heval : (strictHenselizationPointEvaluation t).comp h.hom =
      strictHenselizationPointEvaluation (t ≫ g) := by
    have heq : h ≫ CommRingCat.ofHom (strictHenselizationPointEvaluation t) =
        CommRingCat.ofHom (strictHenselizationPointEvaluation (t ≫ g)) := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      exact hpoint
    exact congrArg CommRingCat.Hom.hom heq
  have hlocal : IsLocalHom h.hom := by
    have : IsLocalHom ((strictHenselizationPointEvaluation t).comp h.hom) := heval.symm ▸ heS
    exact isLocalHom_of_comp h.hom (strictHenselizationPointEvaluation t)
  refine ⟨affineFactor_of_closedPoint A _ iU _ (hcS.symm ▸ hs),
    affineFactor_of_closedPoint B _ iV _ (hcT.symm ▸ ht), ?_, hsS, hsT, hlocal, hbase⟩
  intro a b ha hb
  have hcomp : h.hom.comp a = b.comp f := by
    have heq : CommRingCat.ofHom a ≫ h = CommRingCat.ofHom f ≫ CommRingCat.ofHom b := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp]
      apply (cancel_mono iU).1
      calc
        (Spec.map h ≫ Spec.map (CommRingCat.ofHom a)) ≫ iU =
            strictHenselizationStructuralMap t ≫ g := by rw [Category.assoc, ha, hbase]
        _ = (Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom f)) ≫ iU := by
          rw [Category.assoc, hf, ← Category.assoc, hb]
    exact congrArg CommRingCat.Hom.hom heq
  have haInd : a.IndEtale :=
    smallStrictHenselization_indEtale_of_affine_chart (t ≫ g) A iU hs (Iso.refl _) a
      (by simpa only [Iso.refl_hom, Category.id_comp] using ha)
  have hbInd : b.IndEtale :=
    smallStrictHenselization_indEtale_of_affine_chart t B iV ht (Iso.refl _) b
      (by simpa only [Iso.refl_hom, Category.id_comp] using hb)
  have hbf : (b.comp f).IndEtale := hbInd.comp ((indEtaleAcross_iff f).mp hind)
  have hhInd : h.hom.IndEtale := by
    let : Algebra A (strictHenselizationRing (t ≫ g)) := a.toAlgebra
    let : Algebra A (strictHenselizationRing t) := (b.comp f).toAlgebra
    let hAlg : strictHenselizationRing (t ≫ g) →ₐ[A] strictHenselizationRing t :=
      { h.hom with commutes' := fun x ↦ congrArg (fun k ↦ k x) hcomp }
    exact RingHom.indEtale_principalZariski_stability.2.2.2.2.2.2.2.1
      A (strictHenselizationRing (t ≫ g)) (strictHenselizationRing t) haInd hbf hAlg
  exact ⟨hcomp, (indEtaleAcross_iff a).mpr haInd, (indEtaleAcross_iff b).mpr hbInd,
    (indEtaleAcross_iff (b.comp f)).mpr hbf, (indEtaleAcross_iff h.hom).mpr hhInd⟩

end AlgebraicGeometry.Scheme
