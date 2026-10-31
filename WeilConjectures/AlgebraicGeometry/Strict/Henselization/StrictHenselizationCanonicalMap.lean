/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationFunctoriality

/-! # The canonical pointed strict-local morphism

Source: Stacks Project, Tags 04HX, 03PS and 04GU
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
The existing residue-field formulation is retained; this interface packages its uniquely
characterized map without requiring the caller to supply residue identifications.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Limit extensionality identifies a pointed residue formula with colimit evaluation. -/
private theorem evaluation_eq_of_pointed
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (ψ : strictHenselizationRing y →+* Ω)
    (hp : ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods y),
      Spec.map (CommRingCat.ofHom ψ) ≫
        (strictHenselizationCone y).π.app (Opposite.op (Opposite.op j)) ≫
        (Spec (Opposite.unop ((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods y)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods y)).inverse.obj j).2.left) :
    ψ = strictHenselizationPointEvaluation y := by
  have he : Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation y)) := by
    obtain ⟨hl⟩ := (strictHenselization_properties y).2.2
    apply hl.hom_ext
    intro j
    apply (cancel_mono (Spec (Opposite.unop ((equivSmallModel.{u}
      (strictHenselizationNeighbourhoods y)).inverse.obj
        j.unop.unop).1.left)).isoSpec.inv).1
    exact (hp j.unop.unop).trans
      (strictHenselizationPointEvaluation_pointed y j.unop.unop).symm
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

set_option backward.isDefEq.respectTransparency false in
/-- The unique pointed map over the original morphism.
Source: Stacks Project, Tags 04HX, 03PS and 04GU
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
Proof: apply strictHenselizationResidue to obtain the local structures and the uniquely
pointed residue identifications. Use strictHenselizationFunctoriality with these
identifications and the residue embeddings furnished by the geometric points.
Its local homomorphism gives the required spectrum map. Evaluation is the compatible
geometric-point cocone, so its residue equation is exactly the second displayed equation.
Conversely a pointed map maps the closed point to the closed point and is local.
The residue equation and the uniqueness clause of functoriality give uniqueness. -/
theorem strictHenselizationMap_existsUnique
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ∃! h : strictHenselizationScheme x ⟶ strictHenselizationScheme (x ≫ f),
      h ≫ strictHenselizationStructuralMap (x ≫ f) =
        strictHenselizationStructuralMap x ≫ f ∧
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ h =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (x ≫ f))) := by
  let : Algebra (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo x)).hom.toAlgebra
  let : Algebra (S.residueField ((x ≫ f) (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo (x ≫ f))).hom.toAlgebra
  have hΩx : algebraMap (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo x)).hom := by
    exact RingHom.algebraMap_toAlgebra _
  have hΩxf : algebraMap (S.residueField ((x ≫ f) (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo (x ≫ f))).hom := by
    exact RingHom.algebraMap_toAlgebra _
  obtain ⟨hlocalx, _, _, _, hxx⟩ := strictHenselizationResidue x hΩx
  obtain ⟨hlocalxf, _, _, _, hxff⟩ :=
    strictHenselizationResidue (x ≫ f) hΩxf
  let : IsLocalRing (strictHenselizationRing x) := hlocalx
  let : IsLocalRing (strictHenselizationRing (x ≫ f)) := hlocalxf
  obtain ⟨σx, hσx, _⟩ := hxx
  obtain ⟨σxf, hσxf, _⟩ := hxff
  obtain ⟨_, hdata⟩ := strictHenselizationFunctoriality f x (x ≫ f) rfl hΩxf hΩx
      σxf σx hσxf.1 hσx.1
  obtain ⟨h, hlocal, hbase, hpoint, huniq, _⟩ := hdata
  let hs : strictHenselizationScheme x ⟶ strictHenselizationScheme (x ≫ f) :=
    Spec.map h
  have hsbase : hs ≫ strictHenselizationStructuralMap (x ≫ f) =
      strictHenselizationStructuralMap x ≫ f := by
    exact hbase
  have hevalx := evaluation_eq_of_pointed x _ hσx.1
  have hevalxf := evaluation_eq_of_pointed (x ≫ f) _ hσxf.1
  have hpoint' :
      strictHenselizationPointEvaluation (x ≫ f) =
        (strictHenselizationPointEvaluation x).comp h.hom := by
    simpa only [hevalx, hevalxf] using hpoint
  have hspoint : Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ hs =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (x ≫ f))) := by
    change _ ≫ Spec.map h = _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hpoint'.symm
  refine ⟨hs, ⟨hsbase, hspoint⟩, ?_⟩
  intro h' hh'
  obtain ⟨hbase', hpoint'⟩ := hh'
  let r : strictHenselizationRing (x ≫ f) ⟶ strictHenselizationRing x :=
    Spec.preimage h'
  have hr : Spec.map r = h' := Spec.map_preimage h'
  have hrpoint : strictHenselizationPointEvaluation (x ≫ f) =
      (strictHenselizationPointEvaluation x).comp r.hom := by
    have heq : CommRingCat.ofHom (strictHenselizationPointEvaluation (x ≫ f)) =
        r ≫ CommRingCat.ofHom (strictHenselizationPointEvaluation x) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hr]
      exact hpoint'.symm
    exact congrArg CommRingCat.Hom.hom heq
  have hrlocal : IsLocalHom r.hom := by
    have heval_local : IsLocalHom (strictHenselizationPointEvaluation (x ≫ f)) := by
      rw [← hevalxf]
      infer_instance
    have : IsLocalHom ((strictHenselizationPointEvaluation x).comp r.hom) :=
      hrpoint ▸ heval_local
    exact isLocalHom_of_comp r.hom (strictHenselizationPointEvaluation x)
  have hrh : r = h := huniq r hrlocal (hr ▸ hbase') (by
    simpa only [hevalx, hevalxf] using hrpoint)
  exact hr.symm.trans (congrArg Spec.map hrh)

end AlgebraicGeometry.Scheme
