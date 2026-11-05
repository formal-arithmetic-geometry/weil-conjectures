/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictLocalAbelianTotalExchange
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedFiberComparison
import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedLift
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationCanonicalMap

/-! # Local strict-henselian stalk criterion for exchange

Source: Stacks Project, Tag 0EZU, lemma-base-change-f-star-general-stalks
(blueprint: lem-weil-pbc-exchange-strict-local-cohomology-stalk-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluation_local
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) [IsLocalRing (Scheme.strictHenselizationRing y)] :
    IsLocalHom (Scheme.strictHenselizationRingPointEvaluation y) := by
  let : Algebra (Y.residueField (y (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo y)).hom.toAlgebra
  let e := Scheme.smallStrictHenselizationColimitIso y
  let ψ : Scheme.strictHenselizationRing y →+* _ :=
    (Scheme.strictHenselizationPointEvaluationToSep y rfl).comp e.hom.hom
  have : IsLocalHom ψ := IsLocalHom.of_surjective ψ
    ((Scheme.strictHenselizationPointEvaluationToSep_surjective y rfl).comp
      e.commRingCatIsoToRingEquiv.surjective)
  let ι : separableClosure (Y.residueField (y (IsLocalRing.closedPoint Ω))) Ω →+* Ω :=
    (IntermediateField.val _).toRingHom
  have : IsLocalHom ι := inferInstance
  change IsLocalHom (ι.comp ψ)
  infer_instance

private theorem localization_model_transport
    {Y Z : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s t : Spec (.of Ω) ⟶ Y) (h : s = t)
    (e : Z ≅ Scheme.strictLocalization s) :
    ∃ e' : Z ≅ Scheme.strictLocalization t,
      e'.hom ≫ Scheme.strictLocalizationToBase t =
        e.hom ≫ Scheme.strictLocalizationToBase s := by
  subst t
  exact ⟨e, rfl⟩

private theorem bijective_conjugate
    {A B C D : Type*} (f : A → B) (g : C → D)
    (e : A ≃ C) (e' : B ≃ D) (h : ∀ x, e' (f x) = g (e x)) :
    Function.Bijective f ↔ Function.Bijective g := by
  have hh : e' ∘ f = g ∘ e := funext h
  rw [← Function.Bijective.of_comp_iff' e'.bijective f, hh]
  exact Function.Bijective.of_comp_iff g e.bijective

end AlgebraicGeometry.Etale
