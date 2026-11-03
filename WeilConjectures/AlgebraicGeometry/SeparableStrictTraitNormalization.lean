/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationCanonicalMap
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import WeilConjectures.AlgebraicGeometry.StrictLocalComparisonIndEtale
import WeilConjectures.AlgebraicGeometry.GeometricStrictLocalStalkPresentation
import WeilConjectures.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Mathlib.RingTheory.DedekindDomain.Factorization
import WeilConjectures.RingTheory.StrictHenselizationTrait
import WeilConjectures.RingTheory.FiniteLocalHenselian
import WeilConjectures.RingTheory.FinitePresentationDescent
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import WeilConjectures.RingTheory.IntegralClosureIndEtaleBaseChange
import WeilConjectures.AlgebraicGeometry.Curve.BoundaryNeighbourhood
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme

/-! # Separable normalization of a strict local smooth trait

Source: Stacks Project, Algebra, Tags 032L, 04GH and 05WR; Varieties, Tag 0B8Y;
blueprint `det-tf-restriction-zero-covers`, proof (i)--(ii).
(blueprint: lem-trf-separable-strict-trait-normalization).
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry.Scheme

private theorem indEtale_equiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) : e.toRingHom.IndEtale := by
  rw [RingHom.IndEtale.iff_ind_etale]
  exact MorphismProperty.le_ind _ _ (RingHom.Etale.of_bijective e.bijective)

private theorem indEtale_across {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.IndEtale) : φ.IndEtaleAcrossUniverses := by
  exact (indEtale_equiv ULift.ringEquiv.symm).comp
    (hφ.comp (indEtale_equiv ULift.ringEquiv))

private theorem spec_strict_transport {C : Scheme.{u}} {k : Type u}
    [Field k] [IsAlgClosed k] (x y : Spec (.of k) ⟶ C) (h : x = y) :
    Spec.map (eqToHom (congrArg strictHenselizationRing h)) =
      eqToHom (congrArg strictHenselizationScheme h.symm) := by
  subst y
  change Spec.map (𝟙 (strictHenselizationRing x)) =
    𝟙 (Spec (strictHenselizationRing x))
  exact Spec.map_id _

private theorem strict_affine_structural_iso
    (T k : Type u) [CommRing T] [IsStrictlyHenselianLocalRing T]
    [Field k] [IsAlgClosed k] (ε : T →+* k) [IsLocalHom ε] :
    IsIso (strictHenselizationStructuralMap (Spec.map (CommRingCat.ofHom ε))) := by
  let x : Spec (.of k) ⟶ Spec (.of T) := Spec.map (CommRingCat.ofHom ε)
  let H := strictHenselizationRing x
  obtain ⟨hH, _⟩ := AlgebraicGeometry.strictHenselizationLocalStructure x
  let := hH
  let α : CommRingCat.of T ⟶ H := Spec.preimage (strictHenselizationStructuralMap x)
  have hα : Spec.map α = strictHenselizationStructuralMap x := Spec.map_preimage _
  let : Algebra T H := α.hom.toAlgebra
  have he : (strictHenselizationPointEvaluation x).comp α.hom = ε := by
    have heq : α ≫ CommRingCat.ofHom (strictHenselizationPointEvaluation x) =
        CommRingCat.ofHom ε := by
      apply Spec.map_injective
      rw [Spec.map_comp, hα]
      exact strictHenselizationClosedLift_over x
    exact congrArg CommRingCat.Hom.hom heq
  have : IsLocalHom ((strictHenselizationPointEvaluation x).comp α.hom) := he ▸ inferInstance
  have : IsLocalHom α.hom := isLocalHom_of_comp α.hom (strictHenselizationPointEvaluation x)
  have : Algebra.IndEtale T H :=
    smallStrictHenselization_indEtale_of_affine_chart x (.of T) (𝟙 _) ⟨_, rfl⟩
      (Iso.refl _) α.hom (by
        change Spec.map α ≫ 𝟙 _ = 𝟙 _ ≫ strictHenselizationStructuralMap x
        simpa using hα)
  have : Algebra.WeaklyEtale T H := inferInstance
  have : IsIso α := (ConcreteCategory.isIso_iff_bijective α).mpr
    Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing
  rw [← hα]
  infer_instance

private theorem strictLocal_affine_indEtale_iso
    (A B : CommRingCat.{u}) (φ : A ⟶ B) (hind : φ.hom.IndEtaleAcrossUniverses)
    {k : Type u} [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ Spec B) :
    IsIso (strictHenselizationMap (Spec.map φ) t) := by
  let h : strictHenselizationRing (t ≫ Spec.map φ) ⟶ strictHenselizationRing t :=
    Spec.preimage (strictHenselizationMap (Spec.map φ) t)
  have hh : Spec.map h = strictHenselizationMap (Spec.map φ) t := Spec.map_preimage _
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, hA, hB, hlocal, _⟩ :=
    strictLocalComparison_indEtale (Spec.map φ) t A B (𝟙 _) (𝟙 _)
      ⟨_, rfl⟩ ⟨_, rfl⟩ φ.hom (by
        change Spec.map φ ≫ 𝟙 _ = 𝟙 _ ≫ Spec.map φ
        exact (Category.comp_id _).trans (Category.id_comp _).symm) hind h hh
  let := hA
  let := hB
  let := hlocal
  let : Algebra (strictHenselizationRing (t ≫ Spec.map φ)) (strictHenselizationRing t) :=
    h.hom.toAlgebra
  have hindh := (hab a b ha hb).2.2.2.2
  have hweak : Algebra.WeaklyEtale
      (strictHenselizationRing (t ≫ Spec.map φ)) (strictHenselizationRing t) := by
    let : Algebra (ULift.{u} (strictHenselizationRing (t ≫ Spec.map φ)))
        (ULift.{u} (strictHenselizationRing t)) :=
      ULift.algebra' (strictHenselizationRing (t ≫ Spec.map φ))
        (ULift.{u} (strictHenselizationRing t))
    apply Algebra.WeaklyEtale.ulift_iff.mp
    apply RingHom.weaklyEtale_algebraMap_iff.mp
    exact hindh.weaklyEtale
  let := hweak
  have hbij : Function.Bijective h.hom :=
    Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing
  let e := (RingEquiv.ofBijective h.hom hbij).toCommRingCatIso
  have he : e.hom = h := rfl
  rw [← hh, ← he]
  infer_instance

/-- Identify a pointed affine ind-etale chart of a strictly henselian local ring,
with its structural map, evaluation, and the specified canonical-map square. -/
private theorem affine_strict_comparison_scheme_square
    (C : Scheme.{u}) (B R S : CommRingCat.{u}) [IsStrictlyHenselianLocalRing S]
    (g : Spec B ⟶ C) (b : B ⟶ S) (hind : b.hom.IndEtaleAcrossUniverses)
    {k : Type u} [Field k] [IsAlgClosed k]
    (ε : S →+* k) [IsLocalHom ε]
    (x₀ : Spec (.of k) ⟶ C) (e₀ : strictHenselizationRing x₀ ≃+* R)
    (r : R ⟶ S)
    (hbase : Spec.map b ≫ g = Spec.map r ≫
      Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫ strictHenselizationStructuralMap x₀)
    (hpoint : Spec.map (CommRingCat.ofHom ε) ≫ Spec.map r ≫
      Spec.map (CommRingCat.ofHom e₀.toRingHom) =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x₀))) :
    ∃ (h₁ : (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map b) ≫ g = x₀)
      (e₁ : strictHenselizationRing
        (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map b) ≃+* S),
      Spec.map (CommRingCat.ofHom e₁.toRingHom) ≫
          strictHenselizationStructuralMap
            (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map b) = Spec.map b ∧
      Spec.map (CommRingCat.ofHom ε) ≫ Spec.map (CommRingCat.ofHom e₁.toRingHom) =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation
          (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map b))) ∧
      Spec.map (CommRingCat.ofHom e₁.toRingHom) ≫
          strictHenselizationMap g (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map b) =
        Spec.map r ≫ Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫
          eqToHom (congrArg strictHenselizationScheme h₁.symm) := by
  classical
  let t : Spec (.of k) ⟶ Spec S := Spec.map (CommRingCat.ofHom ε)
  let x₁ := t ≫ Spec.map b
  have h₁ : x₁ ≫ g = x₀ := by
    change (t ≫ Spec.map b) ≫ g = x₀
    rw [Category.assoc, hbase, ← Category.assoc, ← Category.assoc]
    change (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map r ≫
      Spec.map (CommRingCat.ofHom e₀.toRingHom)) ≫ _ = _
    rw [hpoint, strictHenselizationClosedLift_over]
  refine ⟨h₁, ?_⟩
  subst x₀
  have : IsIso (strictHenselizationStructuralMap t) := strict_affine_structural_iso S k ε
  have : IsIso (strictHenselizationMap (Spec.map b) t) :=
    strictLocal_affine_indEtale_iso B S b hind t
  let v : Spec S ⟶ strictHenselizationScheme x₁ :=
    inv (strictHenselizationStructuralMap t) ≫ strictHenselizationMap (Spec.map b) t
  have : IsIso v := inferInstance
  have hvbase : v ≫ strictHenselizationStructuralMap x₁ = Spec.map b := by
    dsimp only [v]
    rw [Category.assoc, strictHenselizationMap_over, IsIso.inv_hom_id_assoc]
  have hteval : t ≫ inv (strictHenselizationStructuralMap t) =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation t)) := by
    apply (cancel_mono (strictHenselizationStructuralMap t)).mp
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      strictHenselizationClosedLift_over]
  have hvpoint : t ≫ v =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x₁)) := by
    dsimp only [v]
    rw [← Category.assoc, hteval]
    exact (Classical.choose_spec (strictHenselizationMap_existsUnique (Spec.map b) t)).1.2
  let w := inv v ≫ Spec.map r ≫ Spec.map (CommRingCat.ofHom e₀.toRingHom)
  have hw : w = strictHenselizationMap (g) x₁ := by
    apply (Classical.choose_spec (strictHenselizationMap_existsUnique (g) x₁)).2 w
    constructor
    · dsimp only [w]
      rw [Category.assoc, Category.assoc, ← hbase, ← Category.assoc,
        ← hvbase, IsIso.inv_hom_id_assoc]
    · have hcancel : v ≫ w =
          Spec.map r ≫ Spec.map (CommRingCat.ofHom e₀.toRingHom) := by
        dsimp only [w]
        rw [IsIso.hom_inv_id_assoc]
      calc
        _ = (t ≫ v) ≫ w := congrArg (fun m ↦ m ≫ w) hvpoint.symm
        _ = t ≫ (v ≫ w) := Category.assoc _ _ _
        _ = _ := (congrArg (fun m ↦ t ≫ m) hcancel).trans hpoint
  have hv : v ≫ strictHenselizationMap (g) x₁ =
      Spec.map r ≫ Spec.map (CommRingCat.ofHom e₀.toRingHom) := by
    rw [← hw]
    dsimp only [w]
    rw [IsIso.hom_inv_id_assoc]
  let h : strictHenselizationRing x₁ ⟶ S := Spec.preimage v
  have : IsIso (Scheme.Spec.map h.op) := by
    change IsIso (Spec.map h)
    rw [show Spec.map h = v from Spec.map_preimage _]
    infer_instance
  have : IsIso h := (isIso_op_iff h).mp (isIso_of_reflects_iso h.op Scheme.Spec)
  let e₁ := (asIso h).commRingCatIsoToRingEquiv
  have he : Spec.map (CommRingCat.ofHom e₁.toRingHom) = v := Spec.map_preimage _
  refine ⟨e₁, ?_, ?_, ?_⟩
  · rw [he]
    exact hvbase
  · rw [he]
    exact hvpoint
  rw [he]
  simpa only [eqToHom_refl, Category.comp_id] using hv

/-- Read the generic canonical scheme square on coordinate rings. -/
private theorem affine_strict_comparison
    (C : Scheme.{u}) (B R S : CommRingCat.{u}) [IsStrictlyHenselianLocalRing S]
    (g : Spec B ⟶ C) (b : B ⟶ S) (hind : b.hom.IndEtaleAcrossUniverses)
    {k : Type u} [Field k] [IsAlgClosed k]
    (ε : S →+* k) [IsLocalHom ε]
    (x₀ : Spec (.of k) ⟶ C) (e₀ : strictHenselizationRing x₀ ≃+* R)
    (r : R ⟶ S)
    (hbase : Spec.map b ≫ g = Spec.map r ≫
      Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫ strictHenselizationStructuralMap x₀)
    (hpoint : Spec.map (CommRingCat.ofHom ε) ≫ Spec.map r ≫
      Spec.map (CommRingCat.ofHom e₀.toRingHom) =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x₀))) :
    ∃ (h₁ : (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map b) ≫ g = x₀)
      (e₁ : strictHenselizationRing
        (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map b) ≃+* S),
      Spec.map (CommRingCat.ofHom e₁.toRingHom) ≫
          strictHenselizationStructuralMap
            (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map b) = Spec.map b ∧
      Spec.map (CommRingCat.ofHom ε) ≫ Spec.map (CommRingCat.ofHom e₁.toRingHom) =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation
          (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map b))) ∧
      ∀ z : strictHenselizationRing
          ((Spec.map (CommRingCat.ofHom ε) ≫ Spec.map b) ≫ g),
        e₁ ((Spec.preimage (strictHenselizationMap (g)
          (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map b))).hom z) =
            r.hom (e₀ ((eqToHom (congrArg strictHenselizationRing h₁)).hom z)) := by
  obtain ⟨h₁, e₁, hbase', hpoint', hsq⟩ :=
    affine_strict_comparison_scheme_square C B R S g b hind ε x₀ e₀ r hbase hpoint
  refine ⟨h₁, e₁, hbase', hpoint', ?_⟩
  subst x₀
  simp only [eqToHom_refl, Category.comp_id] at hsq
  have heq : Spec.preimage (strictHenselizationMap g
        (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map b)) ≫
      CommRingCat.ofHom e₁.toRingHom = CommRingCat.ofHom e₀.toRingHom ≫ r := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    exact hsq
  intro z
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom heq) z

private theorem spec_map_identity_point (R : CommRingCat.{u})
    {k : Type u} [CommRing k] (ε : R →+* k) :
    Spec.map (CommRingCat.ofHom ε) ≫ Spec.map (𝟙 R) ≫ Spec.map (𝟙 R) =
      Spec.map (CommRingCat.ofHom ε) := by
  cases R
  simp only [Spec.map_id, Category.comp_id]

/-- The initial pointed affine chart comparison, with the identity on its strict local ring. -/
private theorem initial_affine_strict_comparison
    {C : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ C) [IsStrictlyHenselianLocalRing (strictHenselizationRing x)]
    [IsLocalHom (strictHenselizationPointEvaluation x)]
    (A : CommRingCat.{u}) (p : Spec A ⟶ C) (a : A ⟶ strictHenselizationRing x)
    (hind : a.hom.IndEtaleAcrossUniverses)
    (hbase : Spec.map a ≫ p = strictHenselizationStructuralMap x) :
    ∃ (h₀ : (Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫
        Spec.map a) ≫ p = x)
      (e₀ : strictHenselizationRing
        (Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ Spec.map a) ≃+*
        strictHenselizationRing x),
      Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫ strictHenselizationStructuralMap
        (Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ Spec.map a) =
          Spec.map a ∧
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫
        Spec.map (CommRingCat.ofHom e₀.toRingHom) =
          Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation
            (Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ Spec.map a))) ∧
      ∀ z : strictHenselizationRing
          ((Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ Spec.map a) ≫ p),
        e₀ ((Spec.preimage (strictHenselizationMap p
          (Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫
            Spec.map a))).hom z) =
          (eqToHom (congrArg strictHenselizationRing h₀)).hom z := by
  let R := strictHenselizationRing x
  apply affine_strict_comparison C A R R p a hind
    (strictHenselizationPointEvaluation x) x (RingEquiv.refl R) (𝟙 R)
  · change Spec.map a ≫ p = Spec.map (𝟙 R) ≫
      Spec.map (𝟙 R) ≫ strictHenselizationStructuralMap x
    simpa only [Spec.map_id, Category.id_comp] using hbase
  · change Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫
      Spec.map (𝟙 R) ≫ Spec.map (𝟙 R) =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x))
    exact spec_map_identity_point R (strictHenselizationPointEvaluation x)

/-- Transport the two chart squares using only abstract coefficient rings. -/
private theorem affine_chart_squares
    (A B R S : CommRingCat.{u}) (c : A ⟶ B) (a : A ⟶ R) (b : B ⟶ S) (r : R ⟶ S)
    (hab : c ≫ b = a ≫ r)
    {k : Type u} [Field k] [IsAlgClosed k]
    (x₀ : Spec (.of k) ⟶ Spec A) (e₀ : strictHenselizationRing x₀ ≃+* R)
    (εR : R →+* k) (εS : S →+* k)
    (hbase : Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫
      strictHenselizationStructuralMap x₀ = Spec.map a)
    (hpoint : Spec.map (CommRingCat.ofHom εR) ≫
      Spec.map (CommRingCat.ofHom e₀.toRingHom) =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x₀)))
    (hε : εS.comp r.hom = εR) :
    (Spec.map b ≫ Spec.map c = Spec.map r ≫
      Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫ strictHenselizationStructuralMap x₀) ∧
    (Spec.map (CommRingCat.ofHom εS) ≫ Spec.map r ≫
      Spec.map (CommRingCat.ofHom e₀.toRingHom) =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x₀))) := by
  constructor
  · rw [← Spec.map_comp, hab, Spec.map_comp]
    exact congrArg (fun z ↦ Spec.map r ≫ z) hbase.symm
  · have hεspec : Spec.map (CommRingCat.ofHom εS) ≫ Spec.map r =
        Spec.map (CommRingCat.ofHom εR) := by
      rw [← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom (εS.comp r.hom)) = _
      rw [hε]
    rw [← Category.assoc, hεspec]
    exact hpoint

/-- Convert the canonical ring comparison into its spectrum square. -/
private theorem canonical_comparison_spec
    {C C₀ : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (p : C₀ ⟶ C) (x₀ : Spec (.of k) ⟶ C₀) (x : Spec (.of k) ⟶ C)
    (h₀ : x₀ ≫ p = x) (e₀ : strictHenselizationRing x₀ ≃+* strictHenselizationRing x)
    (hcan : ∀ z : strictHenselizationRing (x₀ ≫ p),
      e₀ ((Spec.preimage (strictHenselizationMap p x₀)).hom z) =
        (eqToHom (congrArg strictHenselizationRing h₀)).hom z) :
    Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫ strictHenselizationMap p x₀ =
      eqToHom (congrArg strictHenselizationScheme h₀.symm) := by
  have hring : Spec.preimage (strictHenselizationMap p x₀) ≫
      CommRingCat.ofHom e₀.toRingHom = eqToHom (congrArg strictHenselizationRing h₀) := by
    ext z
    exact hcan z
  have hspec := congrArg Spec.map hring
  rw [Spec.map_comp, Spec.map_preimage, spec_strict_transport _ _ h₀] at hspec
  exact hspec

/-- The defining small limit cone presents the structural morphism as pro-affine-etale. -/
private theorem strict_structural_proAffineEtale
    {C : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ C) : proAffineEtale (strictHenselizationStructuralMap x) := by
  classical
  let := (strictHenselization_properties x).2.1
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods x)).inverse
  let D := (strictHenselizationAffineDiagram x).op ⋙ Scheme.Spec
  let t : D ⟶ (Functor.const _).obj C :=
    { app j := Spec.map (ΓSpecIso (N.obj j.unop.unop).1.left.unop).inv ≫
        ((AffineEtale.Spec C).obj (N.obj j.unop.unop).1).hom
      naturality i j v := by
        let g := (N.map v.unop.unop).1.left.unop
        have hg := congrArg Spec.map (ΓSpecIso_inv_naturality g)
        simp only [Spec.map_comp] at hg
        have hw : Spec.map g ≫ ((AffineEtale.Spec C).obj (N.obj j.unop.unop).1).hom =
            ((AffineEtale.Spec C).obj (N.obj i.unop.unop).1).hom :=
          (N.map v.unop.unop).1.w
        change Spec.map (Spec.map g).appTop ≫
          (Spec.map (ΓSpecIso (N.obj j.unop.unop).1.left.unop).inv ≫ _) = _ ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, ← hg, Category.assoc, hw] }
  refine ⟨_, inferInstance, inferInstance, D, t,
    (strictHenselizationCone x).π, (strictHenselization_properties x).2.2.some, ?_⟩
  intro j
  refine ⟨⟨?_, ⟨?_, trivial⟩⟩, ?_⟩
  · dsimp only [t]
    infer_instance
  · change IsAffine (Spec _)
    infer_instance
  · exact (exists_strictHenselizationStructuralMap x).choose_spec j.unop.unop

private theorem chart_indEtale
    {C : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ C) (A : CommRingCat.{u})
    (p : Spec A ⟶ C) [Etale p] (a : A ⟶ strictHenselizationRing x)
    (ha : Spec.map a ≫ p = strictHenselizationStructuralMap x) : a.hom.IndEtale := by
  apply proAffineEtale_Spec_iff.mp
  apply MorphismProperty.of_postcomp _ (Spec.map a) p (proAffineEtale.of_isAffine p)
  rw [ha]
  exact strict_structural_proAffineEtale x

private theorem affine_coeff_chart
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (x : Spec (.of k) ⟶ C) (s : Finset (strictHenselizationRing x)) :
    ∃ (B : CommRingCat.{u}) (p : Spec B ⟶ C) (y : Spec (.of k) ⟶ Spec B)
      (a : B ⟶ strictHenselizationRing x),
      Etale p ∧ IsCurve (p ≫ f) ∧ Smooth (p ≫ f) ∧ y ≫ p = x ∧
      Spec.map a ≫ p = strictHenselizationStructuralMap x ∧
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ Spec.map a = y ∧
      ∀ r ∈ s, r ∈ Set.range a := by
  classical
  have := (strictHenselization_properties x).2.1
  let F := strictHenselizationAffineDiagram x
  obtain ⟨j, hj⟩ := CommRingCat.exists_stage_of_finset (colimit.isColimit F) s
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods x)).inverse.obj j.unop
  let B := N.1.left.unop
  let p : Spec B ⟶ C := ((AffineEtale.Spec C).obj N.1).hom
  let y : Spec (.of k) ⟶ Spec B := N.2.left
  let a : B ⟶ strictHenselizationRing x :=
    (ΓSpecIso B).inv ≫ colimit.ι F j
  have hp : Etale p := inferInstance
  have : Smooth (p ≫ f) := inferInstance
  have hcurve : IsCurve (p ≫ f) :=
    { krullDim_le_one :=
      (topologicalKrullDim_le_of_continuous p.continuous fun _ _ ↦
        p.eq_of_specializes_of_apply_eq).trans (IsCurve.krullDim_le_one (f := f)) }
  refine ⟨B, p, y, a, hp, hcurve, inferInstance, Over.w N.2, ?_, ?_, ?_⟩
  · have hstruct := (exists_strictHenselizationStructuralMap x).choose_spec j.unop
    change Spec.map (colimit.ι (strictHenselizationAffineDiagram x) j) ≫
      Spec.map (ΓSpecIso B).inv ≫ p = strictHenselizationStructuralMap x at hstruct
    simpa only [a, Spec.map_comp, Category.assoc] using hstruct
  · have hpoint := strictHenselizationPointEvaluation_pointed x j.unop
    rw [isoSpec_Spec_inv] at hpoint
    change (Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫
      Spec.map (colimit.ι (strictHenselizationAffineDiagram x) j)) ≫
        Spec.map (ΓSpecIso B).inv = y at hpoint
    simpa only [a, Spec.map_comp, ← Category.assoc] using hpoint
  · intro r hr
    obtain ⟨b, hb⟩ := hj r hr
    let b' : Γ(Spec B, ⊤) := b
    refine ⟨(ΓSpecIso B).hom b', ?_⟩
    change (colimit.ι F j) ((ΓSpecIso B).inv ((ΓSpecIso B).hom b')) = r
    exact (congrArg (colimit.ι F j) ((ΓSpecIso B).hom_inv_id_apply b')).trans hb

/-- Retain the integral component containing the closed point; a local spectrum
factors through every open containing the image of its closed point. -/
private theorem integral_coeff_chart
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (x : Spec (.of k) ⟶ C) (s : Finset (strictHenselizationRing x)) :
    ∃ (A : CommRingCat.{u}) (_ : IsDomain A)
      (p : Spec A ⟶ C) (y : Spec (.of k) ⟶ Spec A)
      (a : A ⟶ strictHenselizationRing x),
      Etale p ∧ IsConnectedCurve (p ≫ f) ∧ Smooth (p ≫ f) ∧ y ≫ p = x ∧
      Spec.map a ≫ p = strictHenselizationStructuralMap x ∧
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ Spec.map a = y ∧
      ∀ r ∈ s, r ∈ Set.range a := by
  classical
  obtain ⟨B, p, y, a, hp, hcurve, hsm, hxy, hbase, hpoint, hs⟩ :=
    affine_coeff_chart k C f x s
  let := hp
  let := hcurve
  let := hsm
  have : IsLocallyNoetherian (Spec B) := LocallyOfFiniteType.isLocallyNoetherian (p ≫ f)
  have : IsNoetherian (Spec B) := {}
  have : IsRegular (Spec B) := IsRegular.of_smooth (p ≫ f)
  obtain ⟨n, U, hclopen, _, hcover, hintegral⟩ := IsRegular.exists_isClopen_isIntegral (Spec B)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show y (IsLocalRing.closedPoint k) ∈ ⨆ j, U j from hcover.symm ▸ trivial)
  let V := U i
  have : IsIntegral V.toScheme := (hintegral i).1
  have : IsClosedImmersion V.ι :=
    .of_isPreimmersion _ (V.range_ι ▸ (hclopen i).1)
  have : IsAffine V.toScheme := isAffine_of_isAffineHom V.ι
  let A := Γ(V.toScheme, ⊤)
  have : IsDomain A := inferInstance
  let c : Spec (strictHenselizationRing x) ⟶ Spec B := Spec.map a
  obtain ⟨hl, _⟩ := AlgebraicGeometry.strictHenselizationLocalStructure x
  let := hl
  have hcclosed : c (IsLocalRing.closedPoint (strictHenselizationRing x)) ∈ V := by
    have : IsLocalHom (strictHenselizationPointEvaluation x) := by
      let : Algebra (C.residueField (x (IsLocalRing.closedPoint k))) k :=
        (descResidueField (stalkClosedPointTo x)).hom.toAlgebra
      let ψ := strictHenselizationPointEvaluationToSep x rfl
      have : IsLocalHom ψ := IsLocalHom.of_surjective ψ
        (strictHenselizationPointEvaluationToSep_surjective x rfl)
      let ι : separableClosure (C.residueField (x (IsLocalRing.closedPoint k))) k →+* k :=
        (IntermediateField.val _).toRingHom
      change IsLocalHom (ι.comp ψ)
      infer_instance
    have he := IsLocalRing.comap_closedPoint (strictHenselizationPointEvaluation x)
    have hh : c (IsLocalRing.closedPoint (strictHenselizationRing x)) =
        y (IsLocalRing.closedPoint k) :=
      (congrArg c he.symm).trans
        (congrArg (fun h ↦ h (IsLocalRing.closedPoint k)) hpoint)
    exact hh.symm ▸ hi
  have hcrange : Set.range c ⊆ Set.range V.ι := by
    rintro z ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint w).map c.continuous).mem_open
      (IsOpenImmersion.isOpen_range V.ι) (by rw [V.range_ι]; exact hcclosed)
  let cV : Spec (strictHenselizationRing x) ⟶ V.toScheme :=
    IsOpenImmersion.lift V.ι c hcrange
  have hcV : cV ≫ V.ι = c := IsOpenImmersion.lift_fac _ _ _
  have hyrange : Set.range y ⊆ Set.range V.ι := by
    rintro z ⟨w, rfl⟩
    have hw : w = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [hw, V.range_ι]
    exact hi
  let yV : Spec (.of k) ⟶ V.toScheme := IsOpenImmersion.lift V.ι y hyrange
  have hyV : yV ≫ V.ι = y := IsOpenImmersion.lift_fac _ _ _
  let q : Spec A ⟶ C := V.toScheme.isoSpec.inv ≫ V.ι ≫ p
  let y' : Spec (.of k) ⟶ Spec A := yV ≫ V.toScheme.isoSpec.hom
  let a' : A ⟶ strictHenselizationRing x := Spec.preimage (cV ≫ V.toScheme.isoSpec.hom)
  have ha' : Spec.map a' = cV ≫ V.toScheme.isoSpec.hom := Spec.map_preimage _
  have hq : Etale q := inferInstance
  have hsm' : Smooth (q ≫ f) := inferInstance
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IrreducibleSpace C := by
    have := IsConnectedCurve.connectedSpace' f
    have : IsRegular C := IsRegular.of_smooth f
    exact IsRegular.irreducibleSpace C
  have : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  have : SmoothOfRelativeDimension 1 (q ≫ f) := by
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (q ≫ f))
  have : IsIntegral (Spec A) := inferInstance
  have hconn : IsConnectedCurve (q ≫ f) :=
    { krullDim_le_one := topologicalKrullDim_le_of_smoothOfRelativeDimension (q ≫ f) 1
      connectedSpace := inferInstance
      krullDim_eq_one := topologicalKrullDim_eq_of_smoothOfRelativeDimension (q ≫ f) 1 }
  refine ⟨A, inferInstance, q, y', a', hq, hconn, hsm', ?_, ?_, ?_, ?_⟩
  · dsimp only [y', q]
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hyV, hxy]
  · rw [ha']
    dsimp only [q]
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hcV]
    exact hbase
  · rw [ha']
    dsimp only [y']
    rw [← Category.assoc]
    apply congrArg (fun m : Spec (.of k) ⟶ V.toScheme ↦ m ≫ V.toScheme.isoSpec.hom)
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, hcV, hyV]
    exact hpoint
  · intro r hr
    obtain ⟨w, hw⟩ := hs r hr
    let d : B ⟶ A := Spec.preimage (V.toScheme.isoSpec.inv ≫ V.ι)
    have hd : d ≫ a' = a := by
      apply Spec.map_injective
      rw [Spec.map_comp, ha', Spec.map_preimage]
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact hcV
    exact ⟨d w, (congrArg (fun h ↦ h w) hd).trans hw⟩

/-- A chart carrying a uniformizer already gives the whole generic field after base change. -/
private theorem fraction_tensor_equiv
    (A R F K : Type u) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Field K]
    [Algebra A F] [IsFractionRing A F] [Algebra A R]
    [Algebra R K] [IsFractionRing R K]
    (hinj : Function.Injective (algebraMap A R)) (t : A)
    (ht : Irreducible (algebraMap A R t)) :
    Nonempty (R ⊗[A] F ≃ₐ[R] K) := by
  let M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  have hM : M ≤ nonZeroDivisors R := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by
      simpa only [map_zero] using hinj.ne (nonZeroDivisors.ne_zero ha))
  have ht0 : t ≠ 0 := by
    intro h
    exact ht.ne_zero (h ▸ map_zero _)
  have htM : algebraMap A R t ∈ M := ⟨t, mem_nonZeroDivisors_of_ne_zero ht0, rfl⟩
  have : IsFractionRing R (R ⊗[A] F) := by
    apply IsLocalization.of_le M (nonZeroDivisors R) hM
    intro r hr
    obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hr) ht
    rw [map_mul, map_pow]
    exact (v.isUnit.map _).mul
      ((IsLocalization.map_units (R ⊗[A] F) ⟨_, htM⟩).pow n)
  exact ⟨IsLocalization.algEquiv (nonZeroDivisors R) (R ⊗[A] F) K⟩

private theorem adjoin_root_tensor_equiv
    (A R F K L : Type u) [CommRing A] [CommRing R] [Field F] [Field K] [Field L]
    [Algebra A R] [Algebra A F] [Algebra R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L]
    (e : R ⊗[A] F ≃ₐ[R] K) (pb : PowerBasis K L) (p : Polynomial F)
    (hp : p.map (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) =
      minpoly K pb.gen) :
    Nonempty (R ⊗[A] AdjoinRoot p ≃ₐ[R] L) := by
  let q := p.map (Algebra.TensorProduct.includeRight.toRingHom : F →+* R ⊗[A] F)
  have hq : Associated (q.map e.toRingHom) (minpoly K pb.gen) := by
    rw [Polynomial.map_map, hp]
  let eq := AdjoinRoot.mapAlgEquiv e q (minpoly K pb.gen) hq
  let eL := AdjoinRoot.equiv' (minpoly K pb.gen) pb (by simp) (minpoly.aeval K pb.gen)
  exact ⟨(AdjoinRoot.tensorAlgEquiv p q rfl).trans (eq.trans (eL.restrictScalars R))⟩

private theorem separable_extension_tensor_of_polynomial
    (A R F K L : Type u) [CommRing A] [CommRing R] [Field F] [Field K] [Field L]
    [Algebra A R] [Algebra A F] [Algebra R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [Algebra.IsSeparable K L]
    (e : R ⊗[A] F ≃ₐ[R] K) (pb : PowerBasis K L) (p : Polynomial F)
    (hp : p.map (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) =
      minpoly K pb.gen) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : Algebra A E),
      IsScalarTower A F E ∧ Module.Finite F E ∧ Algebra.IsSeparable F E ∧
      Nonempty (R ⊗[A] E ≃ₐ[R] L) := by
  let φ := e.toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom : F →+* R ⊗[A] F)
  have hmon : p.Monic := Polynomial.monic_of_injective φ.injective
    (hp.symm ▸ minpoly.monic pb.isIntegral_gen)
  have hirr : Irreducible p := Polynomial.Monic.irreducible_of_irreducible_map φ p hmon
    (hp.symm ▸ minpoly.irreducible pb.isIntegral_gen)
  have : Fact (Irreducible p) := ⟨hirr⟩
  let E := AdjoinRoot p
  have : Module.Finite F E := hmon.finite_adjoinRoot
  have hsep : p.Separable := (Polynomial.separable_map φ).mp
    (hp.symm ▸ Algebra.IsSeparable.isSeparable K pb.gen)
  have hroot : IsSeparable F (AdjoinRoot.root p) := by
    change (minpoly F (AdjoinRoot.root p)).Separable
    rw [AdjoinRoot.minpoly_root hmon.ne_zero, hmon.leadingCoeff]
    simpa using hsep
  have hsub : Algebra.adjoin F ({AdjoinRoot.root p} : Set E) ≤
      (separableClosure F E).toSubalgebra :=
    Algebra.adjoin_le (by rintro z (rfl : z = _); exact hroot)
  have htop : Algebra.adjoin F ({AdjoinRoot.root p} : Set E) = ⊤ :=
    (AdjoinRoot.powerBasis hmon.ne_zero).adjoin_gen_eq_top
  have : Algebra.IsSeparable F E := ⟨fun z ↦ hsub (htop.symm ▸ Algebra.mem_top)⟩
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, adjoin_root_tensor_equiv A R F K L e pb p hp⟩

private theorem integral_closure_tensor_equiv
    (A R E L : Type u) [CommRing A] [CommRing R] [CommRing E] [CommRing L]
    [Algebra A R] [Algebra A E] [Algebra R L]
    (hR : (algebraMap A R).IndEtaleAcrossUniverses)
    (e : R ⊗[A] E ≃ₐ[R] L) :
    ∃ eC : R ⊗[A] integralClosure A E ≃ₐ[R] integralClosure R L,
      ∀ (r : R) (b : integralClosure A E),
        (eC (r ⊗ₜ[A] b) : L) = e (r ⊗ₜ[A] (b : E)) := by
  let eC := (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure A R E)
    (RingHom.integralClosure_bijective_of_indEtale hR)).trans
      (AlgEquiv.mapIntegralClosure e)
  refine ⟨eC, ?_⟩
  intro r b
  simp [eC, TensorProduct.toIntegralClosure]

/-- The normalization chart map and its compatibility with the base-ring inclusion. -/
private theorem integral_closure_chart_map
    (A R : CommRingCat.{u}) (E L : Type u) [CommRing E] [CommRing L]
    [Algebra A E] [Algebra R L] (a : A ⟶ R) (hind : a.hom.IndEtale) :
    letI : Algebra A R := a.hom.toAlgebra
    ∀ _e : R ⊗[A] E ≃ₐ[R] L,
      ∃ b : CommRingCat.of (integralClosure A E) ⟶
          CommRingCat.of (integralClosure R L),
        b.hom.IndEtale ∧
        CommRingCat.ofHom (algebraMap A (integralClosure A E)) ≫ b =
          a ≫ CommRingCat.ofHom (algebraMap R (integralClosure R L)) := by
  let : Algebra A R := a.hom.toAlgebra
  intro e
  obtain ⟨eC, _⟩ :=
    integral_closure_tensor_equiv A R E L (indEtale_across a.hom hind) e
  let B := integralClosure A E
  let S := integralClosure R L
  let b : CommRingCat.of B ⟶ CommRingCat.of S :=
    CommRingCat.ofHom (eC.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  refine ⟨b, ?_, ?_⟩
  · let : Algebra B (R ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    have hi : (Algebra.TensorProduct.includeRight.toRingHom : B →+* R ⊗[A] B).IndEtale :=
      RingHom.IndEtale.isStableUnderBaseChange A R B (R ⊗[A] B) hind
    exact (indEtale_equiv eC.toRingEquiv).comp hi
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change eC (1 ⊗ₜ[A] algebraMap A B z) = algebraMap R S (a z)
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    exact eC.commutes (a z)

/-- Construct the curve as the spectrum of its actual integral-closure ring. -/
private theorem affine_normalization_model
    (k : Type u) [Field k] [IsAlgClosed k] (A : CommRingCat.{u}) [IsDomain A]
    (f : Spec A ⟶ Spec (.of k)) [IsCurve f] [Smooth f]
    (F E : Type u) [Field F] [Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [Module.Finite F E] [Algebra.IsSeparable F E] :
    let B := integralClosure A E
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    IsFinite g ∧ IsCurve (g ≫ f) ∧ Smooth (g ≫ f) := by
  classical
  have : IsIntegral (Spec A) := inferInstance
  have : Nonempty (⊤ : (Spec A).Opens) := ⟨⟨Classical.arbitrary (Spec A), trivial⟩⟩
  have : IsDedekindDomain Γ(Spec A, ⊤) :=
    isDedekindDomain_of_isAffineOpen f (isAffineOpen_top _)
  let e := (ΓSpecIso A).commRingCatIsoToRingEquiv
  have : IsNoetherianRing A := isNoetherianRing_of_ringEquiv _ e
  have : Ring.DimensionLEOne A := .of_ringEquiv e.symm
  have : IsIntegrallyClosed A := .of_equiv e
  have : IsDedekindDomain A := {}
  let B := integralClosure A E
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have : Module.Finite A B := IsIntegralClosure.finite A F E B
  have : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A F E B
  have hg : IsFinite g := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hdim : topologicalKrullDim (Spec (.of B)) ≤ 1 := by
    change topologicalKrullDim (PrimeSpectrum B) ≤ 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact_mod_cast (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 B))
  have : IsLocallyNoetherian (Spec (.of B)) := inferInstance
  have : IsRegular (Spec (.of B)) := IsRegular.of_isIntegrallyClosed_stalk
    (fun z ↦ ⟨inferInstance, isIntegrallyClosed_stalk_Spec B z⟩) hdim
  have : Smooth (g ≫ f) := smooth_of_isRegular _
  exact ⟨hg, { krullDim_le_one := hdim }, inferInstance⟩

/-- Descend an actual primitive polynomial and identify its entire tensor product with L. -/
private theorem field_extension_chart
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (x : Spec (.of k) ⟶ C) [IsDomain (strictHenselizationRing x)]
    [IsDiscreteValuationRing (strictHenselizationRing x)]
    (K L : Type u) [Field K] [Field L]
    [Algebra (strictHenselizationRing x) K]
    [IsFractionRing (strictHenselizationRing x) K] [Algebra K L]
    [Algebra (strictHenselizationRing x) L]
    [IsScalarTower (strictHenselizationRing x) K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] :
    ∃ (A : CommRingCat.{u}) (_ : IsDomain A)
      (p : Spec A ⟶ C) (a : A ⟶ strictHenselizationRing x),
      Etale p ∧ IsConnectedCurve (p ≫ f) ∧ Smooth (p ≫ f) ∧
      Spec.map a ≫ p = strictHenselizationStructuralMap x ∧ a.hom.IndEtale ∧
      letI : Algebra A (strictHenselizationRing x) := a.hom.toAlgebra
      ∃ (F E : Type u) (_ : Field F) (_ : Field E) (_ : Algebra A F)
        (_ : IsFractionRing A F) (_ : Algebra F E) (_ : Algebra A E),
        IsScalarTower A F E ∧ Module.Finite F E ∧ Algebra.IsSeparable F E ∧
        Nonempty ((strictHenselizationRing x) ⊗[A] E ≃ₐ[strictHenselizationRing x] L) := by
  classical
  let R := strictHenselizationRing x
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  let q := minpoly K pb.gen
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_irreducible R
  choose num den hden hfrac using fun c : K ↦ IsFractionRing.div_surjective R c
  let s := insert u (q.coeffs.biUnion fun c ↦ {num c, den c})
  obtain ⟨A, hA, p, y, a, hp, hconn, hsm, _, hbase, _, hs⟩ :=
    integral_coeff_chart k C f x s
  let := hA
  let := hp
  let : Algebra A R := a.hom.toAlgebra
  have hind : a.hom.IndEtale := chart_indEtale x A p a hbase
  have : Algebra.IndEtale A R := hind
  have : Algebra.WeaklyEtale A R := inferInstance
  have : Module.Flat A R := inferInstance
  have hinj : Function.Injective (algebraMap A R) := FaithfulSMul.algebraMap_injective A R
  obtain ⟨t, ht⟩ := hs u (Finset.mem_insert_self _ _)
  let F := FractionRing A
  obtain ⟨e⟩ := fraction_tensor_equiv A R F K hinj t (by
    have htu : a.hom t = u := ht
    exact htu.symm ▸ hu)
  let φ := e.toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom : F →+* R ⊗[A] F)
  have hφ (z : A) : φ (algebraMap A F z) = algebraMap R K (a z) := by
    change e (1 ⊗ₜ[A] algebraMap A F z) = _
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    exact e.commutes (a z)
  have hcoeff : (q.coeffs : Set K) ⊆ Set.range φ := by
    intro c hc
    have hn : num c ∈ s := Finset.mem_insert_of_mem
      (Finset.mem_biUnion.mpr ⟨c, hc, by simp⟩)
    have hd : den c ∈ s := Finset.mem_insert_of_mem
      (Finset.mem_biUnion.mpr ⟨c, hc, by simp⟩)
    obtain ⟨v, hv⟩ := hs _ hn
    obtain ⟨w, hw⟩ := hs _ hd
    refine ⟨algebraMap A F v / algebraMap A F w, ?_⟩
    rw [map_div₀, hφ, hφ, hv, hw]
    exact hfrac c
  obtain ⟨p₀, hp₀⟩ := (Polynomial.mem_lifts q).mp
    ((Polynomial.lifts_iff_coeffs_subset_range q).mpr hcoeff)
  obtain ⟨E, hE, algFE, algAE, htower, hfinite, hsep, he⟩ :=
    separable_extension_tensor_of_polynomial A R F K L e pb p₀ hp₀
  exact ⟨A, hA, p, a, hp, hconn, hsm, hbase, hind, F, E,
    inferInstance, hE, inferInstance, inferInstance, algFE, algAE, htower, hfinite, hsep, he⟩

private theorem normalization_algebra
    (R K L k : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R] [Field K] [Field L] [Field k] [IsAlgClosed k]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    (eR : IsLocalRing.ResidueField R ≃+* k) :
    ∃ (_ : IsDiscreteValuationRing (integralClosure R L)),
      IsStrictlyHenselianLocalRing (integralClosure R L) ∧
      (∃ e : IsLocalRing.ResidueField (integralClosure R L) ≃+* k,
        ∀ r : R, e (IsLocalRing.residue _ (algebraMap R (integralClosure R L) r)) =
          eR (IsLocalRing.residue R r)) ∧
      IsFractionRing (integralClosure R L) L ∧
      Nonempty (Module.Basis (Fin (Module.finrank K L)) R (integralClosure R L)) ∧
      IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) := by
  classical
  let S := integralClosure R L
  have : Module.Finite R S := IsIntegralClosure.finite R K L S
  have : IsLocalRing S :=
    IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain (R := R)
  have : HenselianLocalRing S := HenselianLocalRing.finite_local_henselian R S
  have : IsLocalHom (algebraMap R S) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 4 0).mp
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal S))
  have : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain R K L S
  have : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  have : FaithfulSMul R S := FaithfulSMul.of_field_isFractionRing R S K L
  have : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  have : IsDiscreteValuationRing S := by
    apply ((IsDiscreteValuationRing.TFAE S ?_).out 2 0).mp
      (show IsDedekindDomain S from inferInstance)
    intro hfield
    exact IsDiscreteValuationRing.not_isField R
      (isField_of_isIntegral_of_isField
        (FaithfulSMul.algebraMap_injective R S) hfield)
  have : IsAlgClosed (IsLocalRing.ResidueField R) := IsAlgClosed.of_ringEquiv k _ eR.symm
  let eRS : IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField S :=
    RingEquiv.ofBijective _ IsAlgClosed.algebraMap_bijective_of_isIntegral
  have : IsStrictlyHenselianLocalRing S := ⟨IsSepClosed.of_ringEquiv eRS⟩
  have : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  have : Module.Free R S := IsIntegralClosure.module_free R K L S
  refine ⟨inferInstance, inferInstance, ⟨eRS.symm.trans eR, ?_⟩, inferInstance,
    ⟨Module.finBasisOfFinrankEq R S (IsIntegralClosure.rank R K L S)⟩, ?_, ?_⟩
  · intro r
    change eR (eRS.symm (IsLocalRing.residue S (algebraMap R S r))) = _
    apply congrArg eR
    apply eRS.injective
    rw [eRS.apply_symm_apply]
    exact (IsLocalRing.ResidueField.algebraMap_residue r).symm
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

private theorem normalization_punctured_etale
    (R K L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [Module.Finite K L]
    [Algebra.IsSeparable K L]
    (u : R) (hu : IsLocalRing.maximalIdeal R = Ideal.span {u}) :
    Etale (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away u))))) := by
  classical
  let S := integralClosure R L
  let F := Localization.Away u
  have huirr : Irreducible u :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer u).mpr hu
  have : IsFractionRing R F :=
    IsDiscreteValuationRing.isFractionRing_of_isLocalization_away huirr
  let : Field F := IsFractionRing.toField R
  let e : F ≃ₐ[R] K := IsLocalization.algEquiv (nonZeroDivisors R) F K
  let : Algebra F K := e.toRingHom.toAlgebra
  let : Algebra F L := ((algebraMap K L).comp e.toRingHom).toAlgebra
  have : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R L r = algebraMap K L (e (algebraMap R F r))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply R K L]
  have : Module.Finite F K := RingHom.finite_algebraMap.mp
    (RingHom.Finite.of_surjective e.toRingHom e.surjective)
  have : Module.Finite F L := Module.Finite.trans K L
  have : Algebra.IsSeparable F L :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) (by
      ext r
      change algebraMap K L (e (e.symm r)) = algebraMap K L r
      rw [e.apply_symm_apply])
  have : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  have : Algebra.FinitePresentation F L := Algebra.FinitePresentation.of_finiteType.mp
    inferInstance
  have : Algebra.Etale F L := ⟨inferInstance, inferInstance⟩
  have hEtale : Etale (Spec.map (CommRingCat.ofHom (algebraMap F L))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) L :=
    IsIntegralClosure.isLocalization R K L S
  have : Algebra.IsPushout R S F L := Algebra.isPushout_of_isLocalization (nonZeroDivisors R) F S L
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S F L)
  apply (MorphismProperty.cancel_left_of_respectsIso @Etale hpb.isoPullback.hom
    (pullback.snd _ _)).mp
  rw [hpb.isoPullback_hom_snd]
  exact hEtale

private theorem normalization_uniformizer
    (R K L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [Module.Finite K L]
    [Algebra.IsSeparable K L] [IsDiscreteValuationRing (integralClosure R L)]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    (u : R) (ξ : integralClosure R L)
    (hu : IsLocalRing.maximalIdeal R = Ideal.span {u})
    (hξ : IsLocalRing.maximalIdeal (integralClosure R L) = Ideal.span {ξ}) :
    ∃ a : (integralClosure R L)ˣ,
      algebraMap R (integralClosure R L) u =
        (a : integralClosure R L) * ξ ^ Module.finrank K L := by
  classical
  let S := integralClosure R L
  have : Module.Finite R S := IsIntegralClosure.finite R K L S
  have : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  have : FaithfulSMul R S := FaithfulSMul.of_field_isFractionRing R S K L
  have : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  have : Module.Free R S := IsIntegralClosure.module_free R K L S
  let p := IsLocalRing.maximalIdeal R
  let q := IsLocalRing.maximalIdeal S
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hprimes : p.primesOver S = {q} := IsLocalRing.primesOver_eq S hp
  have hf : Finite (p.primesOver S) := by rw [hprimes]; infer_instance
  let : Fintype (p.primesOver S) := Fintype.ofFinite _
  let Q : p.primesOver S := Ideal.primesOver.mk p q
  have hQ (b : p.primesOver S) : b = Q := by
    apply Subtype.ext
    exact IsLocalRing.eq_maximalIdeal (Ideal.primesOver.isMaximal b)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p S
  have hdeg : q.ramificationIdx R * q.inertiaDeg R = Module.finrank R S := by
    rw [Finset.sum_eq_single Q] at hsum
    · exact hsum
    · intro b _ hb
      exact (hb (hQ b)).elim
    · simp
  have hinertia : q.inertiaDeg R = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal p q]
    change Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) = 1
    let e := LinearEquiv.ofBijective
      (Algebra.linearMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    rw [← e.finrank_eq, Module.finrank_self]
  have he : q.ramificationIdx R = Module.finrank K L := by
    rw [hinertia, mul_one, IsIntegralClosure.rank R K L S] at hdeg
    exact hdeg
  have hfin : (p.primesOver S).toFinset = {q} := by
    ext P
    simp only [Set.mem_toFinset, hprimes, Set.mem_singleton_iff, Finset.mem_singleton]
  have hmap : p.map (algebraMap R S) = q ^ Module.finrank K L := by
    rw [Ideal.map_algebraMap_eq_finsetProd_pow hp, hfin, Finset.prod_singleton, he]
  have hassoc : Associated (ξ ^ Module.finrank K L) (algebraMap R S u) := by
    apply Ideal.span_singleton_eq_span_singleton.mp
    rw [← Ideal.span_singleton_pow, ← hξ, ← hmap, (show p = Ideal.span {u} from hu),
      Ideal.map_span, Set.image_singleton]
  obtain ⟨a, ha⟩ := hassoc
  exact ⟨a, by simpa only [mul_comm] using ha.symm⟩

/-- Assemble the generic algebraic properties before inserting the geometric model. -/
private theorem normalization_package
    (R K L k : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R] [Field K] [Field L] [Field k] [IsAlgClosed k]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    (ε : R →+* k) (eR : IsLocalRing.ResidueField R ≃+* k)
    (heR : eR.toRingHom.comp (IsLocalRing.residue R) = ε)
    (G : Prop)
    (hG : ∀ [IsDiscreteValuationRing (integralClosure R L)]
      [IsStrictlyHenselianLocalRing (integralClosure R L)]
      (eS : IsLocalRing.ResidueField (integralClosure R L) ≃+* k),
      (∀ r : R,
        eS (IsLocalRing.residue (integralClosure R L)
          (algebraMap R (integralClosure R L) r)) = ε r) → G) :
    ∃ (_ : IsDiscreteValuationRing (integralClosure (R) L)),
      IsStrictlyHenselianLocalRing (integralClosure (R) L) ∧
      (∃ e : IsLocalRing.ResidueField
          (integralClosure (R) L) ≃+* k,
        ∀ r : R,
          e (IsLocalRing.residue _
              (algebraMap (R)
                (integralClosure (R) L) r)) =
            ε r) ∧
      IsFractionRing (integralClosure (R) L) L ∧
      Nonempty (Module.Basis (Fin (Module.finrank K L)) (R)
        (integralClosure (R) L)) ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        (algebraMap (R)
          (integralClosure (R) L)))) ∧
      Flat (Spec.map (CommRingCat.ofHom
        (algebraMap (R)
          (integralClosure (R) L)))) ∧
      (∀ u : R,
        IsLocalRing.maximalIdeal (R) = Ideal.span {u} →
        Etale (pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap (R)
            (integralClosure (R) L))))
          (Spec.map (CommRingCat.ofHom (algebraMap (R)
            (Localization.Away u)))))) ∧
      (∀ (u : R)
          (ξ : integralClosure (R) L),
        IsLocalRing.maximalIdeal (R) = Ideal.span {u} →
        IsLocalRing.maximalIdeal (integralClosure (R) L) =
          Ideal.span {ξ} →
        ∃ a : (integralClosure (R) L)ˣ,
          algebraMap (R)
              (integralClosure (R) L) u =
            (a : integralClosure (R) L) * ξ ^ Module.finrank K L) ∧
      G := by
  classical
  obtain ⟨hS, hSstrict, ⟨eS, heS⟩, hfrac, hbas, hfin, hflat⟩ :=
    normalization_algebra R K L k eR
  let := hS
  let := hSstrict
  have : IsAlgClosed (IsLocalRing.ResidueField R) := IsAlgClosed.of_ringEquiv k _ eR.symm
  have hε : ∀ r : R,
      eS (IsLocalRing.residue (integralClosure R L)
        (algebraMap R (integralClosure R L) r)) = ε r := by
    intro r
    rw [heS]
    exact DFunLike.congr_fun heR r
  refine ⟨hS, hSstrict, ⟨eS, hε⟩, hfrac, hbas, hfin, hflat,
    normalization_punctured_etale R K L, normalization_uniformizer R K L, ?_⟩
  exact @hG hS hSstrict eS hε

/-- Read a canonical scheme square as the native normalization ring equation. -/
private theorem native_compatibility_of_scheme_square
    (R : CommRingCat.{u}) (T : Type u) [CommRing T] [Algebra R T]
    (S : Subalgebra R T)
    {C₀ C₁ : Scheme.{u}} (g : C₁ ⟶ C₀)
    {k : Type u} [Field k] [IsAlgClosed k]
    (x₀ : Spec (.of k) ⟶ C₀) (x₁ : Spec (.of k) ⟶ C₁)
    (h₁ : x₁ ≫ g = x₀) (e₀ : strictHenselizationRing x₀ ≃+* R)
    (e₁ : strictHenselizationRing x₁ ≃+* CommRingCat.of S)
    (h : Spec.map (CommRingCat.ofHom e₁.toRingHom) ≫ strictHenselizationMap g x₁ =
      Spec.map (R := R) (S := CommRingCat.of S)
        (CommRingCat.ofHom (algebraMap R S)) ≫
      Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫
        eqToHom (congrArg strictHenselizationScheme h₁.symm)) :
    ∃ e' : strictHenselizationRing x₁ ≃+* S,
      ∀ z : strictHenselizationRing (x₁ ≫ g),
        e' ((Spec.preimage (strictHenselizationMap g x₁)).hom z) =
          algebraMap R S (e₀ ((eqToHom (congrArg strictHenselizationRing h₁)).hom z)) := by
  subst x₀
  simp only [eqToHom_refl, Category.comp_id] at h
  have heq : Spec.preimage (strictHenselizationMap g x₁) ≫
      CommRingCat.ofHom e₁.toRingHom =
        CommRingCat.ofHom e₀.toRingHom ≫ CommRingCat.ofHom (algebraMap R S) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    exact h
  refine ⟨{ toEquiv := e₁.toEquiv, map_mul' := e₁.map_mul, map_add' := e₁.map_add }, ?_⟩
  intro z
  have hz := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom heq) z
  cases R
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    eqToHom_refl, CommRingCat.hom_id, RingHom.id_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom] using hz

/-- Descend the finite separable extension and compare the actual strict local maps. -/
private theorem normalization_curve_chart_square
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (x : Spec (.of k) ⟶ C)
    [IsDomain (strictHenselizationRing x)]
    [IsDiscreteValuationRing (strictHenselizationRing x)]
    [IsStrictlyHenselianLocalRing (strictHenselizationRing x)]
    (K L : Type u) [Field K] [Field L]
    [Algebra (strictHenselizationRing x) K] [IsFractionRing (strictHenselizationRing x) K]
    [Algebra K L] [Algebra (strictHenselizationRing x) L]
    [IsScalarTower (strictHenselizationRing x) K L]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    [IsDiscreteValuationRing (integralClosure (strictHenselizationRing x) L)]
    [IsStrictlyHenselianLocalRing (integralClosure (strictHenselizationRing x) L)]
    (eR : IsLocalRing.ResidueField (strictHenselizationRing x) ≃+* k)
    (heR : eR.toRingHom.comp (IsLocalRing.residue (strictHenselizationRing x)) =
      strictHenselizationPointEvaluation x)
    (eS : IsLocalRing.ResidueField (integralClosure (strictHenselizationRing x) L) ≃+* k)
    (heS : ∀ r : strictHenselizationRing x,
      eS (IsLocalRing.residue (integralClosure (strictHenselizationRing x) L)
        (algebraMap (strictHenselizationRing x)
          (integralClosure (strictHenselizationRing x) L) r)) =
            strictHenselizationPointEvaluation x r) :
    ∃ (C₀ C₁ : Scheme.{u}) (p : C₀ ⟶ C) (g : C₁ ⟶ C₀)
        (x₀ : Spec (.of k) ⟶ C₀) (x₁ : Spec (.of k) ⟶ C₁),
      Etale p ∧ IsCurve (p ≫ f) ∧ Smooth (p ≫ f) ∧
      IsCurve (g ≫ p ≫ f) ∧ Smooth (g ≫ p ≫ f) ∧ IsFinite g ∧
      ∃ (h₁ : x₁ ≫ g = x₀) (h₀ : x₀ ≫ p = x)
        (e₀ : strictHenselizationRing x₀ ≃+* strictHenselizationRing x)
        (e₁ : strictHenselizationRing x₁ ≃+*
          CommRingCat.of (integralClosure (strictHenselizationRing x) L)),
        Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫ strictHenselizationMap p x₀ =
          eqToHom (congrArg strictHenselizationScheme h₀.symm) ∧
        Spec.map (CommRingCat.ofHom e₁.toRingHom) ≫ strictHenselizationMap g x₁ =
          Spec.map (R := strictHenselizationRing x)
            (S := CommRingCat.of (integralClosure (strictHenselizationRing x) L))
            (CommRingCat.ofHom (algebraMap (strictHenselizationRing x)
              (integralClosure (strictHenselizationRing x) L))) ≫
          Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫
            eqToHom (congrArg strictHenselizationScheme h₁.symm) := by
  classical
  let R := strictHenselizationRing x
  let S := integralClosure R L
  obtain ⟨A, hA, p, a, hp, hconn, hsm, hbase, hind, hchart⟩ :=
    field_extension_chart k C f x K L
  let := hA
  let := hp
  let := hconn
  let := hsm
  let : Algebra A R := a.hom.toAlgebra
  obtain ⟨F, E, hF, hE, algAF, hfracF, algFE, algAE, htower, hfinite, hsep, ⟨e⟩⟩ :=
    hchart
  let := hF
  let := hE
  let := algAF
  let := hfracF
  let := algFE
  let := algAE
  let := htower
  let := hfinite
  let := hsep
  let B := integralClosure A E
  let g : Spec (.of B) ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A B))
  obtain ⟨hg, hcurve, hsmB⟩ := affine_normalization_model k A (p ≫ f) F E
  let εR : R →+* k := strictHenselizationPointEvaluation x
  let εS : S →+* k := eS.toRingHom.comp (IsLocalRing.residue S)
  have : IsLocalHom εR := by
    change IsLocalHom (strictHenselizationPointEvaluation x)
    rw [← heR]
    infer_instance
  have : IsLocalHom εS := inferInstance
  have hε : εS.comp (algebraMap R S) = εR := by
    ext z
    exact heS z
  obtain ⟨h₀, e₀, he₀base, he₀point, he₀can⟩ :=
    initial_affine_strict_comparison x A p a (indEtale_across a.hom hind) hbase
  let x₀ : Spec (.of k) ⟶ Spec A := Spec.map (CommRingCat.ofHom εR) ≫ Spec.map a
  obtain ⟨b, hb, hab⟩ := integral_closure_chart_map A R E L a hind e
  obtain ⟨hbbase, hbpoint⟩ :=
    affine_chart_squares A (.of B) R (.of S)
      (CommRingCat.ofHom (algebraMap A B)) a b
      (CommRingCat.ofHom (algebraMap R S)) hab x₀ e₀ εR εS he₀base he₀point hε
  obtain ⟨h₁, e₁, _, _, he₁can⟩ :=
    affine_strict_comparison_scheme_square (Spec A) (.of B) R (.of S) g b (indEtale_across b.hom hb)
      εS x₀ e₀ (CommRingCat.ofHom (algebraMap R S)) hbbase hbpoint
  refine ⟨Spec A, Spec (.of B), p, g, x₀,
    Spec.map (CommRingCat.ofHom εS) ≫ Spec.map b,
    hp, inferInstance, hsm, hcurve, hsmB, hg, h₁, h₀, e₀, e₁, ?_, he₁can⟩
  exact canonical_comparison_spec p x₀ x h₀ e₀ he₀can

/-- Descend the finite separable extension and compare the actual strict local maps. -/
private theorem normalization_curve_descent
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (x : Spec (.of k) ⟶ C)
    [IsDomain (strictHenselizationRing x)]
    [IsDiscreteValuationRing (strictHenselizationRing x)]
    [IsStrictlyHenselianLocalRing (strictHenselizationRing x)]
    (K L : Type u) [Field K] [Field L]
    [Algebra (strictHenselizationRing x) K] [IsFractionRing (strictHenselizationRing x) K]
    [Algebra K L] [Algebra (strictHenselizationRing x) L]
    [IsScalarTower (strictHenselizationRing x) K L]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    [IsDiscreteValuationRing (integralClosure (strictHenselizationRing x) L)]
    [IsStrictlyHenselianLocalRing (integralClosure (strictHenselizationRing x) L)]
    (eR : IsLocalRing.ResidueField (strictHenselizationRing x) ≃+* k)
    (heR : eR.toRingHom.comp (IsLocalRing.residue (strictHenselizationRing x)) =
      strictHenselizationPointEvaluation x)
    (eS : IsLocalRing.ResidueField (integralClosure (strictHenselizationRing x) L) ≃+* k)
    (heS : ∀ r : strictHenselizationRing x,
      eS (IsLocalRing.residue (integralClosure (strictHenselizationRing x) L)
        (algebraMap (strictHenselizationRing x)
          (integralClosure (strictHenselizationRing x) L) r)) =
            strictHenselizationPointEvaluation x r) :
    ∃ (C₀ C₁ : Scheme.{u}) (p : C₀ ⟶ C) (g : C₁ ⟶ C₀)
        (x₀ : Spec (.of k) ⟶ C₀) (x₁ : Spec (.of k) ⟶ C₁),
      Etale p ∧ IsCurve (p ≫ f) ∧ Smooth (p ≫ f) ∧
      IsCurve (g ≫ p ≫ f) ∧ Smooth (g ≫ p ≫ f) ∧ IsFinite g ∧
      ∃ (h₁ : x₁ ≫ g = x₀) (h₀ : x₀ ≫ p = x)
        (e₀ : strictHenselizationRing x₀ ≃+* strictHenselizationRing x)
        (e₁ : strictHenselizationRing x₁ ≃+*
          integralClosure (strictHenselizationRing x) L),
        Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫ strictHenselizationMap p x₀ =
          eqToHom (congrArg strictHenselizationScheme h₀.symm) ∧
        ∀ r : strictHenselizationRing (x₁ ≫ g),
          e₁ ((Spec.preimage (strictHenselizationMap g x₁)).hom r) =
            algebraMap (strictHenselizationRing x)
              (integralClosure (strictHenselizationRing x) L)
              (e₀ ((eqToHom (congrArg strictHenselizationRing h₁)).hom r)) := by
  obtain ⟨C₀, C₁, p, g, x₀, x₁, hp, hc₀, hsm₀, hc₁, hsm₁, hg,
    h₁, h₀, e₀, e₁, he₀, he₁⟩ := normalization_curve_chart_square k C f x K L eR heR eS heS
  obtain ⟨e₁', he₁'⟩ := native_compatibility_of_scheme_square
    (strictHenselizationRing x) L (integralClosure (strictHenselizationRing x) L)
    g x₀ x₁ h₁ e₀ e₁ he₁
  exact ⟨C₀, C₁, p, g, x₀, x₁, hp, hc₀, hsm₀, hc₁, hsm₁, hg,
    h₁, h₀, e₀, e₁', he₀, he₁'⟩

private theorem strict_trait_base
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (x : Spec (.of k) ⟶ C) (hx : x ≫ f = 𝟙 _) :
    ∃ (_ : IsDomain (strictHenselizationRing x))
      (_ : IsDiscreteValuationRing (strictHenselizationRing x)),
      IsStrictlyHenselianLocalRing (strictHenselizationRing x) ∧
      (∃ e : IsLocalRing.ResidueField (strictHenselizationRing x) ≃+* k,
        e.toRingHom.comp (IsLocalRing.residue (strictHenselizationRing x)) =
          strictHenselizationPointEvaluation x) ∧
      (∃ ι : C.presheaf.stalk (x (IsLocalRing.closedPoint k)) →+*
          strictHenselizationRing x,
        Spec.map (CommRingCat.ofHom ι) ≫
            C.fromSpecStalk (x (IsLocalRing.closedPoint k)) =
          strictHenselizationStructuralMap x ∧
        ∀ t : C.presheaf.stalk (x (IsLocalRing.closedPoint k)),
          IsLocalRing.maximalIdeal _ = Ideal.span {t} →
          IsLocalRing.maximalIdeal (strictHenselizationRing x) = Ideal.span {ι t}) := by
  classical
  let z := x (IsLocalRing.closedPoint k)
  let A := C.presheaf.stalk z
  let R := strictHenselizationRing x
  obtain ⟨hC, hnoeth, _, _, _, _, _, _, _, hlocal⟩ :=
    smooth_connected_curve_local_rings k C f
  let := hC
  have : IsNoetherian C := hnoeth
  have : IsClosedImmersion x := isClosedImmersion_of_comp_eq_id f x hx
  have hz : z ∈ closedPoints C := by
    change IsClosed ({z} : Set C)
    have he : x '' ({IsLocalRing.closedPoint k} : Set (Spec (.of k))) = {z} := by
      ext y
      simp [z]
    rw [← he]
    exact x.isClosedMap _ isClosed_singleton
  have : IsDiscreteValuationRing A := (hlocal z hz).1
  let : Algebra (IsLocalRing.ResidueField A) k :=
    (descResidueField (stalkClosedPointTo x)).hom.toAlgebra
  have hΩ : algebraMap (IsLocalRing.ResidueField A) k =
      (descResidueField (stalkClosedPointTo x)).hom := rfl
  let F := separableClosure (IsLocalRing.ResidueField A) k
  let : Algebra A F := Algebra.compHom F (IsLocalRing.residue A)
  have : IsScalarTower A (IsLocalRing.ResidueField A) F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨H, hH, aH, P, locH, θ, hθ, _⟩ :=
    geometricStrictLocal_stalk_presentation x hΩ
  let := hH
  let := aH
  let := locH
  have hsh : Algebra.IsStrictHenselization A F H :=
    ⟨P.cocone, ⟨P.isColimit⟩, ⟨P.identification⟩⟩
  have : IsRegularLocalRing H :=
    (Algebra.isRegularLocalRing_iff_strictHenselization A F H hsh).mp inferInstance
  have hdim : ringKrullDim H = 1 :=
    (Algebra.ringKrullDim_eq_of_isStrictHenselization A F H hsh).symm.trans
      (IsDiscreteValuationRing.ringKrullDim_eq_one A)
  have : IsDiscreteValuationRing H := IsRegularLocalRing.isDiscreteValuationRing H hdim
  have : IsDomain R := θ.toMulEquiv.isDomain H
  have : IsDiscreteValuationRing R :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing θ.symm
  obtain ⟨_, hstrict⟩ := AlgebraicGeometry.strictHenselizationLocalStructure x
  let ε : R →+* k := strictHenselizationPointEvaluation x
  let a : k →+* R := (Spec.preimage (strictHenselizationStructuralMap x ≫ f)).hom
  have hεa : ε.comp a = RingHom.id k := by
    have heq : CommRingCat.ofHom (ε.comp a) = 𝟙 (CommRingCat.of k) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom a ≫ CommRingCat.ofHom ε) = Spec.map (𝟙 _)
      rw [Spec.map_comp, Spec.map_id]
      change Spec.map (CommRingCat.ofHom ε) ≫
        Spec.map (Spec.preimage (strictHenselizationStructuralMap x ≫ f)) = _
      rw [Spec.map_preimage, ← Category.assoc, strictHenselizationClosedLift_over, hx]
    exact congrArg CommRingCat.Hom.hom heq
  have hsurj : Function.Surjective ε := fun t ↦ ⟨a t, DFunLike.congr_fun hεa t⟩
  have hker : RingHom.ker ε = IsLocalRing.maximalIdeal R :=
    IsLocalRing.ker_eq_maximalIdeal ε hsurj
  let er : IsLocalRing.ResidueField R →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) ε (by
      intro r hr
      exact (show r ∈ RingHom.ker ε from hker.symm ▸ hr))
  let e : IsLocalRing.ResidueField R ≃+* k :=
    RingEquiv.ofBijective er ⟨er.injective, fun b ↦ by
      obtain ⟨r, hr⟩ := hsurj b
      exact ⟨IsLocalRing.residue R r, hr⟩⟩
  have he : e.toRingHom.comp (IsLocalRing.residue R) = ε := by
    ext r
    rfl
  obtain ⟨_, hmH⟩ := Algebra.strictHenselization_local_maximalIdeal A F H hsh
  let ι : A →+* R := θ.symm.toRingHom.comp (algebraMap A H)
  refine ⟨inferInstance, inferInstance, hstrict, ⟨e, he⟩, ι, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom ι) ≫ C.fromSpecStalk z = _
    calc
      _ = Spec.map (CommRingCat.ofHom θ.symm.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap A H)) ≫ C.fromSpecStalk z) := by
        rw [← Category.assoc, ← Spec.map_comp]
        rfl
      _ = Spec.map (CommRingCat.ofHom θ.symm.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
            strictHenselizationStructuralMap x) := by rw [hθ]
      _ = strictHenselizationStructuralMap x := by
        rw [← Category.assoc, ← Spec.map_comp]
        have h : CommRingCat.ofHom θ.toRingHom ≫ CommRingCat.ofHom θ.symm.toRingHom =
            𝟙 R := by
          ext r
          exact θ.symm_apply_apply r
        have hid := congrArg
          (fun m : R ⟶ R ↦ Spec.map m ≫ strictHenselizationStructuralMap x) h
        exact hid.trans (by rw [Spec.map_id, Category.id_comp])
  · intro t ht
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal θ.symm, hmH, ht,
      Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    rfl

/-- The strict local ring of a smooth connected curve at a rational point is a DVR;
its finite separable normalizations are strictly henselian DVRs, totally ramified of
the field degree, and descend to finite maps of smooth curves.

Source: Stacks Project, Algebra, Tags 032L (`lemma-Noetherian-normal-domain-finite-separable-
extension`), 04GH (`lemma-finite-over-henselian`) and 05WR
(`lemma-quasi-finite-strict-henselization`); Varieties, Tag 0B8Y
(`lemma-regular-point-on-curve`); blueprint `det-tf-restriction-zero-covers`, proof (i)--(ii).
(blueprint: lem-trf-separable-strict-trait-normalization).

Proof:
1. The ordinary stalk is a DVR. Its strict henselization is a flat local extension
   with maximal ideal generated by the original maximal ideal; thus every ordinary
   uniformizer remains a uniformizer. The geometric stalk presentation identifies
   this ring with the chosen pointed-neighbourhood colimit. Strict henselianity and
   its residue description identify the residue field with the algebraically closed k.
2. By 032L the integral closure is finite. It is a normal one-dimensional domain
   with fraction field L. The finite-over-henselian product decomposition has just
   one nonzero factor, so it is henselian local. Its finite residue extension of k
   is k. Normality and dimension one make it a DVR, hence strictly henselian.
3. The integral-closure freeness and rank theorem over the PID R gives a basis of
   cardinality [L:K]. Thus its spectrum is finite flat of that rank.
4. On the punctured trait the map is the finite separable field extension, hence
   etale. The local ramification identity is e*f = [L:K]; both residue fields are k,
   so f = 1. Comparing generators of the extended maximal ideal gives u = a*xi^d.
5. Descend a primitive-element polynomial, including its finitely many numerator
   and denominator coefficients, to an affine pointed etale curve neighbourhood.
   Irreducibility and separability descend because its function field embeds in K.
6. Normalize that smooth affine curve in the descended finite function-field
   extension. Its normalization is finite and smooth over the perfect field k.
   Integral closure commutes with the ind-etale strict-local base change (0CBF),
   identifying its base change with S. The inverse image of the maximal ideal of S
   gives the required rational point of the normalization.
7. Apply 05WR at that point. The pointed localization of the base change is S,
   since elements outside the chosen maximal ideal already map to units. The
   geometric stalk presentation identifies this comparison with the canonical map
   of strict local rings, giving the displayed commuting square.

The existential class binders assert the ring properties before the extension is
quantified. The basis uses Fin of the field degree. Localization at any uniformizer
is exactly the punctured trait. The first descent equivalence is pinned to the
canonical map for the pointed etale neighbourhood, and the second intertwines the
canonical strict-local map with the actual integral-closure inclusion. -/
theorem separable_strict_trait_normalization
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (x : Spec (.of k) ⟶ C) (hx : x ≫ f = 𝟙 _) :
    ∃ (_ : IsDomain (strictHenselizationRing x))
      (_ : IsDiscreteValuationRing (strictHenselizationRing x)),
      IsStrictlyHenselianLocalRing (strictHenselizationRing x) ∧
      (∃ e : IsLocalRing.ResidueField (strictHenselizationRing x) ≃+* k,
        e.toRingHom.comp (IsLocalRing.residue (strictHenselizationRing x)) =
          strictHenselizationPointEvaluation x) ∧
      (∃ ι : C.presheaf.stalk (x (IsLocalRing.closedPoint k)) →+*
          strictHenselizationRing x,
        Spec.map (CommRingCat.ofHom ι) ≫
            C.fromSpecStalk (x (IsLocalRing.closedPoint k)) =
          strictHenselizationStructuralMap x ∧
        ∀ t : C.presheaf.stalk (x (IsLocalRing.closedPoint k)),
          IsLocalRing.maximalIdeal _ = Ideal.span {t} →
          IsLocalRing.maximalIdeal (strictHenselizationRing x) = Ideal.span {ι t}) ∧
      ∀ (K L : Type u) [Field K] [Field L]
        [Algebra (strictHenselizationRing x) K]
        [IsFractionRing (strictHenselizationRing x) K] [Algebra K L]
        [Algebra (strictHenselizationRing x) L]
        [IsScalarTower (strictHenselizationRing x) K L]
        [Module.Finite K L] [Algebra.IsSeparable K L],
        ∃ (_ : IsDiscreteValuationRing (integralClosure (strictHenselizationRing x) L)),
          IsStrictlyHenselianLocalRing (integralClosure (strictHenselizationRing x) L) ∧
          (∃ e : IsLocalRing.ResidueField
              (integralClosure (strictHenselizationRing x) L) ≃+* k,
            ∀ r : strictHenselizationRing x,
              e (IsLocalRing.residue _
                  (algebraMap (strictHenselizationRing x)
                    (integralClosure (strictHenselizationRing x) L) r)) =
                strictHenselizationPointEvaluation x r) ∧
          IsFractionRing (integralClosure (strictHenselizationRing x) L) L ∧
          Nonempty (Module.Basis (Fin (Module.finrank K L)) (strictHenselizationRing x)
            (integralClosure (strictHenselizationRing x) L)) ∧
          IsFinite (Spec.map (CommRingCat.ofHom
            (algebraMap (strictHenselizationRing x)
              (integralClosure (strictHenselizationRing x) L)))) ∧
          Flat (Spec.map (CommRingCat.ofHom
            (algebraMap (strictHenselizationRing x)
              (integralClosure (strictHenselizationRing x) L)))) ∧
          (∀ u : strictHenselizationRing x,
            IsLocalRing.maximalIdeal (strictHenselizationRing x) = Ideal.span {u} →
            Etale (pullback.snd
              (Spec.map (CommRingCat.ofHom (algebraMap (strictHenselizationRing x)
                (integralClosure (strictHenselizationRing x) L))))
              (Spec.map (CommRingCat.ofHom (algebraMap (strictHenselizationRing x)
                (Localization.Away u)))))) ∧
          (∀ (u : strictHenselizationRing x)
              (ξ : integralClosure (strictHenselizationRing x) L),
            IsLocalRing.maximalIdeal (strictHenselizationRing x) = Ideal.span {u} →
            IsLocalRing.maximalIdeal (integralClosure (strictHenselizationRing x) L) =
              Ideal.span {ξ} →
            ∃ a : (integralClosure (strictHenselizationRing x) L)ˣ,
              algebraMap (strictHenselizationRing x)
                  (integralClosure (strictHenselizationRing x) L) u =
                (a : integralClosure (strictHenselizationRing x) L) * ξ ^ Module.finrank K L) ∧
          ∃ (C₀ C₁ : Scheme.{u}) (p : C₀ ⟶ C) (g : C₁ ⟶ C₀)
              (x₀ : Spec (.of k) ⟶ C₀) (x₁ : Spec (.of k) ⟶ C₁),
            Etale p ∧ IsCurve (p ≫ f) ∧ Smooth (p ≫ f) ∧
            IsCurve (g ≫ p ≫ f) ∧ Smooth (g ≫ p ≫ f) ∧ IsFinite g ∧
            ∃ (h₁ : x₁ ≫ g = x₀) (h₀ : x₀ ≫ p = x)
              (e₀ : strictHenselizationRing x₀ ≃+* strictHenselizationRing x)
              (e₁ : strictHenselizationRing x₁ ≃+*
                integralClosure (strictHenselizationRing x) L),
              Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫ strictHenselizationMap p x₀ =
                eqToHom (congrArg strictHenselizationScheme h₀.symm) ∧
              ∀ r : strictHenselizationRing (x₁ ≫ g),
                e₁ ((Spec.preimage (strictHenselizationMap g x₁)).hom r) =
                  algebraMap (strictHenselizationRing x)
                    (integralClosure (strictHenselizationRing x) L)
                    (e₀ ((eqToHom (congrArg strictHenselizationRing h₁)).hom r)) := by
  classical
  obtain ⟨hR, hDVR, hstrict, ⟨eR, heR⟩, hstalk⟩ := strict_trait_base k C f x hx
  let := hR
  let := hDVR
  let := hstrict
  refine ⟨hR, hDVR, hstrict, ⟨eR, heR⟩, hstalk, ?_⟩
  intro K L _ _ _ _ _ _ _ _ _
  apply normalization_package (strictHenselizationRing x) K L k
    (strictHenselizationPointEvaluation x) eR heR _
  intro hS hSstrict eS heS
  exact normalization_curve_descent k C f x K L eR heR eS heS

end AlgebraicGeometry.Scheme
