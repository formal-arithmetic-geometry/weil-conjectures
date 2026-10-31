/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.AffineCoordinateStrictLocalData
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import WeilConjectures.AlgebraicGeometry.AffineCoordinateStrictLocalFibreComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedLift
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.RingTheory.StrictHenselizationTriples

/-! # Affine coordinate sections and their strict-local polynomial models

Source: Stacks Project, Tags 05WS, 04HX, 04GU, 00T7 and 01JB
(blueprint: lem-trf-affine-coordinate-strict-local-model).
The result structure spells out the coordinate-zero immersion, its strict-local quotient,
and the two pointed polynomial presentations, including the quotient comparison map.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.AffineCoordinateStrictLocal

/-- All the geometric, algebraic and functorial clauses of the coordinate comparison.
Source: Stacks 05WS and 04HX, with 04GU for the uniquely pointed comparison map
(blueprint: lem-trf-affine-coordinate-strict-local-model).
The rings H0 and H1 are supplied together with the recorded universal pointed-etale
presentations, not merely assumed to be strictly henselian. The equations fix the base,
coordinates and residue embeddings; uniqueness fixes the induced strict-local map. -/
structure Model {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
    [IsLocalRing (Base r e v)] (K : Set (Index.{u} r)) where
  /-- The complementary affine space is the scheme-theoretic coordinate-zero subspace. -/
  closed : IsClosedImmersion (inclusion r e K)
  /-- Its projection to S is smooth. -/
  smooth : Smooth (AffineSpace {i : Index.{u} r // i ∉ K} S ↘ S)
  /-- The universal coordinate-zero condition, including arbitrary nonreduced test schemes. -/
  zeroLocus : ∀ (T : Scheme.{u}) (h : T ⟶ V),
    (∀ i ∈ K, h.appTop (e.hom.appTop (AffineSpace.coord S i)) = 0) ↔
      ∃! k : T ⟶ AffineSpace {i : Index.{u} r // i ∉ K} S, k ≫ inclusion r e K = h
  /-- Factorization of the original geometric point. -/
  point : Spec (.of Ω) ⟶ AffineSpace {i : Index.{u} r // i ∉ K} S
  point_eq : v = point ≫ inclusion r e K
  /-- The canonical strict-local quotient of the coordinate subspace. -/
  quotientIso : strictHenselizationRing point ≃+*
    (strictHenselizationRing v ⧸ coordinateIdeal r e v K)
  quotientIso_map : quotientIso.toRingHom.comp
    (ringMap (inclusion r e K) point v point_eq) =
      Ideal.Quotient.mk (coordinateIdeal r e v K)
  /-- The closed-fibre polynomial models, instantiated with the specified rings and maps. -/
  fibres : FibreModels (Base r e v) (strictHenselizationRing v) (PolynomialRing r e v)
    (Index.{u} r) K (fibreIdeal r e v) (coordinateIdeal r e v K) (polynomialIdeal r e v K)
    (baseMap r e v)
    ((MvPolynomial.C).comp (IsLocalRing.residue (Base r e v)))
    (coordinate r e v) MvPolynomial.X
    (strictHenselizationPointEvaluation (v ≫ projection r e))
    (strictHenselizationPointEvaluation v)

private theorem inclusion_over {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S) (K : Set (Index.{u} r)) :
    inclusion r e K ≫ projection r e =
      AffineSpace {i : Index.{u} r // i ∉ K} S ↘ S := by
  classical
  simp [inclusion, projection]

private theorem inclusion_coord {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S) (K : Set (Index.{u} r)) [DecidablePred (· ∈ K)]
    (i : Index.{u} r) :
    (inclusion r e K).appTop (e.hom.appTop (AffineSpace.coord S i)) =
      if h : i ∈ K then 0 else AffineSpace.coord S ⟨i, h⟩ := by
  classical
  change (inclusion r e K ≫ e.hom).appTop (AffineSpace.coord S i) = _
  simp only [inclusion, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    AffineSpace.homOfVector_appTop_coord]
  split_ifs <;> rfl

private theorem inclusion_zeroLocus {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S) (K : Set (Index.{u} r))
    (T : Scheme.{u}) (h : T ⟶ V) :
    (∀ i ∈ K, h.appTop (e.hom.appTop (AffineSpace.coord S i)) = 0) ↔
      ∃! k : T ⟶ AffineSpace {i : Index.{u} r // i ∉ K} S,
        k ≫ inclusion r e K = h := by
  classical
  constructor
  · intro hz
    let k := AffineSpace.homOfVector (h ≫ projection r e)
      (fun i : {i : Index.{u} r // i ∉ K} ↦
        h.appTop (e.hom.appTop (AffineSpace.coord S i.1)))
    have hk : k ≫ inclusion r e K = h := by
      apply (cancel_mono e.hom).1
      apply AffineSpace.hom_ext
      · change (k ≫ inclusion r e K) ≫ projection r e = h ≫ projection r e
        rw [Category.assoc, inclusion_over]
        exact AffineSpace.homOfVector_over _ _
      · intro i
        change k.appTop ((inclusion r e K).appTop
          (e.hom.appTop (AffineSpace.coord S i))) =
            h.appTop (e.hom.appTop (AffineSpace.coord S i))
        rw [inclusion_coord]
        split_ifs with hi
        · simp [hz i hi]
        · exact AffineSpace.homOfVector_appTop_coord _ _ _
    refine ⟨k, hk, ?_⟩
    intro l hl
    apply AffineSpace.hom_ext
    · rw [← inclusion_over r e K, ← Category.assoc, hl, ← hk, Category.assoc]
    · intro i
      have hh := congrArg (fun f : T ⟶ V ↦
        f.appTop (e.hom.appTop (AffineSpace.coord S i.1))) (hl.trans hk.symm)
      change l.appTop ((inclusion r e K).appTop
        (e.hom.appTop (AffineSpace.coord S i.1))) =
          k.appTop ((inclusion r e K).appTop
            (e.hom.appTop (AffineSpace.coord S i.1))) at hh
      simpa only [inclusion_coord, dif_neg i.2] using hh
  · rintro ⟨k, hk, _⟩ i hi
    rw [← hk]
    change k.appTop ((inclusion r e K).appTop
      (e.hom.appTop (AffineSpace.coord S i))) = 0
    rw [inclusion_coord, dif_pos hi, map_zero]

private theorem inclusion_closed {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S) (K : Set (Index.{u} r)) :
    IsClosedImmersion (inclusion r e K) := by
  classical
  let p := e.hom ≫ AffineSpace.reindex
    (Subtype.val : {i : Index.{u} r // i ∉ K} → Index.{u} r) S
  have hp : p ≫ AffineSpace {i : Index.{u} r // i ∉ K} S ↘ S = projection r e := by
    simp [p, projection]
  have : IsSeparated (projection r e) := by
    unfold projection
    infer_instance
  have : IsSeparated (p ≫ AffineSpace {i : Index.{u} r // i ∉ K} S ↘ S) := by
    rw [hp]
    infer_instance
  have : IsSeparated p := IsSeparated.of_comp p
    (AffineSpace {i : Index.{u} r // i ∉ K} S ↘ S)
  have hsec : inclusion r e K ≫ p = 𝟙 _ := by
    apply AffineSpace.hom_ext
    · simp [Category.assoc, hp, inclusion_over]
    · intro i
      change (inclusion r e K).appTop
        (e.hom.appTop ((AffineSpace.reindex Subtype.val S).appTop
          (AffineSpace.coord S i))) = AffineSpace.coord S i
      simp only [AffineSpace.reindex_appTop_coord, inclusion_coord, dif_neg i.2]
  have : IsClosedImmersion (inclusion r e K ≫ p) := by rw [hsec]; infer_instance
  exact IsClosedImmersion.of_comp (inclusion r e K) p

private theorem spec_section {R D : CommRingCat.{u}} (f : R →+* D)
    {X : Scheme.{u}} (g : Spec R ⟶ X) (s : Γ(X, ⊤)) :
    (ΓSpecIso D).hom ((Spec.map (CommRingCat.ofHom f) ≫ g).appTop s) =
      f ((ΓSpecIso R).hom (g.appTop s)) := by
  change ((Spec.map (CommRingCat.ofHom f)).appTop ≫ (ΓSpecIso D).hom)
    (g.appTop s) = _
  rw [ΓSpecIso_naturality]
  rfl

private theorem coordinate_quotient {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S) (K : Set (Index.{u} r))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (a : Spec (.of Ω) ⟶ AffineSpace {i : Index.{u} r // i ∉ K} S) :
    ∃ θ : strictHenselizationRing a ≃+*
        (strictHenselizationRing (a ≫ inclusion r e K) ⧸
          coordinateIdeal r e (a ≫ inclusion r e K) K),
      θ.toRingHom.comp
        (ringMap (inclusion r e K) a (a ≫ inclusion r e K) rfl) =
          Ideal.Quotient.mk (coordinateIdeal r e (a ≫ inclusion r e K) K) := by
  classical
  let i := inclusion r e K
  let B := strictHenselizationRing (a ≫ i)
  let C := strictHenselizationRing a
  let J := coordinateIdeal r e (a ≫ i) K
  let F := (Spec.preimage (strictHenselizationMap i a)).hom
  have hF : Spec.map (CommRingCat.ofHom F) = strictHenselizationMap i a :=
    Spec.map_preimage _
  let g : Spec B ⟶ V := strictHenselizationStructuralMap (a ≫ i)
  have over := strictHenselizationMap_over i a
  have hFg : Spec.map (CommRingCat.ofHom F) ≫ g =
      strictHenselizationStructuralMap a ≫ i := by rw [hF]; exact over
  have hkill : J ≤ RingHom.ker F := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change F (coordinate r e (a ≫ i) j) = 0
    change F ((ΓSpecIso B).hom (g.appTop
      (e.hom.appTop (AffineSpace.coord S j)))) = 0
    rw [← spec_section F g, hFg]
    change (ΓSpecIso C).hom ((strictHenselizationStructuralMap a).appTop
      (i.appTop (e.hom.appTop (AffineSpace.coord S j)))) = 0
    rw [inclusion_coord, dif_pos hj, map_zero, map_zero]
  let q := Ideal.Quotient.mk J
  let f : (B ⧸ J) →+* C := Ideal.Quotient.lift J F (fun x hx ↦ hkill hx)
  have hf : f.comp q = F := Ideal.Quotient.lift_comp_mk _ _ _
  let d := Spec.map (CommRingCat.ofHom f)
  let b := Spec.map (CommRingCat.ofHom q)
  have hdb : d ≫ b = strictHenselizationMap i a := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
    exact hF
  have hbzero : ∀ j ∈ K,
      (b ≫ strictHenselizationStructuralMap (a ≫ i)).appTop
        (e.hom.appTop (AffineSpace.coord S j)) = 0 := by
    intro j hj
    apply (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of (B ⧸ J))).hom).1
    rw [map_zero]
    change (ΓSpecIso (.of (B ⧸ J))).hom
      ((Spec.map (CommRingCat.ofHom q) ≫
        strictHenselizationStructuralMap (a ≫ i)).appTop
        (e.hom.appTop (AffineSpace.coord S j))) = 0
    rw [spec_section]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, hj, rfl⟩)
  obtain ⟨k, hk, _⟩ := (inclusion_zeroLocus r e K _ _).mp hbzero
  have : IsClosedImmersion i := inclusion_closed r e K
  let c := pullback.lift (f := i) (g := strictHenselizationStructuralMap (a ≫ i))
    (strictHenselizationStructuralMap a) (strictHenselizationMap i a) over.symm
  have : IsIso c := isIso_strictHenselizationClosedImmersionCartesian i a
  let z : Spec (.of (B ⧸ J)) ⟶ Spec C :=
    pullback.lift k b hk ≫ inv c
  have hzb : z ≫ strictHenselizationMap i a = b := by
    change (pullback.lift k b hk ≫ inv c) ≫ strictHenselizationMap i a = b
    have hc : c ≫ pullback.snd i (strictHenselizationStructuralMap (a ≫ i)) =
        strictHenselizationMap i a := pullback.lift_snd _ _ _
    rw [← hc]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    exact pullback.lift_snd k b hk
  have hmono : Mono (strictHenselizationMap i a) := by
    have hc : c ≫ pullback.snd i (strictHenselizationStructuralMap (a ≫ i)) =
        strictHenselizationMap i a := pullback.lift_snd _ _ _
    rw [← hc]
    infer_instance
  have hdz : d ≫ z = 𝟙 _ := by
    apply (cancel_mono (strictHenselizationMap i a)).1
    simp only [Category.assoc, hzb, hdb, Category.id_comp]
  have hzd : z ≫ d = 𝟙 _ := by
    apply (cancel_mono b).1
    simp only [Category.assoc, hdb, hzb, Category.id_comp]
  let E : Spec C ≅ Spec (.of (B ⧸ J)) := ⟨d, z, hdz, hzd⟩
  let E' : C ≅ CommRingCat.of (B ⧸ J) :=
    (Spec.fullyFaithful.preimageIso (X := Opposite.op C)
      (Y := Opposite.op (.of (B ⧸ J))) E).unop.symm
  have hE' : E'.hom = Spec.preimage z := by
    apply Spec.map_injective
    rw [Spec.map_preimage]
    exact Spec.fullyFaithful.map_preimage
      (X := Opposite.op (.of (B ⧸ J))) (Y := Opposite.op C) E.inv
  refine ⟨E'.commRingCatIsoToRingEquiv, ?_⟩
  change E'.hom.hom.comp (ringMap (inclusion r e K) a (a ≫ inclusion r e K) rfl) = _
  rw [hE']
  simp only [ringMap, eqToHom_refl, Category.comp_id]
  change (Spec.preimage z).hom.comp F = q
  have hh : z ≫ Spec.map (CommRingCat.ofHom F) = Spec.map (CommRingCat.ofHom q) := by
    rw [hF]
    exact hzb
  have hh' := congrArg (fun h ↦ (Spec.preimage h).hom) hh
  simpa only [Spec.preimage_comp, CommRingCat.hom_comp, Spec.preimage_map,
    CommRingCat.hom_ofHom] using hh'

private theorem evaluation_kernel {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    [IsLocalRing (strictHenselizationRing x)] :
    RingHom.ker (strictHenselizationPointEvaluation x) =
      IsLocalRing.maximalIdeal (strictHenselizationRing x) := by
  let : Algebra (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω :=
    (descResidueField (stalkClosedPointTo x)).hom.toAlgebra
  have hΩ : algebraMap (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω =
      (descResidueField (stalkClosedPointTo x)).hom := RingHom.algebraMap_toAlgebra _
  have hk := IsLocalRing.ker_eq_maximalIdeal
    (strictHenselizationPointEvaluationToSep x hΩ)
    (strictHenselizationPointEvaluationToSep_surjective x hΩ)
  have he : RingHom.ker (strictHenselizationPointEvaluation x) =
      RingHom.ker (strictHenselizationPointEvaluationToSep x hΩ) := by
    ext b
    change strictHenselizationPointEvaluation x b = 0 ↔
      strictHenselizationPointEvaluationToSep x hΩ b = 0
    change strictHenselizationPointEvaluation x b = 0 ↔
      (⟨strictHenselizationPointEvaluation x b, _⟩ :
        separableClosure (X.residueField (x (IsLocalRing.closedPoint Ω))) Ω) = 0
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  exact he.trans hk

private theorem coordinate_evaluation {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
    (i : Index.{u} r) :
    strictHenselizationPointEvaluation v (coordinate r e v i) =
      (ΓSpecIso (.of Ω)).hom (v.appTop (e.hom.appTop (AffineSpace.coord S i))) := by
  let g : Spec (strictHenselizationRing v) ⟶ V := strictHenselizationStructuralMap v
  change strictHenselizationPointEvaluation v
    ((ΓSpecIso (strictHenselizationRing v)).hom
      (g.appTop (e.hom.appTop (AffineSpace.coord S i)))) = _
  exact (spec_section (R := strictHenselizationRing v) (D := .of Ω)
    (strictHenselizationPointEvaluation v) g
    (e.hom.appTop (AffineSpace.coord S i))).symm.trans (by
      rw [show Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation v)) ≫ g = v
        from strictHenselizationClosedLift_over v])

/-- Affine coordinate sections have the coordinate-zero strict-local quotient and the
compatible polynomial models specified by `Model`.
Source: Stacks Project, Tags 05WS, 04HX, 04GU, 00T7 and 01JB
(blueprint: lem-trf-affine-coordinate-strict-local-model).

Proof: Zero insertion is defined by its coordinate vector (AffineSpace.homOfVector).
By the affine-space universal property (homOfVector, hom_ext), a morphism T to V whose
selected coordinate sections vanish factors uniquely through it, for every test scheme
T. Forgetting the selected coordinates is a retraction of zero insertion, separated
because its composite with the complementary projection is the separated affine-space
projection; so zero insertion is a closed immersion (IsClosedImmersion.of_comp). Finite
affine space is smooth (sbc-lem-affine-space-smooth), including dimension zero.
The geometric evaluation on B has kernel m_B (its corestriction to the separable residue
closure is surjective, lem-weil-pbc-strict-henselization-point-evaluation-properties),
so the selected coordinates evaluate to zero; by the closed-lift equation and
naturality of GammaSpecIso their sections vanish at v, and v factors as a followed by
zero insertion. The canonical map F from B to the strict local ring C at a kills J, so
descends to B/J to C. Conversely Spec(B/J) maps to the complementary affine space by
the universal property, hence into the pullback of zero insertion along Spec B, which
lem-trf-closed-immersion-strict-localization-cartesian identifies with Spec C. The two
maps are inverse by cancellation of monomorphisms; full faithfulness of Spec gives the
ring isomorphism and its equation with the canonical map. The polynomial closed-fibre
models are lem-trf-affine-coordinate-strict-local-fibre-comparison. -/
theorem exists_model {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
    [IsLocalRing (Base r e v)] [IsLocalRing (strictHenselizationRing v)]
    (K : Set (Index.{u} r))
    (hK : ∀ i ∈ K, coordinate r e v i ∈ IsLocalRing.maximalIdeal (strictHenselizationRing v)) :
    Nonempty (Model r e v K) := by
  classical
  let : Finite (Index.{u} r) := by unfold Index; infer_instance
  have hzero (i : Index.{u} r) (hi : i ∈ K) :
      strictHenselizationPointEvaluation v (coordinate r e v i) = 0 := by
    have hh : coordinate r e v i ∈ RingHom.ker (strictHenselizationPointEvaluation v) := by
      rw [evaluation_kernel]
      exact hK i hi
    exact hh
  have hvzero : ∀ i ∈ K, v.appTop (e.hom.appTop (AffineSpace.coord S i)) = 0 := by
    intro i hi
    apply (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of Ω)).hom).1
    rw [map_zero, ← coordinate_evaluation]
    exact hzero i hi
  obtain ⟨a, ha, _⟩ := (inclusion_zeroLocus r e K _ v).mp hvzero
  have hv : v = a ≫ inclusion r e K := ha.symm
  subst v
  obtain ⟨θ, hθ⟩ := coordinate_quotient r e K a
  obtain ⟨F⟩ := exists_fibre_models r e (a ≫ inclusion r e K) K hzero
  exact ⟨{
    closed := inclusion_closed r e K
    smooth := SmoothOfRelativeDimension.smooth
      (Nat.card {i : Index.{u} r // i ∉ K}) _
    zeroLocus := inclusion_zeroLocus r e K
    point := a
    point_eq := rfl
    quotientIso := θ
    quotientIso_map := hθ
    fibres := F }⟩

end AlgebraicGeometry.Scheme.AffineCoordinateStrictLocal
