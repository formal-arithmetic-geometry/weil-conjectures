/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionProjection

/-! # The old coordinate support in the successor affine tower

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered coordinate product.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

/-- The first r coordinate factors inside the tower of rank r+1.
Source: ordered coordinate product
(blueprint: lem-pur-coordinate-successor-support-geometry). -/
abbrev successorTailList (r : ℕ) : List (Fin (r + 1)) :=
  (List.finRange r).map Fin.succ

/-- The literal intersection supporting the old coordinate factors.
Source: ordered coordinate product
(blueprint: lem-pur-coordinate-successor-support-geometry). -/
abbrev successorTail (B : Scheme.{u}) (r : ℕ) := support B (r + 1) (successorTailList r)

/-- Its closed immersion into the successor tower.
Source: ordered coordinate product
(blueprint: lem-pur-coordinate-successor-support-geometry). -/
abbrev successorTailMap (B : Scheme.{u}) (r : ℕ) :
    successorTail B r ⟶ iteratedAffineLine B (r + 1) :=
  supportMap B (r + 1) (successorTailList r)

/-- Pullback of an old coordinate is its successor-index coordinate.
Source: the polynomial coordinate definition in the ordered product.
(blueprint: lem-pur-coordinate-successor-support-geometry).
Proof: this is the defining successor clause of iteratedAffineLine.coord. -/
theorem successorCoordinate_pullback (B : Scheme.{u}) (r : ℕ) (i : Fin r) :
    (lastProjection B r).appTop (iteratedAffineLine.coord B r i) =
      iteratedAffineLine.coord B (r + 1) i.succ :=
  (iteratedAffineLine.coord_succ_succ B r i).symm

/-- The coordinate singleton sets are carried to their successor singleton sets.
Source: coordinate zero-locus pullback in the ordered product.
(blueprint: lem-pur-coordinate-successor-support-geometry).
Proof: the image of a singleton is the singleton of its image; apply the proved
coordinate pullback equation. -/
theorem successorCoordinate_set_pullback (B : Scheme.{u}) (r : ℕ) (i : Fin r) :
    (lastProjection B r).appTop '' {iteratedAffineLine.coord B r i} =
      {iteratedAffineLine.coord B (r + 1) i.succ} := by
  rw [Set.image_singleton, successorCoordinate_pullback]
  rfl

/-- The canonical map from an old-coordinate divisor in the next affine tower.
Source: coordinate zero-locus pullback in the ordered product.
(blueprint: lem-pur-coordinate-successor-support-geometry). -/
def successorDivisorProjection (B : Scheme.{u}) (r : ℕ) (i : Fin r) :
    divisor B (r + 1) i.succ ⟶ divisor B r i :=
  (lastProjection B r).zeroLocusSubschemeMap {iteratedAffineLine.coord B r i}
    {iteratedAffineLine.coord B (r + 1) i.succ} (successorCoordinate_set_pullback B r i)

/-- Every old-coordinate divisor square is Cartesian along the last projection.
Source: coordinate zero-locus pullback in the ordered product.
(blueprint: lem-pur-coordinate-successor-support-geometry).
Proof: base change of the zero locus of a global section is the zero locus of
its pullback. The two coordinate singleton sets agree by the preceding lemma. -/
theorem successorDivisor_isPullback (B : Scheme.{u}) (r : ℕ) (i : Fin r) :
    IsPullback (successorDivisorProjection B r i) (inclusion B (r + 1) i.succ)
      (inclusion B r i) (lastProjection B r) :=
  Scheme.isPullback_zeroLocusSubschemeι (lastProjection B r)
    {iteratedAffineLine.coord B r i} {iteratedAffineLine.coord B (r + 1) i.succ}
    (successorCoordinate_set_pullback B r i)

private theorem support_coordinate_zero (B : Scheme.{u}) (c : ℕ)
    (is : List (Fin c)) (i : Fin c) (hi : i ∈ is) :
    (supportMap B c is).appTop (iteratedAffineLine.coord B c i) = 0 := by
  induction is with
  | nil => exact False.elim (List.not_mem_nil hi)
  | cons j is ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · change (pullback.fst (supportMap B c is) (inclusion B c i) ≫
        supportMap B c is).appTop _ = 0
      rw [pullback.condition, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        Scheme.zeroLocusSubschemeι_appTop (Set.mem_singleton _), map_zero]
    · change (pullback.fst (supportMap B c is) (inclusion B c j) ≫
        supportMap B c is).appTop _ = 0
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ih hi, map_zero]

private def supportLift (B : Scheme.{u}) (c : ℕ) {T : Scheme.{u}} :
    ∀ (is : List (Fin c)) (f : T ⟶ iteratedAffineLine B c)
      (_h : ∀ i ∈ is, f.appTop (iteratedAffineLine.coord B c i) = 0),
      {g : T ⟶ support B c is // g ≫ supportMap B c is = f}
  | [], f, _ => ⟨f, Category.comp_id _⟩
  | i :: is, f, h =>
    let g := supportLift B c is f (fun j hj ↦ h j (List.mem_cons_of_mem i hj))
    let hker : (inclusion B c i).ker ≤ f.ker :=
      Scheme.IdealSheafData.le_ker_of_comap_eq_bot f (by
        rw [Scheme.IdealSheafData.ker_subschemeι,
          Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton,
          h i List.mem_cons_self, Ideal.span_singleton_zero]
        ext U
        simp only [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_bot,
          Scheme.IdealSheafData.ideal_bot]
        rfl)
    let k := IsClosedImmersion.lift (inclusion B c i) f hker
    let hk : k ≫ inclusion B c i = f := IsClosedImmersion.lift_fac _ _ _
    ⟨pullback.lift g.val k (g.property.trans hk.symm), by
      change pullback.lift _ _ _ ≫
        (pullback.fst (supportMap B c is) (inclusion B c i) ≫ supportMap B c is) = _
      rw [← Category.assoc, pullback.lift_fst, g.property]⟩

private theorem tower_hom_ext {B T : Scheme.{u}} (c : ℕ)
    (f g : T ⟶ iteratedAffineLine B c)
    (hp : f ≫ iteratedAffineLineProj B c = g ≫ iteratedAffineLineProj B c)
    (ht : ∀ i, f.appTop (iteratedAffineLine.coord B c i) =
      g.appTop (iteratedAffineLine.coord B c i)) : f = g := by
  induction c with
  | zero =>
    exact (Category.comp_id f).symm.trans (hp.trans (Category.comp_id g))
  | succ c ih =>
    apply AffineSpace.hom_ext (n := PUnit.{u + 1})
    · apply ih
      · have h := hp
        rw [iteratedAffineLineProj_succ] at h
        exact (Category.assoc f _ _).trans (h.trans (Category.assoc g _ _).symm)
      · intro i
        have h := ht i.succ
        rw [iteratedAffineLine.coord_succ_succ] at h
        let p : iteratedAffineLine B (c + 1) ⟶ iteratedAffineLine B c :=
          𝔸(PUnit.{u + 1}; iteratedAffineLine B c) ↘ iteratedAffineLine B c
        exact (show (f ≫ p).appTop _ = f.appTop (p.appTop _) by
          rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]).trans
          (h.trans (show (g ≫ p).appTop _ = g.appTop (p.appTop _) by
            rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]).symm)
    · intro i
      cases i
      exact ht 0

private theorem partial_old_coordinate_zero (B : Scheme.{u}) (r : ℕ)
    (is : List (Fin r)) {T : Scheme.{u}}
    (a : T ⟶ support B r is) (b : T ⟶ iteratedAffineLine B (r + 1))
    (h : a ≫ supportMap B r is = b ≫ lastProjection B r)
    (i : Fin r) (hi : i ∈ is) :
    b.appTop (iteratedAffineLine.coord B (r + 1) i.succ) = 0 := by
  change T ⟶ 𝔸(PUnit.{u + 1}; iteratedAffineLine B r) at b
  change a ≫ supportMap B r is =
    b ≫ (𝔸(PUnit.{u + 1}; iteratedAffineLine B r) ↘ iteratedAffineLine B r) at h
  rw [iteratedAffineLine.coord_succ_succ]
  calc
    _ = (b ≫ (𝔸(PUnit.{u + 1}; iteratedAffineLine B r) ↘
        iteratedAffineLine B r)).appTop (iteratedAffineLine.coord B r i) := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rfl
    _ = (a ≫ supportMap B r is).appTop (iteratedAffineLine.coord B r i) :=
      congrArg (fun f ↦ f.appTop (iteratedAffineLine.coord B r i)) h.symm
    _ = 0 := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        support_coordinate_zero B r is i hi, map_zero]

/-- The projected partial support has a unique lift to the old support.
Source: coordinate zero-locus pullback in the ordered product.
(blueprint: lem-pur-coordinate-successor-support-geometry).
Proof: all coordinates in the old list vanish after projection. Construct the
lift successively into their zero loci. Uniqueness follows from the old support
being a monomorphism. -/
theorem successorPartialProjection_existsUnique (B : Scheme.{u}) (r : ℕ)
    (is : List (Fin r)) :
    ∃! f : support B (r + 1) (is.map Fin.succ) ⟶ support B r is,
      f ≫ supportMap B r is =
        supportMap B (r + 1) (is.map Fin.succ) ≫ lastProjection B r := by
  let g := supportLift B r is
    (supportMap B (r + 1) (is.map Fin.succ) ≫ lastProjection B r) (by
      intro i hi
      have hz := support_coordinate_zero B (r + 1) (is.map Fin.succ) i.succ
        (List.mem_map.mpr ⟨i, hi, rfl⟩)
      let f : support B (r + 1) (is.map Fin.succ) ⟶
          𝔸(PUnit.{u + 1}; iteratedAffineLine B r) :=
        supportMap B (r + 1) (is.map Fin.succ)
      change (f ≫ (𝔸(PUnit.{u + 1}; iteratedAffineLine B r) ↘
        iteratedAffineLine B r)).appTop _ = _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      exact hz)
  exact ⟨g.val, g.property, fun f hf ↦
    (cancel_mono (supportMap B r is)).mp (hf.trans g.property.symm)⟩

/-- Every partial old-coordinate support maps to its counterpart in one lower rank.
Source: coordinate zero-locus pullback in the ordered product.
(blueprint: lem-pur-coordinate-successor-support-geometry). -/
def successorPartialProjection (B : Scheme.{u}) (r : ℕ) (is : List (Fin r)) :
    support B (r + 1) (is.map Fin.succ) ⟶ support B r is :=
  (successorPartialProjection_existsUnique B r is).choose

/-- The support projection commutes with the two closed immersions.
Source: coordinate zero-locus pullback in the ordered product.
(blueprint: lem-pur-coordinate-successor-support-geometry).
Proof: this is the characterizing equation of the unique support projection. -/
theorem successorPartialProjection_fac (B : Scheme.{u}) (r : ℕ) (is : List (Fin r)) :
    successorPartialProjection B r is ≫ supportMap B r is =
      supportMap B (r + 1) (is.map Fin.succ) ≫ lastProjection B r :=
  (successorPartialProjection_existsUnique B r is).choose_spec.1

/-- Every partial old-coordinate intersection is preserved by the last projection.
Source: coordinate zero-locus pullback in the ordered product.
(blueprint: lem-pur-coordinate-successor-support-geometry).
Proof: a cone has second leg with each coordinate in the list zero, as follows
by applying its commutative square to that coordinate. Lift it successively into
the listed zero loci. Its first projection is forced by the monomorphism of the
old support. The second is the lift equation; uniqueness uses the monomorphism
of the new support. Empty and repeated lists are included. -/
theorem successorPartial_isPullback (B : Scheme.{u}) (r : ℕ) (is : List (Fin r)) :
    IsPullback (successorPartialProjection B r is)
      (supportMap B (r + 1) (is.map Fin.succ))
      (supportMap B r is) (lastProjection B r) := by
  refine IsPullback.of_isLimit
    (c := PullbackCone.mk _ _ (successorPartialProjection_fac B r is)) ?_
  let lift (s : PullbackCone (supportMap B r is) (lastProjection B r)) :=
    supportLift B (r + 1) (is.map Fin.succ) s.snd (by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      exact partial_old_coordinate_zero B r is s.fst s.snd s.condition i hi)
  refine PullbackCone.IsLimit.mk _ (fun s ↦ (lift s).val) ?_ ?_ ?_
  · intro s
    apply (cancel_mono (supportMap B r is)).mp
    calc
      _ = (lift s).val ≫ (successorPartialProjection B r is ≫ supportMap B r is) :=
        Category.assoc _ _ _
      _ = (lift s).val ≫
          (supportMap B (r + 1) (is.map Fin.succ) ≫ lastProjection B r) :=
        congrArg (fun f ↦ (lift s).val ≫ f) (successorPartialProjection_fac B r is)
      _ = ((lift s).val ≫ supportMap B (r + 1) (is.map Fin.succ)) ≫
          lastProjection B r := (Category.assoc _ _ _).symm
      _ = s.snd ≫ lastProjection B r :=
        congrArg (fun f ↦ f ≫ lastProjection B r) (lift s).property
      _ = s.fst ≫ supportMap B r is := s.condition.symm
  · intro s
    exact (lift s).property
  · intro s m _ hm
    exact (cancel_mono (supportMap B (r + 1) (is.map Fin.succ))).mp
      (hm.trans (lift s).property.symm)

/-- Projection of the old coordinate support onto the original base.
Source: the old coordinates vanish
(blueprint: lem-pur-coordinate-successor-support-geometry). -/
def successorTailProjection (B : Scheme.{u}) (r : ℕ) : successorTail B r ⟶ B :=
  successorTailMap B r ≫ lastProjection B r ≫ iteratedAffineLineProj B r

/-- On the old coordinate support, the last projection factors through the zero section.
Source: the polynomial-chart argument of the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-successor-support-geometry).
Proof: both maps have the same base projection. Every old coordinate vanishes on
its closed intersection, so every coordinate also agrees. Apply the universal
property of the iterated affine space. -/
theorem successorTailProjection_zero (B : Scheme.{u}) (r : ℕ) :
    successorTailProjection B r ≫ zero B r = successorTailMap B r ≫ lastProjection B r := by
  apply tower_hom_ext r
  · unfold successorTailProjection
    simp only [Category.assoc, zero_proj, Category.comp_id]
    exact (Category.assoc _ _ _).symm
  · intro i
    have hi : i.succ ∈ successorTailList r :=
      List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have hz := support_coordinate_zero B (r + 1) (successorTailList r) i.succ hi
    rw [zero, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Scheme.Hom.toIteratedAffineLine_appTop_coord, map_zero]
    rw [iteratedAffineLine.coord_succ_succ] at hz
    exact hz.symm

private theorem old_coordinate_zero (B : Scheme.{u}) (r : ℕ) {T : Scheme.{u}}
    (a : T ⟶ B) (b : T ⟶ iteratedAffineLine B (r + 1))
    (h : a ≫ zero B r = b ≫ lastProjection B r) (i : Fin r) :
    b.appTop (iteratedAffineLine.coord B (r + 1) i.succ) = 0 := by
  change a ≫ zero B r =
    b ≫ (𝔸(PUnit.{u + 1}; iteratedAffineLine B r) ↘ iteratedAffineLine B r) at h
  change T ⟶ 𝔸(PUnit.{u + 1}; iteratedAffineLine B r) at b
  rw [iteratedAffineLine.coord_succ_succ]
  calc
    _ = (b ≫ (𝔸(PUnit.{u + 1}; iteratedAffineLine B r) ↘
        iteratedAffineLine B r)).appTop (iteratedAffineLine.coord B r i) := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rfl
    _ = (a ≫ zero B r).appTop (iteratedAffineLine.coord B r i) :=
      congrArg (fun f ↦ f.appTop (iteratedAffineLine.coord B r i)) h.symm
    _ = 0 := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, zero,
        Scheme.Hom.toIteratedAffineLine_appTop_coord, map_zero]

/-- The old coordinate support is exactly the pullback of the rank-r zero section.
Source: the polynomial-chart argument of the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-successor-support-geometry).
Proof: in any cone over the zero section and last projection, every old
coordinate of the second leg is zero. Lift that leg successively into its
coordinate zero loci and their pullbacks. The first projection equation follows
by composing the cone equation with the affine-space projection. The second is
the defining equation of the successive lift. Uniqueness follows because the
support immersion is a monomorphism. This also covers r=0 and an empty base. -/
theorem successorTail_isPullback (B : Scheme.{u}) (r : ℕ) :
    IsPullback (successorTailProjection B r) (successorTailMap B r)
      (zero B r) (lastProjection B r) := by
  refine IsPullback.of_isLimit
    (c := PullbackCone.mk _ _ (successorTailProjection_zero B r)) ?_
  let lift (s : PullbackCone (zero B r) (lastProjection B r)) :=
    supportLift B (r + 1) (successorTailList r) s.snd (by
      intro j hj
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
      exact old_coordinate_zero B r s.fst s.snd s.condition i)
  refine PullbackCone.IsLimit.mk _ (fun s ↦ (lift s).val) ?_ ?_ ?_
  · intro s
    change (lift s).val ≫
      (successorTailMap B r ≫ lastProjection B r ≫ iteratedAffineLineProj B r) = s.fst
    calc
      _ = (s.snd ≫ lastProjection B r) ≫ iteratedAffineLineProj B r := by
        rw [← Category.assoc, (lift s).property]
        exact (Category.assoc _ _ _).symm
      _ = (s.fst ≫ zero B r) ≫ iteratedAffineLineProj B r :=
        congrArg (fun f ↦ f ≫ iteratedAffineLineProj B r) s.condition.symm
      _ = s.fst := by rw [Category.assoc, zero_proj, Category.comp_id]
  · intro s
    exact (lift s).property
  · intro s m _ hm
    exact (cancel_mono (successorTailMap B r)).mp (hm.trans (lift s).property.symm)

/-- The chosen Cartesian square supplied by the literal old coordinate intersection.
Source: old-coordinate pullback in the affine tower
(blueprint: lem-pur-coordinate-successor-support-geometry). -/
def successorTailSquare (B : Scheme.{u}) (r : ℕ) :
    ChosenCartesianSquare (successorTailProjection B r) (successorTailMap B r)
      (zero B r) (lastProjection B r) where
  toCommSq := (successorTail_isPullback B r).toCommSq
  isoPullback := (successorTail_isPullback B r).isoPullback
  hom_fst := (successorTail_isPullback B r).isoPullback_hom_fst
  hom_snd := (successorTail_isPullback B r).isoPullback_hom_snd

/-- Restricting the affine projection and its zero section to the newest divisor
is identity on its image.
Source: the last-coordinate zero locus in the affine-space product.
(blueprint: lem-pur-coordinate-successor-support-geometry).
Proof: the two maps have the same affine projection and newest coordinate zero,
so the universal property of the affine line identifies them. -/
theorem successorLastCoordinate_retraction (B : Scheme.{u}) (r : ℕ) :
    inclusion B (r + 1) 0 ≫ lastProjection B r ≫ lastSection B r =
      inclusion B (r + 1) 0 := by
  let f : divisor B (r + 1) 0 ⟶ 𝔸(PUnit.{u + 1}; iteratedAffineLine B r) :=
    inclusion B (r + 1) 0
  let q := 𝔸(PUnit.{u + 1}; iteratedAffineLine B r) ↘ iteratedAffineLine B r
  let s : iteratedAffineLine B r ⟶ 𝔸(PUnit.{u + 1}; iteratedAffineLine B r) :=
    lastSection B r
  have hs : s ≫ q = 𝟙 _ :=
    Scheme.Hom.toIteratedAffineLine_comp_over (𝟙 _) (fun _ ↦ 0)
  have hz : s.appTop (AffineSpace.coord (iteratedAffineLine B r) PUnit.unit) = 0 :=
    Scheme.Hom.toIteratedAffineLine_appTop_coord (𝟙 _) (fun _ ↦ 0) 0
  have hf : f.appTop (AffineSpace.coord (iteratedAffineLine B r) PUnit.unit) = 0 :=
    Scheme.zeroLocusSubschemeι_appTop (Set.mem_singleton _)
  change f ≫ q ≫ s = f
  apply AffineSpace.hom_ext (n := PUnit.{u + 1})
  · change (f ≫ q ≫ s) ≫ q = f ≫ q
    simp only [Category.assoc, hs, Category.comp_id]
  · intro i
    cases i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hz, map_zero, map_zero, hf]

/-- The last zero section lifts uniquely to the actual newest coordinate divisor.
Source: the last-coordinate zero locus in the affine-space product.
(blueprint: lem-pur-coordinate-successor-support-geometry).
Proof: its newest coordinate is zero. The ideal of that coordinate therefore
lies in its kernel, giving a closed-immersion lift. The divisor inclusion is
monic, so this lift is unique. -/
theorem successorLastCoordinateLift_existsUnique (B : Scheme.{u}) (r : ℕ) :
    ∃! f : iteratedAffineLine B r ⟶ divisor B (r + 1) 0,
      f ≫ inclusion B (r + 1) 0 = lastSection B r := by
  have hz : (lastSection B r).appTop (iteratedAffineLine.coord B (r + 1) 0) = 0 := by
    change (zero (iteratedAffineLine B r) 1).appTop
      (iteratedAffineLine.coord (iteratedAffineLine B r) 1 0) = 0
    exact Scheme.Hom.toIteratedAffineLine_appTop_coord (𝟙 _) (fun _ ↦ 0) 0
  have hker : (inclusion B (r + 1) 0).ker ≤ (lastSection B r).ker :=
    Scheme.IdealSheafData.le_ker_of_comap_eq_bot (lastSection B r) (by
      rw [Scheme.IdealSheafData.ker_subschemeι,
        Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton,
        hz, Ideal.span_singleton_zero]
      ext U
      simp only [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_bot,
        Scheme.IdealSheafData.ideal_bot]
      rfl)
  refine ⟨IsClosedImmersion.lift (inclusion B (r + 1) 0) (lastSection B r) hker,
    IsClosedImmersion.lift_fac _ _ _, ?_⟩
  intro f hf
  exact (cancel_mono (inclusion B (r + 1) 0)).mp
    (hf.trans (IsClosedImmersion.lift_fac _ _ _).symm)

/-- The newest coordinate divisor is canonically the last zero section, with
inverse given by the affine projection.
Source: the last-coordinate zero locus in the affine-space product.
(blueprint: lem-pur-coordinate-successor-support-geometry). -/
def successorLastCoordinateIso (B : Scheme.{u}) (r : ℕ) :
    iteratedAffineLine B r ≅ divisor B (r + 1) 0 := by
  let l := (successorLastCoordinateLift_existsUnique B r).choose
  have hl : l ≫ inclusion B (r + 1) 0 = lastSection B r :=
    (successorLastCoordinateLift_existsUnique B r).choose_spec.1
  refine ⟨l, inclusion B (r + 1) 0 ≫ lastProjection B r, ?_, ?_⟩
  · exact (Category.assoc l (inclusion B (r + 1) 0) (lastProjection B r)).symm.trans
      ((congrArg (fun f ↦ f ≫ lastProjection B r) hl).trans
        (Scheme.Hom.toIteratedAffineLine_comp_over (𝟙 _) (fun _ ↦ 0)))
  · apply (cancel_mono (inclusion B (r + 1) 0)).mp
    exact (Category.assoc (inclusion B (r + 1) 0 ≫ lastProjection B r) l
        (inclusion B (r + 1) 0)).trans
      ((Category.assoc (inclusion B (r + 1) 0) (lastProjection B r)
        (l ≫ inclusion B (r + 1) 0)).trans
        ((congrArg (fun f ↦ inclusion B (r + 1) 0 ≫ lastProjection B r ≫ f) hl).trans
          ((successorLastCoordinate_retraction B r).trans (Category.id_comp _).symm)))

/-- The canonical divisor isomorphism is over the successor affine tower.
Source: the last-coordinate zero locus in the affine-space product.
(blueprint: lem-pur-coordinate-successor-support-geometry).
Proof: this is the equation specifying its uniquely determined lift. -/
theorem successorLastCoordinateIso_hom_inclusion (B : Scheme.{u}) (r : ℕ) :
    (successorLastCoordinateIso B r).hom ≫ inclusion B (r + 1) 0 = lastSection B r :=
  (successorLastCoordinateLift_existsUnique B r).choose_spec.1

/-- Exact pullback and the normalized closed-coefficient exchange on the old support.
Source: old-coordinate pullback in the affine tower
(blueprint: lem-pur-coordinate-successor-support-geometry). -/
def successorTailSourcePullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (r : ℕ) :
    (inverseImage (setting P n).Coefficient (lastProjection B r)).obj
      ((cupSingle (setting P n) (iteratedAffineLine B r)).obj
        ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B r)).obj
          ((setting P n).constant B))) ≅
      classSource P n B (r + 1) (successorTailList r) :=
  pullbackSingle (setting P n).Coefficient (lastProjection B r) _ _
      ((setting P n).functorialCupExchange true (zero B r) (successorTailMap B r)
        (lastProjection B r) (successorTailProjection B r) (successorTailSquare B r)) ≪≫
    (eqToIso (classSource_eq P n B (r + 1) (successorTailList r))).symm

end AlgebraicGeometry.ProEtale.AffineZeroPurity
