/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.RingTheory.PthRootAlgebraLocal
public import Sheaf.Paper.StrictLocalKummerTameModule
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Compatible unit changes on parameter-root towers

Source: ILO, Travaux de Gabber, IX Proposition 2.1, printed p.133, and the explicit
substitution argument in the DAG (blueprint: lem-sfb-unit-root-coordinate-tower-comparison).

An optional order denotes a finite stage (`some n`) or the full stage (`none`).
An optional boundary denotes no reduction, or reduction by root coordinates (tag 0),
coefficient equations (tag 1), or their product (tag 2). The last Boolean in a view
specifies whether the original boundary product is inverted. These are actual quotient
and localization constructions, including the zero ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open AlgebraicGeometry.ProEtale
open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.UnitRootCoordinates

/-- Finite and full stages, using the existing simultaneous and compatible-root quotients.
Source: ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
abbrev stage (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    (k : Option (TameRootOrder p)) : Type u :=
  match k with
  | some n => Algebra.pthRootAlgebra n.val r H t
  | none => tameRootAlgebra p t

/-- The ring structures of the existing stages. Source: ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
instance stageCommRing (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    (k : Option (TameRootOrder p)) : CommRing (stage p t k) :=
  match k with
  | some _ => inferInstance
  | none => inferInstance

/-- The coefficient structures of the existing stages. Source: ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
instance stageAlgebra (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    (k : Option (TameRootOrder p)) : Algebra H (stage p t k) :=
  match k with
  | some _ => inferInstance
  | none => inferInstance

/-- Labels of the polynomial generators at a finite or full stage. Source: ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
abbrev labels (p r : ℕ) (k : Option (TameRootOrder p)) : Type :=
  match k with
  | some _ => Fin r
  | none => Fin r × TameRootOrder p

/-- The parameter index of a labelled root. Source: ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
def labelIndex (p r : ℕ) (k : Option (TameRootOrder p)) : labels p r k → Fin r :=
  match k with
  | some _ => id
  | none => Prod.fst

/-- The order of a labelled root. Source: ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
def labelOrder (p r : ℕ) (k : Option (TameRootOrder p)) : labels p r k → TameRootOrder p :=
  match k with
  | some n => fun _ => n
  | none => Prod.snd

/-- The actual polynomial class of a labelled root. Source: ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
def root (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    (k : Option (TameRootOrder p)) : labels p r k → stage p t k :=
  match k with
  | some _ => fun i => Ideal.Quotient.mk _ (MvPolynomial.X i)
  | none => fun i => Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- Both boundary ideals, and principal ideals of products of boundary equations.
Source: the boundary-reduction calculation in DAG proof step 5, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
def boundaryIdeal (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    (k : Option (TameRootOrder p)) (d : Fin 3 × Finset (Fin r)) : Ideal (stage p t k) :=
  if d.1 = 0 then
    Ideal.span {x | ∃ j : labels p r k, labelIndex p r k j ∈ d.2 ∧ x = root p t k j}
  else if d.1 = 1 then
    Ideal.span {x | ∃ i ∈ d.2, x = algebraMap H (stage p t k) (t i)}
  else Ideal.span {algebraMap H (stage p t k) (∏ i ∈ d.2, t i)}

/-- A stage with the specified optional boundary reduction. Source: DAG proof step 5,
ILO IX 2.1, p.133 (blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
abbrev reduced (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    (k : Option (TameRootOrder p)) (d : Option (Fin 3 × Finset (Fin r))) : Type u :=
  match d with
  | none => stage p t k
  | some s => stage p t k ⧸ boundaryIdeal p t k s

/-- Quotient ring structure. Source: ILO IX 2.1, p.133 and DAG proof step 5
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
instance reducedCommRing (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    (k : Option (TameRootOrder p)) (d : Option (Fin 3 × Finset (Fin r))) :
    CommRing (reduced p t k d) :=
  match d with
  | none => inferInstance
  | some _ => inferInstance

/-- Canonical reduction map. Source: DAG proof step 5, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
def reductionMap (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    (k : Option (TameRootOrder p)) (d : Option (Fin 3 × Finset (Fin r))) :
    stage p t k →+* reduced p t k d :=
  match d with
  | none => RingHom.id _
  | some _ => Ideal.Quotient.mk _

/-- A finite/full, residual/unreduced, punctured/unpunctured ring.
Source: DAG proof steps 4-5, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
abbrev view (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    (k : Option (TameRootOrder p)) (d : Option (Fin 3 × Finset (Fin r))) (q : Bool) : Type u :=
  match q with
  | false => reduced p t k d
  | true => Localization.Away (reductionMap p t k d (algebraMap H _ (∏ i, t i)))

/-- The actual localization or quotient ring structure. Source: DAG proof steps 4-5,
ILO IX 2.1, p.133 (blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
instance viewCommRing (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    (k : Option (TameRootOrder p)) (d : Option (Fin 3 × Finset (Fin r))) (q : Bool) :
    CommRing (view p t k d q) :=
  match q with
  | false => inferInstance
  | true => inferInstance

/-- Canonical map to the specified boundary quotient and localization.
Source: DAG proof steps 4-5, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
def viewMap (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    (k : Option (TameRootOrder p)) (d : Option (Fin 3 × Finset (Fin r))) (q : Bool) :
    stage p t k →+* view p t k d q :=
  match q with
  | false => reductionMap p t k d
  | true => (algebraMap (reduced p t k d) _).comp (reductionMap p t k d)

/-- Exactly the specified units and coherent roots of a change of equations.
Source: DAG statement, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
structure Change (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t t' : Fin r → H) where
  unit : Fin r → Hˣ
  equation : ∀ i, t' i = (unit i : H) * t i
  rootUnit : Fin r → TameRootOrder p → Hˣ
  power : ∀ i n, rootUnit i n ^ n.val = unit i
  coherent : ∀ i n m, n.val ∣ m.val → rootUnit i m ^ (m.val / n.val) = rootUnit i n

/-- Power transitions and coprojections at every residual and punctured level.
Source: DAG proof steps 2-5, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
structure TowerMaps (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H) where
  transition : ∀ (n m : TameRootOrder p), n.val ∣ m.val →
    ∀ (d : Option (Fin 3 × Finset (Fin r))) (q : Bool),
      view p t (some n) d q →+* view p t (some m) d q
  inclusion : ∀ (n : TameRootOrder p) (d : Option (Fin 3 × Finset (Fin r))) (q : Bool),
    view p t (some n) d q →+* view p t none d q
  transition_coeff : ∀ n m h d q a,
    transition n m h d q (viewMap p t (some n) d q (algebraMap H _ a)) =
      viewMap p t (some m) d q (algebraMap H _ a)
  transition_root : ∀ n m h d q i,
    transition n m h d q (viewMap p t (some n) d q (root p t (some n) i)) =
      viewMap p t (some m) d q (root p t (some m) i) ^ (m.val / n.val)
  inclusion_coeff : ∀ n d q a,
    inclusion n d q (viewMap p t (some n) d q (algebraMap H _ a)) =
      viewMap p t none d q (algebraMap H _ a)
  inclusion_root : ∀ n d q i,
    inclusion n d q (viewMap p t (some n) d q (root p t (some n) i)) =
      viewMap p t none d q (root p t none (i, n))
  transition_id : ∀ n d q x, transition n n (dvd_refl n.val) d q x = x
  transition_comp : ∀ n m l h₁ h₂ d q x,
    transition m l h₂ d q (transition n m h₁ d q x) =
      transition n l (dvd_trans h₁ h₂) d q x
  inclusion_compatible : ∀ n m h d q x,
    inclusion m d q (transition n m h d q x) = inclusion n d q x

/-- The thin divisibility category of positive prime-to-p orders. Source: DAG proof step 3,
ILO IX 2.1, p.133 (blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
instance orderCategory (p : ℕ) : SmallCategory (TameRootOrder p) where
  Hom n m := PLift (n.val ∣ m.val)
  id n := ⟨dvd_refl n.val⟩
  comp f g := ⟨dvd_trans f.down g.down⟩
  id_comp := fun _ ↦ Subsingleton.elim _ _
  comp_id := fun _ ↦ Subsingleton.elim _ _
  assoc := fun _ _ _ ↦ Subsingleton.elim _ _

/-- The actual finite-stage power homomorphism as an algebra homomorphism.
Source: DAG proof steps 2-3, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
def TowerMaps.finiteMap {p : ℕ} {H : Type u} [CommRing H] {r : ℕ} {t : Fin r → H}
    (T : TowerMaps p t) (n m : TameRootOrder p) (h : n.val ∣ m.val) :
    stage p t (some n) →ₐ[H] stage p t (some m) :=
  { T.transition n m h none false with commutes' := T.transition_coeff n m h none false }

/-- The actual finite-to-full coprojection as an algebra homomorphism.
Source: DAG proof step 3, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
def TowerMaps.fullMap {p : ℕ} {H : Type u} [CommRing H] {r : ℕ} {t : Fin r → H}
    (T : TowerMaps p t) (n : TameRootOrder p) :
    stage p t (some n) →ₐ[H] stage p t none :=
  { T.inclusion n none false with commutes' := T.inclusion_coeff n none false }

/-- The divisibility diagram in commutative H-algebras, with the actual stages as objects.
Source: DAG proof step 3, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
def TowerMaps.diagram {p : ℕ} {H : Type u} [CommRing H] {r : ℕ} {t : Fin r → H}
    (T : TowerMaps p t) : TameRootOrder p ⥤ CommAlgCat.{u} H where
  obj n := CommAlgCat.of H (stage p t (some n))
  map {n m} h := CommAlgCat.ofHom (T.finiteMap n m h.down)
  map_id n := CommAlgCat.hom_ext (AlgHom.ext (T.transition_id n none false))
  map_comp f g := CommAlgCat.hom_ext
    (AlgHom.ext (fun x ↦ (T.transition_comp _ _ _ f.down g.down none false x).symm))

/-- The full compatible-root quotient as a cocone on the finite stages.
Source: DAG proof step 3, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
def TowerMaps.cocone {p : ℕ} {H : Type u} [CommRing H] {r : ℕ} {t : Fin r → H}
    (T : TowerMaps p t) : Cocone T.diagram where
  pt := CommAlgCat.of H (stage p t none)
  ι :=
    { app := fun n ↦ CommAlgCat.ofHom (T.fullMap n)
      naturality := fun n m h ↦ CommAlgCat.hom_ext
        (AlgHom.ext (T.inclusion_compatible n m h.down none false)) }

/-- A power tower whose full presented algebra is its categorical colimit.
Source: DAG proof step 3, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
structure Tower (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H)
    extends TowerMaps p t where
  isColimit : IsColimit toTowerMaps.cocone

/-- A coefficient homomorphism on all the actual quotient and localization views.
Source: DAG proof step 6, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
structure CoefficientMap (p : ℕ) {H K : Type u} [CommRing H] [CommRing K] {r : ℕ}
    (t : Fin r → H) (s : Fin r → K) (h : H →+* K) where
  map : ∀ k d q, view p t k d q →+* view p s k d q
  coeff : ∀ k d q a, map k d q (viewMap p t k d q (algebraMap H _ a)) =
    viewMap p s k d q (algebraMap K _ (h a))
  root : ∀ k d q j, map k d q (viewMap p t k d q (UnitRootCoordinates.root p t k j)) =
    viewMap p s k d q (UnitRootCoordinates.root p s k j)
  descend : ∀ k d q x,
    map k d q (viewMap p t k d q x) = viewMap p s k d q (map k none false x)

/-- The canonical unit substitution at all levels, with its quotient/localization squares.
Specifying coefficients and labelled generators determines each map uniquely.
Source: DAG proof steps 1, 3-5, ILO IX 2.1, p.133
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison). -/
structure Comparison (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} {t t' : Fin r → H}
    (c : Change p t t') where
  equiv : ∀ k d q, view p t' k d q ≃+* view p t k d q
  coeff : ∀ k d q a, equiv k d q (viewMap p t' k d q (algebraMap H _ a)) =
    viewMap p t k d q (algebraMap H _ a)
  root : ∀ k d q j,
    equiv k d q (viewMap p t' k d q (UnitRootCoordinates.root p t' k j)) =
      viewMap p t k d q
        (algebraMap H _ (c.rootUnit (labelIndex p r k j) (labelOrder p r k j) : H) *
          UnitRootCoordinates.root p t k j)
  descend : ∀ k d q x,
    equiv k d q (viewMap p t' k d q x) = viewMap p t k d q (equiv k none false x)

private theorem stage_ext {p : ℕ} {H B : Type u} [CommRing H] [CommRing B]
    {r : ℕ} {t : Fin r → H} (k : Option (TameRootOrder p))
    {f g : stage p t k →+* B}
    (hc : ∀ a, f (algebraMap H _ a) = g (algebraMap H _ a))
    (hx : ∀ j, f (root p t k j) = g (root p t k j)) : f = g := by
  cases k with
  | none =>
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · exact hc
    · exact hx
  | some n =>
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · exact hc
    · exact hx

private theorem root_pow {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (k : Option (TameRootOrder p)) (j : labels p r k) :
    root p t k j ^ (labelOrder p r k j).val =
      algebraMap H _ (t (labelIndex p r k j)) := by
  cases k with
  | none =>
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk _ (MvPolynomial.X j) ^ _ -
      Ideal.Quotient.mk _ (MvPolynomial.C _) = 0
    rw [← map_pow, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Or.inl ⟨j.1, j.2, rfl⟩))
  | some n =>
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk _ (MvPolynomial.X j) ^ _ -
      Ideal.Quotient.mk _ (MvPolynomial.C _) = 0
    rw [← map_pow, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)

private theorem root_coherent {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (i : Fin r) (n m : TameRootOrder p) (h : n.val ∣ m.val) :
    root p t none (i, m) ^ (m.val / n.val) = root p t none (i, n) := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk _ (MvPolynomial.X (i, m)) ^ _ -
    Ideal.Quotient.mk _ (MvPolynomial.X (i, n)) = 0
  rw [← map_pow, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Or.inr ⟨i, n, m, h, rfl⟩))

private def stageLift {p : ℕ} {H B : Type u} [CommRing H] [CommRing B]
    {r : ℕ} (t : Fin r → H) (k : Option (TameRootOrder p))
    (f : H →+* B) (y : labels p r k → B)
    (hy : ∀ j, y j ^ (labelOrder p r k j).val = f (t (labelIndex p r k j)))
    (hz : ∀ (i : Fin r) (n m : TameRootOrder p) (_h : n.val ∣ m.val),
      ∀ e : k = none, y (e ▸ (i, m)) ^ (m.val / n.val) = y (e ▸ (i, n))) :
    stage p t k →+* B := by
  cases k with
  | some n =>
    refine Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom f y) ?_
    change Ideal.span _ ≤ RingHom.ker (MvPolynomial.eval₂Hom f y)
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change MvPolynomial.eval₂Hom f y (_ ^ _ - _) = 0
    simpa [labelOrder, labelIndex] using sub_eq_zero.mpr (hy i)
  | none =>
    refine Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom f y) ?_
    change Ideal.span _ ≤ RingHom.ker (MvPolynomial.eval₂Hom f y)
    apply Ideal.span_le.mpr
    rintro a (⟨i, n, rfl⟩ | ⟨i, n, m, h, rfl⟩)
    · change MvPolynomial.eval₂Hom f y (_ ^ _ - _) = 0
      simpa [labelOrder, labelIndex] using sub_eq_zero.mpr (hy (i, n))
    · change MvPolynomial.eval₂Hom f y (_ ^ _ - _) = 0
      simpa using sub_eq_zero.mpr (hz i n m h rfl)

private theorem stageLift_coeff {p : ℕ} {H B : Type u} [CommRing H] [CommRing B]
    {r : ℕ} (t : Fin r → H) (k : Option (TameRootOrder p))
    (f : H →+* B) (y : labels p r k → B) (hy hz) (a : H) :
    stageLift t k f y hy hz (algebraMap H _ a) = f a := by
  cases k <;>
    dsimp only [stageLift] <;>
    change Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ (MvPolynomial.C a)) = _ <;>
    simp

private theorem stageLift_root {p : ℕ} {H B : Type u} [CommRing H] [CommRing B]
    {r : ℕ} (t : Fin r → H) (k : Option (TameRootOrder p))
    (f : H →+* B) (y : labels p r k → B) (hy hz) (j : labels p r k) :
    stageLift t k f y hy hz (root p t k j) = y j := by
  cases k <;> simp [stageLift, root]

private theorem reduced_ext {p : ℕ} {H B : Type u} [CommRing H] [CommRing B]
    {r : ℕ} {t : Fin r → H} (k : Option (TameRootOrder p))
    (d : Option (Fin 3 × Finset (Fin r))) {f g : reduced p t k d →+* B}
    (h : ∀ x, f (reductionMap p t k d x) = g (reductionMap p t k d x)) : f = g := by
  cases d with
  | none => exact RingHom.ext h
  | some d => exact Ideal.Quotient.ringHom_ext (RingHom.ext h)

private theorem view_ext {p : ℕ} {H B : Type u} [CommRing H] [CommRing B]
    {r : ℕ} {t : Fin r → H} (k : Option (TameRootOrder p))
    (d : Option (Fin 3 × Finset (Fin r))) (q : Bool) {f g : view p t k d q →+* B}
    (hc : ∀ a, f (viewMap p t k d q (algebraMap H _ a)) =
      g (viewMap p t k d q (algebraMap H _ a)))
    (hx : ∀ j, f (viewMap p t k d q (root p t k j)) =
      g (viewMap p t k d q (root p t k j))) : f = g := by
  have hstage : f.comp (viewMap p t k d q) = g.comp (viewMap p t k d q) :=
    stage_ext k hc hx
  cases q with
  | false => exact reduced_ext k d (RingHom.congr_fun hstage)
  | true =>
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (reductionMap p t k d (algebraMap H _ (∏ i, t i))))
    exact reduced_ext k d (RingHom.congr_fun hstage)

private def reducedLift {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} {t : Fin r → H} {s : Fin r → K} {k l : Option (TameRootOrder p)}
    (f : stage p t k →+* stage p s l)
    (hb : ∀ d, boundaryIdeal p t k d ≤ (boundaryIdeal p s l d).comap f)
    (d : Option (Fin 3 × Finset (Fin r))) : reduced p t k d →+* reduced p s l d :=
  match d with
  | none => f
  | some d => Ideal.quotientMap _ f (hb d)

private theorem reducedLift_apply {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} {t : Fin r → H} {s : Fin r → K} {k l : Option (TameRootOrder p)}
    (f : stage p t k →+* stage p s l) (hb) (d) (x : stage p t k) :
    reducedLift f hb d (reductionMap p t k d x) = reductionMap p s l d (f x) := by
  cases d <;> rfl

private def viewLift {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} {t : Fin r → H} {s : Fin r → K} {k l : Option (TameRootOrder p)}
    (f : stage p t k →+* stage p s l)
    (hb : ∀ d, boundaryIdeal p t k d ≤ (boundaryIdeal p s l d).comap f)
    (hu : ∀ d, IsUnit ((algebraMap (reduced p s l d)
      (view p s l d true)) (reductionMap p s l d (f (algebraMap H _ (∏ i, t i))))))
    (d : Option (Fin 3 × Finset (Fin r))) (q : Bool) :
    view p t k d q →+* view p s l d q := by
  cases q with
  | false => exact reducedLift f hb d
  | true =>
    apply IsLocalization.Away.lift
      (reductionMap p t k d (algebraMap H _ (∏ i, t i)))
      (g := (algebraMap (reduced p s l d) _).comp (reducedLift f hb d))
    simpa only [RingHom.comp_apply, reducedLift_apply] using hu d

private theorem viewLift_apply {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} {t : Fin r → H} {s : Fin r → K} {k l : Option (TameRootOrder p)}
    (f : stage p t k →+* stage p s l) (hb hu) (d q) (x : stage p t k) :
    viewLift f hb hu d q (viewMap p t k d q x) = viewMap p s l d q (f x) := by
  cases q with
  | false => exact reducedLift_apply f hb d x
  | true =>
    simp only [viewLift, viewMap, RingHom.comp_apply,
      IsLocalization.Away.lift_eq, reducedLift_apply]

private theorem coefficient_product {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} {t : Fin r → H} {s : Fin r → K} {k l : Option (TameRootOrder p)}
    (f : stage p t k →+* stage p s l) (h : H →+* K) (a : Fin r → Kˣ)
    (hc : ∀ x, f (algebraMap H _ x) = algebraMap K _ (h x))
    (ht : ∀ i, h (t i) = (a i : K) * s i) (S : Finset (Fin r)) :
    f (algebraMap H _ (∏ i ∈ S, t i)) =
      algebraMap K _ (∏ i ∈ S, (a i : K)) * algebraMap K _ (∏ i ∈ S, s i) := by
  rw [hc, map_prod]
  simp_rw [ht]
  rw [Finset.prod_mul_distrib, map_mul]

private theorem boundary_preserved {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} {t : Fin r → H} {s : Fin r → K} {k l : Option (TameRootOrder p)}
    (f : stage p t k →+* stage p s l) (h : H →+* K) (a : Fin r → Kˣ)
    (hc : ∀ x, f (algebraMap H _ x) = algebraMap K _ (h x))
    (ht : ∀ i, h (t i) = (a i : K) * s i)
    (hx : ∀ S j, labelIndex p r k j ∈ S →
      f (root p t k j) ∈ boundaryIdeal p s l (0, S))
    (d : Fin 3 × Finset (Fin r)) :
    boundaryIdeal p t k d ≤ (boundaryIdeal p s l d).comap f := by
  classical
  unfold boundaryIdeal
  split_ifs with h0 h1
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    exact hx d.2 j hj
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change f (algebraMap H _ (t i)) ∈
      Ideal.span {x | ∃ i ∈ d.2, x = algebraMap K (stage p s l) (s i)}
    rw [hc, ht, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, hi, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    change f (algebraMap H _ (∏ i ∈ d.2, t i)) ∈
      Ideal.span {algebraMap K (stage p s l) (∏ i ∈ d.2, s i)}
    rw [coefficient_product f h a hc ht]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

private theorem puncture_unit {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} {t : Fin r → H} {s : Fin r → K} {k l : Option (TameRootOrder p)}
    (f : stage p t k →+* stage p s l) (h : H →+* K) (a : Fin r → Kˣ)
    (hc : ∀ x, f (algebraMap H _ x) = algebraMap K _ (h x))
    (ht : ∀ i, h (t i) = (a i : K) * s i) (d) :
    IsUnit ((algebraMap (reduced p s l d) (view p s l d true))
      (reductionMap p s l d (f (algebraMap H _ (∏ i, t i))))) := by
  rw [coefficient_product f h a hc ht, map_mul, map_mul]
  apply IsUnit.mul
  · apply IsUnit.map
    apply IsUnit.map
    apply IsUnit.map
    exact IsUnit.prod_univ_iff.mpr (fun i ↦ (a i).isUnit)
  · exact IsLocalization.Away.algebraMap_isUnit _

private def coefficientStage {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} (t : Fin r → H) (s : Fin r → K) (h : H →+* K)
    (ht : ∀ i, h (t i) = s i) (k : Option (TameRootOrder p)) :
    stage p t k →+* stage p s k :=
  stageLift t k ((algebraMap K _).comp h) (root p s k)
    (fun j ↦ by rw [root_pow, RingHom.comp_apply, ht])
    (fun i n m hn e ↦ by subst k; exact root_coherent s i n m hn)

private theorem coefficientStage_coeff {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} (t : Fin r → H) (s : Fin r → K) (h : H →+* K) (ht)
    (k : Option (TameRootOrder p)) (a : H) :
    coefficientStage t s h ht k (algebraMap H _ a) = algebraMap K _ (h a) :=
  stageLift_coeff ..

private theorem coefficientStage_root {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} (t : Fin r → H) (s : Fin r → K) (h : H →+* K) (ht) (k) (j) :
    coefficientStage t s h ht k (root p t k j) = root p s k j :=
  stageLift_root ..

private def coefficientView {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} (t : Fin r → H) (s : Fin r → K) (h : H →+* K)
    (ht : ∀ i, h (t i) = s i) (k : Option (TameRootOrder p)) (d q) :
    view p t k d q →+* view p s k d q :=
  viewLift (coefficientStage t s h ht k)
    (boundary_preserved _ h (fun _ ↦ 1) (coefficientStage_coeff t s h ht k)
      (fun i ↦ by simpa using ht i) (fun S j hj ↦ by
        rw [coefficientStage_root]
        exact Ideal.subset_span (by simp only [Set.mem_ofPred_eq]; exact ⟨j, hj, rfl⟩)))
    (puncture_unit _ h (fun _ ↦ 1) (coefficientStage_coeff t s h ht k)
      (fun i ↦ by simpa using ht i)) d q

private theorem coefficientView_apply {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} (t : Fin r → H) (s : Fin r → K) (h : H →+* K) (ht) (k d q) (x) :
    coefficientView t s h ht k d q (viewMap p t k d q x) =
      viewMap p s k d q (coefficientStage t s h ht k x) := viewLift_apply ..

private def coefficientData {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} (t : Fin r → H) (s : Fin r → K) (h : H →+* K)
    (ht : ∀ i, h (t i) = s i) : CoefficientMap p t s h where
  map := coefficientView t s h ht
  coeff k d q a := by rw [coefficientView_apply, coefficientStage_coeff]
  root k d q j := by rw [coefficientView_apply, coefficientStage_root]
  descend k d q x := by
    rw [coefficientView_apply]
    rfl

private def changeInverse {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    {t t' : Fin r → H} (c : Change p t t') : Change p t' t where
  unit i := (c.unit i)⁻¹
  equation i := by rw [c.equation]; simp
  rootUnit i n := (c.rootUnit i n)⁻¹
  power i n := by rw [inv_pow, c.power]
  coherent i n m h := by rw [inv_pow, c.coherent i n m h]

private def changeStage {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    {t t' : Fin r → H} (c : Change p t t') (k : Option (TameRootOrder p)) :
    stage p t' k →+* stage p t k :=
  stageLift t' k (algebraMap H _)
    (fun j ↦ algebraMap H _ (c.rootUnit (labelIndex p r k j) (labelOrder p r k j) : H) *
      root p t k j)
    (fun j ↦ by
      rw [mul_pow, ← map_pow, root_pow]
      have hc := congrArg (fun z : Hˣ ↦ (z : H)) (c.power (labelIndex p r k j)
        (labelOrder p r k j))
      simp only [Units.val_pow_eq_pow_val] at hc
      rw [hc, ← map_mul, ← c.equation])
    (fun i n m h e ↦ by
      subst k
      dsimp only [labelIndex, labelOrder]
      rw [mul_pow, ← map_pow, root_coherent t i n m h]
      have hc := congrArg (fun z : Hˣ ↦ (z : H)) (c.coherent i n m h)
      simp only [Units.val_pow_eq_pow_val] at hc
      rw [hc])

private theorem changeStage_coeff {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    {t t' : Fin r → H} (c : Change p t t') (k) (a : H) :
    changeStage c k (algebraMap H _ a) = algebraMap H _ a := stageLift_coeff ..

private theorem changeStage_root {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    {t t' : Fin r → H} (c : Change p t t') (k) (j) :
    changeStage c k (root p t' k j) =
      algebraMap H _ (c.rootUnit (labelIndex p r k j) (labelOrder p r k j) : H) *
        root p t k j := stageLift_root ..

private def changeView {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    {t t' : Fin r → H} (c : Change p t t') (k : Option (TameRootOrder p)) (d q) :
    view p t' k d q →+* view p t k d q :=
  viewLift (changeStage c k)
    (boundary_preserved _ (RingHom.id H) c.unit (changeStage_coeff c k) c.equation
      (fun S j hj ↦ by
        rw [changeStage_root]
        apply Ideal.mul_mem_left
        exact Ideal.subset_span (by simp only [Set.mem_ofPred_eq]; exact ⟨j, hj, rfl⟩)))
    (puncture_unit _ (RingHom.id H) c.unit (changeStage_coeff c k) c.equation) d q

private theorem changeView_apply {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    {t t' : Fin r → H} (c : Change p t t') (k d q) (x) :
    changeView c k d q (viewMap p t' k d q x) = viewMap p t k d q (changeStage c k x) :=
  viewLift_apply ..

private theorem changeView_coeff {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    {t t' : Fin r → H} (c : Change p t t') (k d q) (a : H) :
    changeView c k d q (viewMap p t' k d q (algebraMap H _ a)) =
      viewMap p t k d q (algebraMap H _ a) := by
  rw [changeView_apply, changeStage_coeff]

private theorem changeView_root {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    {t t' : Fin r → H} (c : Change p t t') (k d q) (j) :
    changeView c k d q (viewMap p t' k d q (root p t' k j)) =
      viewMap p t k d q
        (algebraMap H _ (c.rootUnit (labelIndex p r k j) (labelOrder p r k j) : H) *
          root p t k j) := by rw [changeView_apply, changeStage_root]

private theorem changeView_inverse {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    {t t' : Fin r → H} (c : Change p t t') (k d q) :
    (changeView c k d q).comp (changeView (changeInverse c) k d q) = RingHom.id _ := by
  apply view_ext k d q
  · intro a
    simp only [RingHom.comp_apply, changeView_coeff, RingHom.id_apply]
  · intro j
    simp only [RingHom.comp_apply, changeView_root, map_mul, changeView_coeff,
      RingHom.id_apply]
    simp only [← map_mul, ← mul_assoc, ← map_mul]
    simp [changeInverse]

private def comparisonData {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    {t t' : Fin r → H} (c : Change p t t') : Comparison p c where
  equiv k d q := RingEquiv.ofRingHom (changeView c k d q)
    (changeView (changeInverse c) k d q) (changeView_inverse c k d q) (by
      convert changeView_inverse (changeInverse c) k d q using 1
      rfl)
  coeff := changeView_coeff c
  root := changeView_root c
  descend k d q x := by
    change changeView c k d q (viewMap p t' k d q x) = _
    rw [changeView_apply]
    rfl

private def powerStage {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n m : TameRootOrder p) (h : n.val ∣ m.val) :
    stage p t (some n) →+* stage p t (some m) :=
  stageLift t (some n) (algebraMap H _)
    (fun i ↦ root p t (some m) i ^ (m.val / n.val))
    (fun i ↦ by
      dsimp only [labelOrder, labelIndex]
      rw [← pow_mul, Nat.div_mul_cancel h]
      exact root_pow t (some m) i)
    (fun _ _ _ _ e ↦ by cases e)

private theorem powerStage_coeff {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n m : TameRootOrder p) (h) (a : H) :
    powerStage t n m h (algebraMap H _ a) = algebraMap H _ a := stageLift_coeff ..

private theorem powerStage_root {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n m : TameRootOrder p) (h) (i) :
    powerStage t n m h (root p t (some n) i) =
      root p t (some m) i ^ (m.val / n.val) := stageLift_root ..

private def inclusionStage {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n : TameRootOrder p) : stage p t (some n) →+* stage p t none :=
  stageLift t (some n) (algebraMap H _) (fun i ↦ root p t none (i, n))
    (fun i ↦ root_pow t none (i, n)) (fun _ _ _ _ e ↦ by cases e)

private theorem inclusionStage_coeff {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n : TameRootOrder p) (a : H) :
    inclusionStage t n (algebraMap H _ a) = algebraMap H _ a := stageLift_coeff ..

private theorem inclusionStage_root {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n : TameRootOrder p) (i) :
    inclusionStage t n (root p t (some n) i) = root p t none (i, n) := stageLift_root ..

private def powerView {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n m : TameRootOrder p) (h : n.val ∣ m.val) (d q) :
    view p t (some n) d q →+* view p t (some m) d q :=
  viewLift (powerStage t n m h)
    (boundary_preserved _ (RingHom.id H) (fun _ ↦ 1) (powerStage_coeff t n m h)
      (fun _ ↦ (one_mul _).symm) (fun S i hi ↦ by
        rw [powerStage_root]
        apply Ideal.pow_mem_of_mem
        · exact Ideal.subset_span (by simp only [Set.mem_ofPred_eq]; exact ⟨i, hi, rfl⟩)
        · exact Nat.div_pos (Nat.le_of_dvd m.prop.1 h) n.prop.1))
    (puncture_unit _ (RingHom.id H) (fun _ ↦ 1) (powerStage_coeff t n m h)
      (fun _ ↦ (one_mul _).symm)) d q

private theorem powerView_apply {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n m : TameRootOrder p) (h) (d q) (x) :
    powerView t n m h d q (viewMap p t (some n) d q x) =
      viewMap p t (some m) d q (powerStage t n m h x) := viewLift_apply ..

private theorem powerView_coeff {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n m : TameRootOrder p) (h) (d q) (a : H) :
    powerView t n m h d q (viewMap p t (some n) d q (algebraMap H _ a)) =
      viewMap p t (some m) d q (algebraMap H _ a) := by
  rw [powerView_apply, powerStage_coeff]

private theorem powerView_root {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n m : TameRootOrder p) (h) (d q) (i) :
    powerView t n m h d q (viewMap p t (some n) d q (root p t (some n) i)) =
      viewMap p t (some m) d q (root p t (some m) i) ^ (m.val / n.val) := by
  rw [powerView_apply, powerStage_root, map_pow]

private def inclusionView {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n : TameRootOrder p) (d q) :
    view p t (some n) d q →+* view p t none d q :=
  viewLift (inclusionStage t n)
    (boundary_preserved _ (RingHom.id H) (fun _ ↦ 1) (inclusionStage_coeff t n)
      (fun _ ↦ (one_mul _).symm) (fun S i hi ↦ by
        rw [inclusionStage_root]
        exact Ideal.subset_span (by simp only [Set.mem_ofPred_eq]; exact ⟨(i, n), hi, rfl⟩)))
    (puncture_unit _ (RingHom.id H) (fun _ ↦ 1) (inclusionStage_coeff t n)
      (fun _ ↦ (one_mul _).symm)) d q

private theorem inclusionView_apply {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n : TameRootOrder p) (d q) (x) :
    inclusionView t n d q (viewMap p t (some n) d q x) =
      viewMap p t none d q (inclusionStage t n x) := viewLift_apply ..

private theorem inclusionView_coeff {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n : TameRootOrder p) (d q) (a : H) :
    inclusionView t n d q (viewMap p t (some n) d q (algebraMap H _ a)) =
      viewMap p t none d q (algebraMap H _ a) := by
  rw [inclusionView_apply, inclusionStage_coeff]

private theorem inclusionView_root {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (n : TameRootOrder p) (d q) (i) :
    inclusionView t n d q (viewMap p t (some n) d q (root p t (some n) i)) =
      viewMap p t none d q (root p t none (i, n)) := by
  rw [inclusionView_apply, inclusionStage_root]

private theorem exponent_comp {p : ℕ} (n m l : TameRootOrder p)
    (h₁ : n.val ∣ m.val) (h₂ : m.val ∣ l.val) :
    (l.val / m.val) * (m.val / n.val) = l.val / n.val := by
  apply Nat.eq_of_mul_eq_mul_right n.prop.1
  rw [mul_assoc, Nat.div_mul_cancel h₁, Nat.div_mul_cancel h₂,
    Nat.div_mul_cancel (dvd_trans h₁ h₂)]

private def towerMapsData {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) : TowerMaps p t where
  transition := powerView t
  inclusion := inclusionView t
  transition_coeff := powerView_coeff t
  transition_root := powerView_root t
  inclusion_coeff := inclusionView_coeff t
  inclusion_root := inclusionView_root t
  transition_id n d q := RingHom.congr_fun (show
      powerView t n n (dvd_refl _) d q = RingHom.id _ from by
    apply view_ext (some n) d q
    · intro a; exact powerView_coeff t n n (dvd_refl _) d q a
    · intro i
      rw [powerView_root t n n (dvd_refl _) d q i, Nat.div_self n.prop.1, pow_one]
      rfl)
  transition_comp n m l h₁ h₂ d q := RingHom.congr_fun (show
      (powerView t m l h₂ d q).comp (powerView t n m h₁ d q) =
        powerView t n l (dvd_trans h₁ h₂) d q from by
    apply view_ext (some n) d q
    · intro a
      change powerView t m l h₂ d q (powerView t n m h₁ d q
        (viewMap p t (some n) d q (algebraMap H _ a))) = _
      rw [powerView_coeff t n m h₁, powerView_coeff t m l h₂,
        powerView_coeff t n l (dvd_trans h₁ h₂)]
    · intro i
      change powerView t m l h₂ d q (powerView t n m h₁ d q
        (viewMap p t (some n) d q (root p t (some n) i))) = _
      rw [powerView_root t n m h₁, map_pow, powerView_root t m l h₂,
        powerView_root t n l (dvd_trans h₁ h₂), ← pow_mul, exponent_comp n m l h₁ h₂])
  inclusion_compatible n m h d q := RingHom.congr_fun (show
      (inclusionView t m d q).comp (powerView t n m h d q) =
        inclusionView t n d q from by
    apply view_ext (some n) d q
    · intro a
      change inclusionView t m d q (powerView t n m h d q
        (viewMap p t (some n) d q (algebraMap H _ a))) = _
      rw [powerView_coeff t n m h, inclusionView_coeff t m, inclusionView_coeff t n]
    · intro i
      change inclusionView t m d q (powerView t n m h d q
        (viewMap p t (some n) d q (root p t (some n) i))) = _
      rw [powerView_root t n m h, map_pow, inclusionView_root t m,
        inclusionView_root t n, ← map_pow, root_coherent t i n m h])

private theorem cocone_root_coherent {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (s : Cocone (towerMapsData (p := p) t).diagram)
    (i : Fin r) (n m : TameRootOrder p) (h : n.val ∣ m.val) :
    (s.ι.app m).hom (root p t (some m) i) ^ (m.val / n.val) =
      (s.ι.app n).hom (root p t (some n) i) := by
  have hn := congrArg (fun f ↦ (f : _ ⟶ s.pt).hom (root p t (some n) i))
    (s.w (show n ⟶ m from ⟨h⟩))
  change (s.ι.app m).hom (powerView t n m h none false (root p t (some n) i)) = _ at hn
  rw [show root p t (some n) i =
    viewMap p t (some n) none false (root p t (some n) i) from rfl,
    powerView_root t n m h, map_pow] at hn
  exact hn

private def colimitDesc {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) (s : Cocone (towerMapsData (p := p) t).diagram) : stage p t none →+* s.pt :=
  stageLift t none (algebraMap H s.pt)
    (fun j ↦ (s.ι.app j.2).hom (root p t (some j.2) j.1))
    (fun j ↦ by
      change (s.ι.app j.2).hom (root p t (some j.2) j.1) ^ j.2.val = _
      have hj := root_pow t (some j.2) j.1
      dsimp only [labelOrder, labelIndex, id_eq] at hj
      rw [← map_pow, hj]
      exact (s.ι.app j.2).hom.commutes (t j.1))
    (fun i n m h _ ↦ cocone_root_coherent t s i n m h)

private def tower_isColimit {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) : IsColimit (towerMapsData (p := p) t).cocone where
  desc s := CommAlgCat.ofHom
    { colimitDesc t s with commutes' := fun a ↦ stageLift_coeff _ _ _ _ _ _ a }
  fac s n := by
    apply CommAlgCat.hom_ext
    apply AlgHom.coe_ringHom_injective
    apply stage_ext (some n)
    · intro a
      change colimitDesc t s (inclusionView t n none false (algebraMap H _ a)) = _
      rw [show algebraMap H (stage p t (some n)) a =
        viewMap p t (some n) none false (algebraMap H _ a) from rfl,
        inclusionView_coeff t n]
      exact (stageLift_coeff ..).trans ((s.ι.app n).hom.commutes a).symm
    · intro i
      change colimitDesc t s (inclusionView t n none false (root p t (some n) i)) = _
      rw [show root p t (some n) i =
        viewMap p t (some n) none false (root p t (some n) i) from rfl,
        inclusionView_root t n]
      exact stageLift_root ..
  uniq s m hm := by
    apply CommAlgCat.hom_ext
    apply AlgHom.coe_ringHom_injective
    apply stage_ext none
    · intro a
      change m.hom (algebraMap H _ a) = colimitDesc t s (algebraMap H _ a)
      rw [m.hom.commutes]
      exact (stageLift_coeff t none _ _ _ _ a).symm
    · intro j
      have hn := congrArg (fun f ↦ (f : _ ⟶ s.pt).hom (root p t (some j.2) j.1)) (hm j.2)
      change m.hom (inclusionView t j.2 none false (root p t (some j.2) j.1)) = _ at hn
      rw [show root p t (some j.2) j.1 =
        viewMap p t (some j.2) none false (root p t (some j.2) j.1) from rfl,
        inclusionView_root t j.2] at hn
      change m.hom (root p t none j) = colimitDesc t s (root p t none j)
      change m.hom (root p t none j) =
        (s.ι.app j.2).hom (root p t (some j.2) j.1) at hn
      dsimp only [colimitDesc]
      rw [stageLift_root]
      exact hn

private def towerData {p : ℕ} {H : Type u} [CommRing H] {r : ℕ}
    (t : Fin r → H) : Tower p t where
  toTowerMaps := towerMapsData t
  isColimit := tower_isColimit t

private theorem rank_zero_stage {p : ℕ} {H : Type u} [CommRing H]
    (t : Fin 0 → H) (k : Option (TameRootOrder p)) :
    Function.Surjective (algebraMap H (stage p t k)) := by
  cases k with
  | none =>
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction x using MvPolynomial.induction_on with
    | C a => exact ⟨a, rfl⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X x i _ => exact Fin.elim0 i.1
  | some n =>
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction x using MvPolynomial.induction_on with
    | C a => exact ⟨a, rfl⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X x i _ => exact Fin.elim0 i

private theorem rank_zero_reduced {p : ℕ} {H : Type u} [CommRing H]
    (t : Fin 0 → H) (k : Option (TameRootOrder p)) (d) :
    Function.Surjective ((reductionMap p t k d).comp (algebraMap H _)) := by
  cases d with
  | none => exact rank_zero_stage t k
  | some d => exact Ideal.Quotient.mk_surjective.comp (rank_zero_stage t k)

private theorem rank_zero_view {p : ℕ} {H : Type u} [CommRing H]
    (t : Fin 0 → H) (k : Option (TameRootOrder p)) (d q) :
    Function.Surjective ((viewMap p t k d q).comp (algebraMap H _)) := by
  cases q with
  | false => exact rank_zero_reduced t k d
  | true =>
    change Function.Surjective ((algebraMap (reduced p t k d) (view p t k d true)) ∘
      ((reductionMap p t k d).comp (algebraMap H _)))
    apply Function.Surjective.comp _ (rank_zero_reduced t k d)
    apply IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
      (reductionMap p t k d (algebraMap H _ (∏ i, t i)))
    simp only [Fin.prod_univ_zero, map_one]
    exact one_mul 1

private theorem coefficientView_coeff {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} (t : Fin r → H) (s : Fin r → K) (h : H →+* K) (ht) (k d q) (a : H) :
    coefficientView t s h ht k d q (viewMap p t k d q (algebraMap H _ a)) =
      viewMap p s k d q (algebraMap K _ (h a)) := by
  rw [coefficientView_apply, coefficientStage_coeff]

private theorem coefficientView_root {p : ℕ} {H K : Type u} [CommRing H] [CommRing K]
    {r : ℕ} (t : Fin r → H) (s : Fin r → K) (h : H →+* K) (ht) (k d q) (j) :
    coefficientView t s h ht k d q (viewMap p t k d q (root p t k j)) =
      viewMap p s k d q (root p s k j) := by
  rw [coefficientView_apply, coefficientStage_root]

/-- Compatible unit-root coordinate comparisons, simultaneously at finite, residual, full,
and punctured levels, natural in coefficient data and satisfying normalized cocycles.
Source: ILO IX Proposition 2.1, p.133; the eight explicit DAG substitution steps
(blueprint: lem-sfb-unit-root-coordinate-tower-comparison).

Proof:
1. Evaluate primed polynomials at b_(i,n) x_(i,n). The relation maps to
   b_(i,n)^n t_i-t'_i=0. Descend through the ideal using the quotient universal
   property. Evaluation at inverse units gives the inverse. Both composites fix
   coefficients and variables; polynomial uniqueness and quotient surjectivity apply.
2. For n dividing m the two substitutions on a root differ only by
   b_(i,n)=b_(i,m)^(m/n). This proves commutation with every power transition.
3. The full compatible-root quotient is the colimit: a cocone evaluates each labelled
   root by its finite-stage map, and cocone compatibility kills all power relations.
   Polynomial uniqueness proves the universal property. Substitute directly in this
   quotient, with the coherence of the units preserving its compatibility relations.
4. The primed boundary product is A times the original one, A the product of the units.
   Localization universality extends the comparison by z/(f')^k -> phi(z) A^(-k)/f^k.
   The inverse substitution extends too; uniqueness proves the inverse and tower laws.
5. Multiplication by units preserves the root-coordinate ideals, coefficient-equation
   ideals, and principal ideals of their products. Descend to these quotients and then
   localize. This includes a zero localization. All quotient/localization squares commute.
6. A coefficient homomorphism preserving the given units and their specified roots
   commutes with substitution on each coefficient and variable. Quotient surjectivity,
   colimit uniqueness and localization uniqueness give naturality on every view.
7. Normalize a finite family against one reference tuple. The ratio roots b_a/b_b
   multiply to b_a/b_c and have the required powers and coherence. Substitution uniqueness
   gives the identity and cocycle on every finite, residual, full and punctured view.
   The final two clauses below express these laws for any coherent pair/triple of ratios,
   thus in particular for every finite family normalized in the prescribed way.
8. With no parameters, coefficients surject onto every stage and boundary quotient;
   the puncture is localization at one, whose coefficient map is also surjective.
   Thus every comparison fixes the coefficient represented by each element, even when
   the empty product boundary ideal makes the quotient the zero ring.
   At order one the specified unit root equals the unit and the variable equals t_i;
   hence the comparison is substitution of the original equation, fixing coefficients.
-/
theorem unitRoot_coordinate_tower_comparison (p : ℕ) (hp : p.Prime) (r : ℕ) :
    ∃ (T : ∀ (H : Type u) [CommRing H] [CharP H p] (t : Fin r → H), Tower p t)
      (E : ∀ (H : Type u) [CommRing H] [CharP H p] (t t' : Fin r → H)
        (c : Change p t t'), Comparison p c)
      (F : ∀ (H K : Type u) [CommRing H] [CommRing K] [CharP H p] [CharP K p]
        (t : Fin r → H) (s : Fin r → K) (h : H →+* K),
        (∀ i, h (t i) = s i) → CoefficientMap p t s h),
      (∀ (H : Type u) [CommRing H] [CharP H p] (t t' : Fin r → H)
          (c : Change p t t') (n m : TameRootOrder p) (h : n.val ∣ m.val) d q,
        ((E H t t' c).equiv (some m) d q).toRingHom.comp
            ((T H t').transition n m h d q) =
          ((T H t).transition n m h d q).comp
            ((E H t t' c).equiv (some n) d q).toRingHom) ∧
      (∀ (H : Type u) [CommRing H] [CharP H p] (t t' : Fin r → H)
          (c : Change p t t') n d q,
        ((E H t t' c).equiv none d q).toRingHom.comp ((T H t').inclusion n d q) =
          ((T H t).inclusion n d q).comp
            ((E H t t' c).equiv (some n) d q).toRingHom) ∧
      (∀ (H K : Type u) [CommRing H] [CommRing K] [CharP H p] [CharP K p]
          (t t' : Fin r → H) (s s' : Fin r → K) (c : Change p t t')
          (c' : Change p s s') (h : H →+* K)
          (ht : ∀ i, h (t i) = s i) (ht' : ∀ i, h (t' i) = s' i),
        (∀ i, h (c.unit i : H) = (c'.unit i : K)) →
        (∀ i n, h (c.rootUnit i n : H) = (c'.rootUnit i n : K)) →
        ∀ k d q, ((F H K t s h ht).map k d q).comp
            ((E H t t' c).equiv k d q).toRingHom =
          ((E K s s' c').equiv k d q).toRingHom.comp ((F H K t' s' h ht').map k d q)) ∧
      (∀ (H : Type u) [CommRing H] [CharP H p] (t : Fin r → H) (c : Change p t t),
        (∀ i n, c.rootUnit i n = 1) →
        ∀ k d q, (E H t t c).equiv k d q = RingEquiv.refl _) ∧
      (∀ (H : Type u) [CommRing H] [CharP H p] (t₀ t₁ t₂ : Fin r → H)
          (c₀₁ : Change p t₁ t₀) (c₁₂ : Change p t₂ t₁) (c₀₂ : Change p t₂ t₀),
        (∀ i n, c₀₁.rootUnit i n * c₁₂.rootUnit i n = c₀₂.rootUnit i n) →
        ∀ k d q, ((E H t₁ t₀ c₀₁).equiv k d q).trans
            ((E H t₂ t₁ c₁₂).equiv k d q) = (E H t₂ t₀ c₀₂).equiv k d q) ∧
      (∀ (H : Type u) [CommRing H] [CharP H p] (t t' : Fin r → H)
          (c : Change p t t'), r = 0 →
        ∀ k d q x, ∃ a : H,
          viewMap p t' k d q (algebraMap H _ a) = x ∧
          (E H t t' c).equiv k d q x = viewMap p t k d q (algebraMap H _ a)) ∧
      (∀ (H : Type u) [CommRing H] [CharP H p] (t t' : Fin r → H)
          (c : Change p t t') (n : TameRootOrder p), n.val = 1 →
        ∀ i, (E H t t' c).equiv (some n) none false (root p t' (some n) i) =
          algebraMap H _ (t' i)) := by
  have _ := hp
  refine ⟨(fun H _ _ t ↦ towerData (p := p) t),
    (fun H _ _ t t' c ↦ comparisonData c),
    (fun H K _ _ _ _ t s h ht ↦ coefficientData t s h ht), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro H _ _ t t' c n m h d q
    change (changeView c (some m) d q).comp (powerView t' n m h d q) =
      (powerView t n m h d q).comp (changeView c (some n) d q)
    apply view_ext (some n) d q
    · intro a
      change changeView c (some m) d q (powerView t' n m h d q
        (viewMap p t' (some n) d q (algebraMap H _ a))) = _
      rw [powerView_coeff t' n m h, changeView_coeff]
      exact (by rw [RingHom.comp_apply, changeView_coeff, powerView_coeff t n m h])
    · intro i
      change changeView c (some m) d q (powerView t' n m h d q
        (viewMap p t' (some n) d q (root p t' (some n) i))) = _
      rw [powerView_root t' n m h, map_pow, changeView_root]
      simp only [labelIndex, labelOrder, map_mul, mul_pow, ← map_pow]
      rw [RingHom.comp_apply, changeView_root, map_mul, map_mul, powerView_coeff t n m h,
        powerView_root t n m h]
      have hc := congrArg (fun z : Hˣ ↦ (z : H)) (c.coherent i n m h)
      simp only [Units.val_pow_eq_pow_val] at hc
      simp only [labelIndex, labelOrder, id_eq, hc, map_pow]
  · intro H _ _ t t' c n d q
    change (changeView c none d q).comp (inclusionView t' n d q) =
      (inclusionView t n d q).comp (changeView c (some n) d q)
    apply view_ext (some n) d q
    · intro a
      change changeView c none d q (inclusionView t' n d q
        (viewMap p t' (some n) d q (algebraMap H _ a))) = _
      rw [inclusionView_coeff t' n, changeView_coeff]
      rw [RingHom.comp_apply, changeView_coeff, inclusionView_coeff t n]
    · intro i
      change changeView c none d q (inclusionView t' n d q
        (viewMap p t' (some n) d q (root p t' (some n) i))) = _
      rw [inclusionView_root t' n, changeView_root, RingHom.comp_apply, changeView_root]
      simp only [labelIndex, labelOrder, map_mul]
      rw [inclusionView_coeff t n, inclusionView_root t n]
      rfl
  · intro H K _ _ _ _ t t' s s' c c' h ht ht' _hunit hroot k d q
    change (coefficientView t s h ht k d q).comp (changeView c k d q) =
      (changeView c' k d q).comp (coefficientView t' s' h ht' k d q)
    apply view_ext k d q
    · intro a
      simp only [RingHom.comp_apply, changeView_coeff, coefficientView_coeff]
    · intro j
      simp only [RingHom.comp_apply, changeView_root, coefficientView_root, map_mul,
        coefficientView_coeff, hroot]
  · intro H _ _ t c hc k d q
    apply RingEquiv.toRingHom_injective
    change changeView c k d q = RingHom.id _
    apply view_ext k d q
    · intro a; exact changeView_coeff c k d q a
    · intro j
      rw [changeView_root, hc]
      simp
  · intro H _ _ t₀ t₁ t₂ c₀₁ c₁₂ c₀₂ hc k d q
    apply RingEquiv.toRingHom_injective
    change (changeView c₁₂ k d q).comp (changeView c₀₁ k d q) = changeView c₀₂ k d q
    apply view_ext k d q
    · intro a
      simp only [RingHom.comp_apply, changeView_coeff]
    · intro j
      simp only [RingHom.comp_apply, changeView_root, map_mul, changeView_coeff]
      have hcoeff := congrArg
        (fun z : Hˣ ↦ viewMap p t₂ k d q (algebraMap H _ (z : H)))
        (hc (labelIndex p r k j) (labelOrder p r k j))
      simp only [Units.val_mul, map_mul] at hcoeff
      rw [← mul_assoc, hcoeff]
  · intro H _ _ t t' c hr k d q x
    subst r
    obtain ⟨a, ha⟩ := rank_zero_view t' k d q x
    refine ⟨a, ha, ?_⟩
    rw [← ha]
    exact changeView_coeff c k d q a
  · intro H _ _ t t' c n hn i
    change changeStage c (some n) (root p t' (some n) i) = _
    rw [changeStage_root]
    change algebraMap H _ (c.rootUnit i n : H) * root p t (some n) i = _
    have hu := congrArg (fun z : Hˣ ↦ (z : H)) (c.power i n)
    simp only [hn, pow_one] at hu
    have hx := root_pow t (some n) i
    change root p t (some n) i ^ n.val = _ at hx
    have hexp := congrArg (fun e : ℕ ↦ root p t (some n) i ^ e) hn
    rw [pow_one] at hexp
    have hx' := hexp.symm.trans hx
    dsimp only [labelIndex, id_eq] at hx'
    clear hx
    rw [hu, hx', ← map_mul, ← c.equation]

end AlgebraicGeometry.ProEtale.UnitRootCoordinates
