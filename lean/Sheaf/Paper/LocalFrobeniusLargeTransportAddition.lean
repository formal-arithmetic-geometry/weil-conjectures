/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.LocalFrobeniusLargeCoefficients
import Sheaf.Paper.LocalFrobeniusLargeTransportNaturality
import Sheaf.Paper.LocalFrobeniusLargeCompositionAssociativity

/-! # Addition of positive point transports

Source: Bhatt--Scholze, Remark 6.8.15; the restriction-and-coprojection
calculation for the constant-extension clause of local Frobenius comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.commonStageDerivedPullback
  WeilConjectures.LocalFrobeniusLarge.composition
  WeilConjectures.LocalFrobeniusLarge.pointFibre
  WeilConjectures.LocalFrobeniusLarge.transportIterate
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.LocalFrobeniusLarge

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

private theorem power_add {X : Scheme.{u}} (g : X ⟶ X) (a b : ℕ) :
    localPositivePower g b ≫ localPositivePower g a =
      localPositivePower g (a + b + 1) := by
  induction a with
  | zero => simp [localPositivePower]
  | succ a ih =>
    simp only [localPositivePower, ← Category.assoc, ih, Nat.succ_add]

private theorem map_heq {C T : Type*} [Category* C] [Category* T]
    (F : C ⥤ T) {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst A'
  subst B'
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

/-- Concatenating positive transports gives the transport of the sum, with the actual
pullback compositor at the endpoint. Both indices denote one more step than their value.

Source: BS Remark 6.8.15; blueprint real-mixed-by-curves, paragraph 1,
constant-extension calculation, as expanded in the proof of transport_blocks
(blueprint: lem-zl-large-transport-iterate-addition).

Proof: induct on a, simultaneously for every point object N. For a = 0 the word
is the successor recursion for transportIterate. For a+1 expand the first
transport iterate into one step followed by its preceding iterate on the
one-step pullback of N. Apply the induction hypothesis there. Reassociate the
three pullbacks using the compositor associativity law; naturality of the point
transport moves the comparison between its two successive pulled-back objects.
The result is the successor recursion for a+b+3 steps. These laws hold for the
specified maps: before rationalization each transport is restriction followed by
the inverse-image coprojection. Restriction is functorial and the coprojection
relation identifies the two successive restrictions with their composite. On a
single flat resolution the completed comparison is the same quotient map in
both words, with zero shifted-product coordinate in the Roos cone. Thus the
law holds in the derived category, rather than just after residue projections.
The integral compositor associativity passes through rationalization and stage
inclusion. The normalized coefficient comparisons commute with restriction and
coprojection, so they cancel when enlarging a representative coefficient field.
Apply H⁰ and extend scalars to Ω to get the displayed equality. -/
theorem transportIterate_add
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) (a b : ℕ) :
    letI := frobeniusPointPrimeInvertible D l hl
    HEq
      (transportIterate D l hl Ω N a ≫
        transportIterate D l hl Ω
          ((commonStageDerivedPullback l Ω
            (localPositivePower (frobeniusPointIso D).hom a)).obj N) b ≫
        (pointFibre D l hl Ω).map
          (composition l Ω (localPositivePower (frobeniusPointIso D).hom b)
            (localPositivePower (frobeniusPointIso D).hom a) N).inv)
      (transportIterate D l hl Ω N (a + b + 1)) := by
  let := frobeniusPointPrimeInvertible D l hl
  induction a generalizing N with
  | zero =>
    rw [Nat.zero_add]
    simp only [transportIterate, localPositivePower]
    rfl
  | succ a ih =>
    let g := (frobeniusPointIso D).hom
    let P (f : Spec (.of D.k) ⟶ Spec (.of D.k)) := commonStageDerivedPullback l Ω f
    let V := pointFibre D l hl Ω
    let M := (P g).obj N
    let c := composition l Ω (localPositivePower g a) g N
    have hn := transportIterate_naturality D l hl Ω c.inv b
    have ha := composition_inv_assoc l Ω
      (localPositivePower g b) (localPositivePower g a) g N
    have hi := ih M
    simp only [transportIterate, localPositivePower, Category.assoc]
    rw [reassoc_of% hn]
    rw [← V.map_comp]
    have he := map_heq V rfl
      (congrArg (fun f ↦ (P f).obj N) (Category.assoc
        (localPositivePower g b) (localPositivePower g a) g).symm) ha
    have he' := heq_comp rfl rfl
      (congrArg V.obj (congrArg (fun f ↦ (P f).obj N) (Category.assoc
        (localPositivePower g b) (localPositivePower g a) g).symm))
      (HEq.refl (transport D l hl Ω N ≫
        transportIterate D l hl Ω M a ≫
        transportIterate D l hl Ω ((P (localPositivePower g a)).obj M) b)) he
    simp only [Category.assoc, V.map_comp] at he'
    simp only [V.map_comp]
    apply he'.trans
    have hp := power_add g a b
    have hc := congr_arg_heq
      (fun f ↦ V.map (composition l Ω f g N).inv) hp
    have hh := heq_comp rfl
      (congrArg V.obj (congrArg (fun f ↦ (P f).obj M) hp))
      (congrArg V.obj (congrArg (fun f ↦ (P (f ≫ g)).obj N) hp)) hi hc
    have hh' := heq_comp rfl rfl
      (congrArg V.obj (congrArg (fun f ↦ (P (f ≫ g)).obj N) hp))
      (HEq.refl (transport D l hl Ω N)) hh
    have hr := congr_arg_heq
      (fun n ↦ transport D l hl Ω N ≫ transportIterate D l hl Ω M n ≫
        V.map (composition l Ω (localPositivePower g n) g N).inv)
      (Nat.add_right_comm a b 1)
    simpa only [Category.assoc] using hh'.trans hr

end WeilConjectures.LocalFrobeniusLarge
