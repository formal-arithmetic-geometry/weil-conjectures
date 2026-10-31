/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.LocalFrobeniusTrace
import WeilConjectures.Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.AlgebraicGeometry.CondensedModuleTransportComposition

/-! # Change of geometric lift for a condensed module return

Source: the finite-orbit and transport steps of the condensed local-power argument.
(blueprint: lem-wf-condensed-module-lift-conjugacy).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedModule

private theorem factor_field_point {K : Type u} [Field K] {X : Scheme.{u}}
    (z : Spec (.of K) ⟶ X) (y : X)
    (hy : z (IsLocalRing.closedPoint K) = y) :
    ∃ i : X.residueField y →+* K,
      Spec.map (CommRingCat.ofHom i) ≫ X.fromSpecResidueField y = z := by
  obtain ⟨⟨p, i⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective z
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply] at hy
  subst p
  exact ⟨i.hom, rfl⟩

private theorem factor_geometric_lift (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (hy : (z ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (IsLocalRing.closedPoint D.k) = y.val) :
    ∃ i : Y₀.left.residueField y.val →+* D.k,
      ∃ hi : i.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k,
        z = localClosedPoint D Y₀ y i hi := by
  obtain ⟨i, hi⟩ := factor_field_point _ y.val hy
  have hb : (Spec.map (CommRingCat.ofHom i) ≫ Y₀.left.fromSpecResidueField y.val) ≫
      Y₀.hom = Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
    rw [hi, Category.assoc, pullback.condition]
    change z ≫ (D.geometricFiber Y₀).hom ≫ _ = _
    rw [← Category.assoc, hz, Category.id_comp]
  rw [Category.assoc, ← Y₀.hom.specMap_residueFieldAlgebraMap,
    ← Spec.map_comp, Spec.map_inj] at hb
  have hic : i.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k :=
    congrArg (fun f : CommRingCat.of D.k₀ ⟶ CommRingCat.of D.k ↦ f.hom) hb
  refine ⟨i, hic, ?_⟩
  apply pullback.hom_ext
  · simpa only [localClosedPoint, pullback.lift_fst] using hi.symm
  · simpa [localClosedPoint, FiniteFieldDatum.geometricFiber] using hz

private theorem point_power_eq (D : FiniteFieldDatum.{u}) (n : ℕ) :
    localPositivePower (frobeniusPointIso D).hom n =
      let := Fintype.ofFinite D.k₀
      Spec.map (CommRingCat.ofHom
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ (n + 1)).toRingHom) := by
  let := Fintype.ofFinite D.k₀
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [localPositivePower, ih]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1

private theorem frobenius_projections (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (n : ℕ) :
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        localPositivePower (frobeniusPointIso D).hom n := by
  let := Fintype.ofFinite D.k₀
  have h := D.galoisMap_projections Y₀.hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
  change (D.geometricFrobenius Y₀).hom ≫ _ = _ ∧
    (D.geometricFrobenius Y₀).hom ≫ _ = _ ≫ (frobeniusPointIso D).hom at h
  induction n with
  | zero => exact h
  | succ n ih =>
    constructor
    · rw [localPositivePower, Category.assoc, h.1]
      exact ih.1
    · rw [localPositivePower, Category.assoc, h.2, ← Category.assoc, ih.2, Category.assoc]
      rfl

private theorem geometric_lifts_orbit (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (z z' : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (hz' : z' ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (hy : (z ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (IsLocalRing.closedPoint D.k) = y.val)
    (hy' : (z' ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (IsLocalRing.closedPoint D.k) = y.val) :
    ∃ r : ℕ, 1 ≤ r ∧
      z' ≫ localPositivePower (D.geometricFrobenius Y₀).hom (r - 1) =
        localPositivePower (frobeniusPointIso D).hom (r - 1) ≫ z := by
  let := Fintype.ofFinite D.k₀
  obtain ⟨i, hi, rfl⟩ := factor_geometric_lift D Y₀ y z hz hy
  obtain ⟨j, hj, rfl⟩ := factor_geometric_lift D Y₀ y z' hz' hy'
  let := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
  have : Module.Finite D.k₀ (Y₀.left.residueField y.val) :=
    (closedPoint_iff_residueField_trdeg_zero_and_finite Y₀.hom y.val).2.1.mp y.property
  have : Finite (Y₀.left.residueField y.val) := Module.finite_of_finite D.k₀
  have hc : Nat.card (Y₀.left.residueField y.val) =
      Fintype.card D.k₀ ^ localClosedPointDegree D Y₀ y := by
    simpa only [Nat.card_eq_fintype_card, localClosedPointDegree] using
      (Module.natCard_eq_pow_finrank (K := D.k₀) (V := Y₀.left.residueField y.val))
  obtain ⟨n, hn⟩ := FiniteField.exists_apply_eq_pow_card_pow_of_comp_eq
    (Y₀.hom.residueFieldAlgebraMap y.val) (hi.trans hj.symm)
  obtain ⟨r, hr, he⟩ := FiniteField.exists_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_eq
    D.k₀ D.k (localClosedPointDegree_pos D Y₀ y) hc i n
  refine ⟨r, hr, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, (frobenius_projections D Y₀ (r - 1)).1]
    simp only [localClosedPoint, pullback.lift_fst, Category.assoc]
    rw [← Category.assoc, point_power_eq, Nat.sub_add_cancel hr, ← Spec.map_comp]
    congr 2
    ext a
    exact (hn a).trans (he a).symm
  · rw [Category.assoc, (frobenius_projections D Y₀ (r - 1)).2]
    simp only [localClosedPoint, Category.assoc, pullback.lift_snd_assoc,
      pullback.lift_snd, Category.comp_id, Category.id_comp]

private theorem positivePower_add {Y : Scheme.{u}} (a : Y ⟶ Y) (n m : ℕ) :
    localPositivePower a (n + m + 1) = localPositivePower a n ≫ localPositivePower a m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change localPositivePower a (n + m + 1) ≫ a =
      localPositivePower a n ≫ (localPositivePower a m ≫ a)
    rw [ih, Category.assoc]

private theorem compose_square {Y S : Scheme.{u}} (a : Y ⟶ Y) (σ : S ⟶ S)
    (z₀ z₁ z₂ : S ⟶ Y) (n m : ℕ)
    (h₁ : z₀ ≫ localPositivePower a n = localPositivePower σ n ≫ z₁)
    (h₂ : z₁ ≫ localPositivePower a m = localPositivePower σ m ≫ z₂) :
    z₀ ≫ localPositivePower a (n + m + 1) =
      localPositivePower σ (n + m + 1) ≫ z₂ := by
  rw [positivePower_add, positivePower_add, ← Category.assoc, h₁, Category.assoc,
    h₂, ← Category.assoc]

private theorem hom_intertwine {C : Type*} [Category C] {X Y : C}
    (A : X ≅ X) (B : Y ≅ Y) (T R : X ≅ Y)
    (h₁ : A ≪≫ T = R) (h₂ : R = T ≪≫ B) :
    A.hom ≫ T.hom = T.hom ≫ B.hom := by
  simpa only [Iso.trans_hom] using congrArg Iso.hom (h₁.trans h₂)

/-- Returns with the same exponent at two lifts of one closed point are intertwined.
Source: local Frobenius powers, proof steps 1--4; latest blueprint
`lem-wf-l2-upper.proof.md`, opening sentence.

Proof: the residue field is finite. The two lifts correspond to embeddings of that
field into the fixed closure. Finite-field Galois theory puts them in one Frobenius
orbit. Transport along an orbit segment by the iterated Weil map and the canonical
point reparametrization gives an isomorphism of their actual fibres. Apply the fibre
comparison composition, mixed, and naturality identities in the two orders to the
segment followed by the `n`-return and the `n`-return followed by the segment.
The equality of the two concatenated words is precisely the intertwining equation.
This argument does not identify a return with a power; both returns here have exponent
`n`, and it works also for the zero module.
(blueprint: lem-wf-condensed-module-lift-conjugacy). -/
theorem lift_conjugacy (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (z z' : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (hz' : z' ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (hy : (z ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (IsLocalRing.closedPoint D.k) = y.val)
    (hy' : (z' ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (IsLocalRing.closedPoint D.k) = y.val)
    (M : Modules l (D.geometricFiber Y₀).left)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom).obj M ≅ M)
    (n : ℕ) (_hn : 1 ≤ n)
    (h : z ≫ localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
      localPositivePower (frobeniusPointIso D).hom (n - 1) ≫ z)
    (h' : z' ≫ localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
      localPositivePower (frobeniusPointIso D).hom (n - 1) ≫ z') :
    ∃ T : fibre l D M z ≅ fibre l D M z',
      operator l D (D.geometricFrobenius Y₀).hom M θ z (n - 1) h ≫ T.hom =
        T.hom ≫ operator l D (D.geometricFrobenius Y₀).hom M θ z' (n - 1) h' := by
  obtain ⟨r, hr, hs⟩ := geometric_lifts_orbit D Y₀ y z z' hz hz' hy hy'
  let T := transport l D (D.geometricFrobenius Y₀).hom M θ z' z (r - 1) hs
  refine ⟨T, ?_⟩
  have hs₁ := compose_square (D.geometricFrobenius Y₀).hom (frobeniusPointIso D).hom
    z' z z (r - 1) (n - 1) hs h
  have hs₂ := compose_square (D.geometricFrobenius Y₀).hom (frobeniusPointIso D).hom
    z' z' z (n - 1) (r - 1) h' hs
  have hc₁ := transport_comp D l (D.geometricFrobenius Y₀).hom M θ
    z' z z (r - 1) (n - 1) hs h hs₁
  have hc₂ := transport_comp D l (D.geometricFrobenius Y₀).hom M θ
    z' z' z (n - 1) (r - 1) h' hs hs₂
  have he : (r - 1) + (n - 1) + 1 = (n - 1) + (r - 1) + 1 := by omega
  have hc₂' : transport l D (D.geometricFrobenius Y₀).hom M θ z' z
      ((r - 1) + (n - 1) + 1) hs₁ =
      T ≪≫ transport l D (D.geometricFrobenius Y₀).hom M θ z' z' (n - 1) h' := by
    simpa only [he, T] using hc₂.symm
  exact hom_intertwine
    (transport l D (D.geometricFrobenius Y₀).hom M θ z z (n - 1) h)
    (transport l D (D.geometricFrobenius Y₀).hom M θ z' z' (n - 1) h') T _ hc₁ hc₂'

end WeilConjectures.CondensedModule
