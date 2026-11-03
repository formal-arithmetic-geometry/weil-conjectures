/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointTrivializationComposition
import WeilConjectures.CategoryTheory.PullbackFamily
import WeilConjectures.Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import WeilConjectures.PointCount

/-! # Change of lift for the actual condensed scalar fibre

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 3.
(blueprint: lem-zl-native-anchor-lift-conjugacy).
The proof reuses the coefficient-independent transport-composition and finite-orbit
arguments directly on NativeCondensedModule.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open WeilConjectures.NativeCondensedModule
local instance (D : WeilConjectures.FiniteFieldDatum.{u}) : IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.NativeCondensedModule

private theorem transport_raw_eq (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {Y : Scheme.{u}} (a : Y ⟶ Y) (M : Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z z' : Spec (.of D.k) ⟶ Y) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z') :
    transport l D a M θ z z' n h = (pointSections l D.k).mapIso
      (rawTransport
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
        (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
        (fun f ↦ CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) f)
        a (frobeniusPointIso D).hom M (iterate l a M θ) z z' n h) := by
  unfold transport rawTransport
  rw [CondensedRing.pointComparison_eq]

/-- The actual positive semilinear transports compose in their natural order.
Source: current blueprint coefficient pullback-composition paragraph, and local Frobenius
powers proof steps 2--3.

Proof: induction on the second word gives the concatenation formula for the iterated
Weil map. Its successor step is pullback associativity and naturality of the compositor.
The point comparison for a composite square is the two point comparisons in sequence:
expand its specified trivialization, apply its composition identity and pullback
associativity, and use naturality of the first trivialization. Naturality of the first
point comparison at the second Weil map then combines these two identities. Apply the
point-sections functor, which preserves composition. Equality casts in the two positive
power identities cancel; proof irrelevance identifies the return-equation proofs.
(blueprint: lem-zl-native-anchor-lift-conjugacy). -/
private theorem transport_comp (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {Y : Scheme.{u}} (a : Y ⟶ Y) (M : Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z₀ z₁ z₂ : Spec (.of D.k) ⟶ Y) (n m : ℕ)
    (h₁ : z₀ ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z₁)
    (h₂ : z₁ ≫ localPositivePower a m =
      localPositivePower (frobeniusPointIso D).hom m ≫ z₂)
    (h : z₀ ≫ localPositivePower a (n + m + 1) =
      localPositivePower (frobeniusPointIso D).hom (n + m + 1) ≫ z₂) :
    transport l D a M θ z₁ z₂ m h₂ ≪≫ transport l D a M θ z₀ z₁ n h₁ =
      transport l D a M θ z₀ z₂ (n + m + 1) h := by
  have hI := actual_iteration_add l a M θ n m
  have H := genericTransport_comp
    (E := fun T : Scheme.{u} ↦ CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T))
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
    (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
    (CondensedRing.pullback_assoc (Profinite.padicAlgClRingObj l))
    (fun f ↦ CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) f)
    (fun f g ↦ CondensedRing.trivialization_inv_iso_comp (Profinite.padicAlgClRingObj l) f g)
    a (frobeniusPointIso D).hom M (iterate l a M θ) z₀ z₁ z₂ n m h₁ h₂ h hI
  simp only [transport_raw_eq]
  exact mapped_comp (pointSections l D.k) _ _ _ H

end WeilConjectures.NativeCondensedModule

namespace WeilConjectures.NativeCondensedModule

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
    D.k₀ D.k (by
      let := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
      have := (closedPoint_iff_residueField_trdeg_zero_and_finite Y₀.hom y.val).2.1.mp y.prop
      exact Module.finrank_pos) hc i n
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

private theorem lift_positivePower_add {Y : Scheme.{u}} (a : Y ⟶ Y) (n m : ℕ) :
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
  rw [lift_positivePower_add, lift_positivePower_add, ← Category.assoc, h₁, Category.assoc,
    h₂, ← Category.assoc]

private theorem hom_intertwine {C : Type*} [Category C] {X Y : C}
    (A : X ≅ X) (B : Y ≅ Y) (T R : X ≅ Y)
    (h₁ : A ≪≫ T = R) (h₂ : R = T ≪≫ B) :
    A.hom ≫ T.hom = T.hom ≫ B.hom := by
  simpa only [Iso.trans_hom] using congrArg Iso.hom (h₁.trans h₂)

/-- Returns with the same exponent at two lifts of one closed point are intertwined.
Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 3,
and `def-weil-punctual-weights.md`, independence of the geometric lift.

Proof: the residue field is finite. The two lifts correspond to embeddings of that
field into the fixed closure. Finite-field Galois theory puts them in one Frobenius
orbit. Transport along an orbit segment by the iterated Weil map and the canonical
point reparametrization gives an isomorphism of their actual fibres. Apply the fibre
comparison composition, mixed, and naturality identities in the two orders to the
segment followed by the `n`-return and the `n`-return followed by the segment.
The equality of the two concatenated words is precisely the intertwining equation.
This argument does not identify a return with a power; both returns here have exponent
`n`, and it works also for the zero module.
(blueprint: lem-zl-native-anchor-lift-conjugacy). -/
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

end WeilConjectures.NativeCondensedModule
