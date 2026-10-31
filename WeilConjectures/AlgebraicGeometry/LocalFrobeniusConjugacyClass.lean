/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalFrobeniusTrace
import WeilConjectures.AlgebraicGeometry.LocalFrobeniusStepCompatibility
import WeilConjectures.Mathlib.FieldTheory.Finite.Basic

/-! # Independence of the local Frobenius operator from the embedding

Source: Weil conjectures blueprint, `sec-poincare-duality/sk-lem-finite`,
`lem-weil-local-frobenius-conjugacy-class.md`, order 2429
(blueprint: lem-weil-local-frobenius-conjugacy-class).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- Powers of geometric field Frobenius, with the k₀-compatibility retained. -/
private theorem embeddingPower_compatible (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀)))
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (γ : D.k ≃ₐ[D.k₀] D.k) (i : ℕ) :
    ((γ ^ i).toRingHom.comp ι).comp (Y₀.hom.residueFieldAlgebraMap y.val) =
      algebraMap D.k₀ D.k := by
  ext a
  change (γ ^ i) (ι ((Y₀.hom.residueFieldAlgebraMap y.val) a)) = _
  have ha := RingHom.congr_fun hι a
  change ι ((Y₀.hom.residueFieldAlgebraMap y.val) a) = _ at ha
  rw [ha]
  exact (γ ^ i).commutes a

/-- Contravariant Spec makes geometric powers into consecutive semilinear points. -/
private theorem embeddingPower_step (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (i : ℕ) :
    letI := Fintype.ofFinite D.k₀
    let γ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
    localClosedPoint D Y₀ y ((γ ^ (i + 1)).toRingHom.comp ι)
        (embeddingPower_compatible D Y₀ y ι hι γ (i + 1)) ≫
        (D.geometricFrobenius Y₀).hom =
      (frobeniusPointIso D).hom ≫
        localClosedPoint D Y₀ y ((γ ^ i).toRingHom.comp ι)
          (embeddingPower_compatible D Y₀ y ι hι γ i) := by
  let := Fintype.ofFinite D.k₀
  let γ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
  have hp := D.galoisMap_projections Y₀.hom γ
  change (D.geometricFrobenius Y₀).hom ≫ _ = _ ∧
    (D.geometricFrobenius Y₀).hom ≫ _ = _ ≫ (frobeniusPointIso D).hom at hp
  dsimp only
  apply pullback.hom_ext
  · rw [Category.assoc, hp.1]
    simp only [localClosedPoint, pullback.lift_fst, Category.assoc]
    rw [← Category.assoc]
    apply congrArg (fun f ↦ f ≫ Y₀.left.fromSpecResidueField y.val)
    change Spec.map _ = Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext a
    change (γ ^ (i + 1)) (ι a) = γ ((γ ^ i) (ι a))
    rw [pow_succ', AlgEquiv.mul_apply]
  · rw [Category.assoc, hp.2]
    simp only [localClosedPoint]
    rw [← Category.assoc, pullback.lift_snd, Category.id_comp,
      Category.assoc, pullback.lift_snd, Category.comp_id]

attribute [local irreducible] localPointComplex localClosedFrobenius
  localFrobeniusOperator localPointTransportIterate localWeilIterate pointRationalFibre

/-- For two compatible residue-field embeddings, the local Frobenius maps are conjugate.
Proof plan from the source: the residue field is a finite extension of `k₀`, so its two
`k₀`-embeddings differ by a power of geometric Frobenius.  Reparametrized geometric
points `zᵢ` therefore form a finite Frobenius orbit and satisfy the pointwise return
equations.  The point-fibre transport maps `τᵢ` are natural isomorphisms, and their
iterated composites `Qᵢ,ₙ` agree with the specified iterated transport by induction,
using pullback-composition coherence.  If `Aᵢ` is the transport followed by the Weil
structure, the corresponding cyclic products `Pᵢ,ₙ` agree with the local return
operators by a second induction using naturality.  At the orbit length, consecutive
cyclic products satisfy `Fᵢ Aᵢ = Aᵢ Fᵢ₊₁`; the product from the first embedding to the
second consequently gives an isomorphism intertwining the two operators.  Applying
the coefficient cohomology functor yields the displayed conjugacy, including zero
cohomology modules.
Source: Weil conjectures blueprint,
`sec-poincare-duality/sk-lem-finite/lem-weil-local-frobenius-conjugacy-class.md`,
order 2429 (blueprint: lem-weil-local-frobenius-conjugacy-class). -/
theorem localFrobeniusConjugacyClass (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (K : sfWeilComplex D c.l c.different Y₀ E.val)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι ι' : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (hι' : ι'.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (j : ℤ) :
    ∃ e :
      (DerivedCategory.coefficientFdCohomology E.val j).obj
        (localPointComplex c.l E.val D c.different Y₀ K
          (localClosedPoint D Y₀ y ι hι)) ≅
      (DerivedCategory.coefficientFdCohomology E.val j).obj
        (localPointComplex c.l E.val D c.different Y₀ K
          (localClosedPoint D Y₀ y ι' hι')),
      e.hom ≫ (localClosedFrobeniusCohomology c.l E.val D c.different Y₀ K y
        ι' hι' j) =
      (localClosedFrobeniusCohomology c.l E.val D c.different Y₀ K y
        ι hι j) ≫ e.hom := by
  let := Fintype.ofFinite D.k₀
  let γ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
  let emb (i : ℕ) := (γ ^ i).toRingHom.comp ι
  have hemb (i : ℕ) :
      (emb i).comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k :=
    embeddingPower_compatible D Y₀ y ι hι γ i
  let x (i : ℕ) := localClosedPoint D Y₀ y (emb i) (hemb i)
  let C (i : ℕ) := localPointComplex c.l E.val D c.different Y₀ K (x i)
  let F (i : ℕ) := localClosedFrobenius c.l E.val D c.different Y₀ K y (emb i) (hemb i)
  have hs (i : ℕ) : x (i + 1) ≫ (D.geometricFrobenius Y₀).hom =
      (frobeniusPointIso D).hom ≫ x i := embeddingPower_step D Y₀ y ι hι i
  have hchain (i : ℕ) : ∃ e : C 0 ≅ C i, e.hom ≫ F i = F 0 ≫ e.hom := by
    induction i with
    | zero =>
      refine ⟨Iso.refl _, ?_⟩
      change 𝟙 (C 0) ≫ F 0 = F 0 ≫ 𝟙 (C 0)
      rw [Category.id_comp, Category.comp_id]
    | succ i ih =>
      obtain ⟨e, he⟩ := ih
      let a := asIso (localFrobeniusStepTransport D c E Y₀ K (x (i + 1)) (x i) (hs i))
      have ha : a.hom ≫ F (i + 1) = F i ≫ a.hom := by
        simpa only [a, asIso_hom, F, localClosedFrobenius, x] using
          localFrobeniusStepCompatibility D c E Y₀ K (x (i + 1)) (x i) (hs i)
            (localClosedPointDegree D Y₀ y - 1)
            (localClosedPoint_return D Y₀ y (emb (i + 1)) (hemb (i + 1)))
            (localClosedPoint_return D Y₀ y (emb i) (hemb i))
      refine ⟨e ≪≫ a, ?_⟩
      change (e.hom ≫ a.hom) ≫ F (i + 1) = F 0 ≫ (e.hom ≫ a.hom)
      rw [Category.assoc, ha, ← Category.assoc, he, Category.assoc]
  let := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
  have := (closedPoint_iff_residueField_trdeg_zero_and_finite Y₀.hom y.val).2.1.mp y.prop
  have : Finite (Y₀.left.residueField y.val) := Module.finite_of_finite D.k₀
  obtain ⟨i, hi⟩ := FiniteField.exists_apply_eq_pow_card_pow_of_comp_eq
    (Y₀.hom.residueFieldAlgebraMap y.val) (hι.trans hι'.symm)
  have hc : Nat.card (Y₀.left.residueField y.val) =
      Fintype.card D.k₀ ^ localClosedPointDegree D Y₀ y := by
    simpa only [Nat.card_eq_fintype_card, localClosedPointDegree] using
      (Module.natCard_eq_pow_finrank (K := D.k₀) (V := Y₀.left.residueField y.val))
  obtain ⟨t, _, ht⟩ := FiniteField.exists_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_eq
    D.k₀ D.k (localClosedPointDegree_pos D Y₀ y) hc ι i
  have ht' : emb t = ι' := RingHom.ext fun a ↦ (ht a).trans (hi a).symm
  obtain ⟨e, he⟩ := hchain t
  let H := DerivedCategory.coefficientFdCohomology E.val j
  have hresult : ∃ a : H.obj (C 0) ≅ H.obj (C t),
      a.hom ≫ H.map (F t) = H.map (F 0) ≫ a.hom := by
    refine ⟨H.mapIso e, ?_⟩
    simpa only [Functor.mapIso_hom, Functor.map_comp] using
      congrArg (fun f ↦ H.map f) he
  let B := { f : Y₀.left.residueField y.val →+* D.k //
    f.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k }
  let P (a b : B) : Prop :=
    ∃ z : H.obj (localPointComplex c.l E.val D c.different Y₀ K
        (localClosedPoint D Y₀ y a.val a.prop)) ≅
        H.obj (localPointComplex c.l E.val D c.different Y₀ K
          (localClosedPoint D Y₀ y b.val b.prop)),
      z.hom ≫ H.map (localClosedFrobenius c.l E.val D c.different Y₀ K y b.val b.prop) =
        H.map (localClosedFrobenius c.l E.val D c.different Y₀ K y a.val a.prop) ≫ z.hom
  have hp : P ⟨emb 0, hemb 0⟩ ⟨emb t, hemb t⟩ := hresult
  have h₀ : (⟨emb 0, hemb 0⟩ : B) = ⟨ι, hι⟩ := by
    apply Subtype.ext
    ext a
    rfl
  have h₁ : (⟨emb t, hemb t⟩ : B) = ⟨ι', hι'⟩ := Subtype.ext ht'
  rw [h₀, h₁] at hp
  simpa only [P, H, localClosedFrobenius, localClosedFrobeniusCohomology,
    localFrobeniusCohomology] using hp

end WeilConjectures
