/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric

/-! # The geometric map for return restriction -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.WeilSheaf

/-- The structural square induces a map of geometric fibers intertwining the return power.
Source: blueprint `thm-zl-real-mixed-by-curves`, paragraphs 1--3.
(blueprint: lem-zl-clopen-return-data).

Proof: Identify the two algebraic closures over k₀. The map into the geometric
fiber of X is the pullback lift of the composite Cbar → C → X and the chosen map
Cbar → Spec k₀bar. The structural square supplies the pullback compatibility.
Both projections of the Frobenius square agree: the projection to X is fixed,
and the projection to the algebraic closure is the finite-field identity
Fr(k₁) = Fr(k₀)^r under the chosen identification. The pullback universal property
therefore gives the asserted square. No immersion hypothesis is needed. -/
theorem exists_clopen_return_geometric_map
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] [Algebra.IsAlgebraic k₀ k₁]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    (c : C ⟶ X)
    (hc : c ≫ (X ↘ Spec (.of k₀)) =
      (C ↘ Spec (.of k₁)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)))
    (r : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r) :
    ∃ v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber,
      v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
        (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c ∧
      v ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
        (C ↘ Spec (.of k₁)).geometricFiberToAlgebraicClosure ≫
          Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₁).symm.toRingHom) ∧
      (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ v =
        v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom := by
  let f := X ↘ Spec (.of k₀)
  let g := C ↘ Spec (.of k₁)
  let a := Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₁).toRingHom)
  let b := Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₁).symm.toRingHom)
  have ha : IsIso a :=
    (Scheme.Spec.mapIso (algebraicClosureAlgEquiv k₀ k₁).toRingEquiv.toCommRingCatIso.op).isIso_hom
  have hba : b ≫ a = 𝟙 _ :=
    (Scheme.Spec.mapIso (algebraicClosureAlgEquiv k₀ k₁).toRingEquiv.toCommRingCatIso.op).inv_hom_id
  have hb : (specGeometricFrobenius k₁).hom ≫ b =
      b ≫ (specGeometricFrobenius k₀ ^ r).hom := by
    rw [← cancel_mono a, Category.assoc, Category.assoc,
      ← Scheme.Hom.spec_algebraicClosureAlgEquiv_comp_specGeometricFrobenius r hr,
      ← Category.assoc b, hba, Category.id_comp, Category.comp_id]
  let v : g.geometricFiber ⟶ f.geometricFiber :=
    pullback.lift (g.geometricFiberProj ≫ c) (g.geometricFiberToAlgebraicClosure ≫ b) (by
      rw [Category.assoc, hc, Scheme.Hom.geometricFiber_condition_assoc, Category.assoc]
      refine congrArg (_ ≫ ·)
        ((spec_map_comp_spec_map_eq _ _ (algebraMap k₀ _) fun x ↦ ?_).trans
          (spec_map_comp_spec_map_eq _ _ _ fun x ↦ ?_).symm)
      · exact (IsScalarTower.algebraMap_apply _ _ _ x).symm
      · simp)
  have hp : v ≫ f.geometricFiberProj = g.geometricFiberProj ≫ c :=
    pullback.lift_fst _ _ _
  have hq : v ≫ f.geometricFiberToAlgebraicClosure =
      g.geometricFiberToAlgebraicClosure ≫ b := pullback.lift_snd _ _ _
  refine ⟨v, hp, hq, ?_⟩
  apply pullback.hom_ext
  · change g.geometricGaloisFrobenius.hom ≫ v ≫ f.geometricFiberProj =
      v ≫ (f.geometricGaloisFrobenius ^ r).hom ≫ f.geometricFiberProj
    simp only [hp,
      Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj_assoc,
      Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]
  · change g.geometricGaloisFrobenius.hom ≫ v ≫ f.geometricFiberToAlgebraicClosure =
      v ≫ (f.geometricGaloisFrobenius ^ r).hom ≫ f.geometricFiberToAlgebraicClosure
    simp only [hq,
      Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure_assoc,
      Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure]
    rw [← Category.assoc v, hq, Category.assoc]
    exact congrArg (g.geometricFiberToAlgebraicClosure ≫ ·) hb

end AlgebraicGeometry.WeilSheaf
