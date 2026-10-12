module

public import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension
public import WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform
public import WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

/-- The coordinate in `k̄` of a geometric point `t : Spec k̄ ⟶ 𝔸¹` of the affine line. -/
noncomputable def affineLine.coordOfPoint (t : Spec (.of (AlgebraicClosure k₀)) ⟶ affineLine k₀) :
    AlgebraicClosure k₀ :=
  (Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).hom.hom
    (t.appTop (AffineSpace.coord _ PUnit.unit))

omit [Finite k₀] in
/-- **The kernel along a horizontal line.** Let `i : Z ⟶ 𝔸¹` be a morphism over `k₀`, and
`X' = Z ×_{𝔸¹} (𝔸¹ × 𝔸¹)` its base change along the first projection, with projections `q` to
`Z` and `i'` to the plane. A section `σ` of the base change to `k̄` of `X' ⟶ 𝔸¹`
(the second projection) lying over the geometric point `t` of `Z` is `y ↦ (t, y)`; along it
the multiplication `μ` becomes the geometric multiplication by the coordinate of `t`. -/
lemma geometricFiberMap_mul_eq_geometricSMul {Z X' : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of k₀))] [X'.Over (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ affineLine k₀) [i.IsOver (Spec (CommRingCat.of k₀))] (q : X' ⟶ Z)
    [q.IsOver (Spec (CommRingCat.of k₀))] (i' : X' ⟶ affinePlane k₀)
    [i'.IsOver (Spec (CommRingCat.of k₀))] (hw : i' ≫ affinePlane.fst k₀ = q ≫ i)
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (σ : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (X' ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hσq : σ ≫ Scheme.Hom.geometricFiberMap q (comp_over q _) =
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫ t)
    (hσπ : σ ≫ Scheme.Hom.geometricFiberMap (i' ≫ affinePlane.snd k₀)
      (comp_over (i' ≫ affinePlane.snd k₀) _) = 𝟙 _) :
    σ ≫ Scheme.Hom.geometricFiberMap (i' ≫ affinePlane.mul k₀)
      (comp_over (i' ≫ affinePlane.mul k₀) _) =
      affineLine.geometricSMul k₀ (affineLine.coordOfPoint
        (t ≫ (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i)) := by
  have h₁ : σ ≫ (X' ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i' ≫
      affinePlane.snd k₀ = (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj := by
    rw [← Scheme.Hom.geometricFiberMap_comp_geometricFiberProj (i' ≫ affinePlane.snd k₀)
        (comp_over (i' ≫ affinePlane.snd k₀) _), ← Category.assoc, hσπ, Category.id_comp]
  have h₂ : σ ≫ (X' ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i' ≫
      affinePlane.fst k₀ =
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫ t ≫
          (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i := by
    rw [hw, ← Scheme.Hom.geometricFiberMap_comp_geometricFiberProj_assoc q (comp_over q _),
      ← Category.assoc σ, hσq, Category.assoc]
  have h₃ : σ ≫ (X' ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure =
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure := by
    rw [← Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure
      (i' ≫ affinePlane.snd k₀) (comp_over (i' ≫ affinePlane.snd k₀) _), ← Category.assoc, hσπ,
      Category.id_comp]
  refine Scheme.Hom.geometricFiber_hom_ext _ ?_ ?_
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      affineLine.geometricSMul_comp_geometricFiberProj, affinePlane.mul]
    simp only [← Category.assoc]
    rw [AffineSpace.comp_homOfVector]
    have key (g : affinePlane k₀ ⟶ affineLine k₀) (c : Γ(affineLine k₀, ⊤)) :
        ((σ ≫ (X' ↘ Spec (CommRingCat.of k₀)).geometricFiberProj) ≫ i').appTop (g.appTop c) =
          (σ ≫ (X' ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i' ≫ g).appTop c := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      simp only [Category.assoc]
    refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
    · rw [AffineSpace.homOfVector_over, AffineSpace.homOfVector_over,
        ← comp_over (affinePlane.snd k₀) (Spec (CommRingCat.of k₀))]
      simp only [Category.assoc]
      rw [reassoc_of% h₁,
        Scheme.Hom.geometricFiber_condition]
    · simp only [AffineSpace.homOfVector_appTop_coord, Function.comp_apply, map_mul]
      rw [key, key, h₁, h₂, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      simp [affineLine.coordOfPoint, affineLine.geometricConst]
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure,
      affineLine.geometricSMul_comp_geometricFiberToAlgebraicClosure, ← h₃]

end AlgebraicGeometry
