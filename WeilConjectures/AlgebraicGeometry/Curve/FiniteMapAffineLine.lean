/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Curve.FiniteMapToLine
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension
import Mathlib.FieldTheory.IsSepClosed

/-!
# A finite generically étale map from an open enlargement of an affine curve

Source: Weil conjectures blueprint, `sec-deligne-laumon-a1/sk-thm-dl-a1-upper`,
`lem-a1-finite-map-curve.md` (blueprint: lem-a1-finite-map-curve).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits WeilConjectures

namespace AlgebraicGeometry

/-- A smooth affine curve over the global finite field, geometrically a connected curve,
has a smooth geometrically connected open enlargement with finite complement and a finite
morphism to the affine line which is étale on a dense open of its source.
Source: Weil conjectures blueprint, `lem-a1-finite-map-curve.md`
(blueprint: lem-a1-finite-map-curve).

Proof:
1. The connected geometric curve hypothesis gives geometric connectedness over the
   finite field. Dimension is unchanged by field extension, so smoothness has relative
   dimension one.
2. Apply the existing finite-field affine-curve theorem
   `AffineSpace.exists_isFinite_etale_morphismRestrict_of_finite`. Take the enlargement
   to be the original curve and its inclusion to be the identity. Reindex the affine
   line from `PUnit` to `ULift (Fin 1)` by its canonical isomorphism.
3. Pull the dense étale target open back to the source. It is dense by
   `dense_preimage_of_isIntegralHom`, since a finite map between smooth curves is
   integral. The source restriction is étale by the restriction identity, followed
   by the affine-line isomorphism. -/
theorem exists_finite_genericallyEtale_curve_enlargement
    (D : FiniteFieldDatum.{u}) (C₀ : Over (Spec (.of D.k₀)))
    [IsCurve C₀.hom] [Smooth C₀.hom] [IsAffine C₀.left]
    [IsConnectedCurve (D.geometricFiber C₀).hom] :
    ∃ (C₀' : Over (Spec (.of D.k₀))) (hC₀' : IsCurve C₀'.hom),
      Smooth C₀'.hom ∧
      IsConnectedCurve
        (@FiniteFieldDatum.geometricFiber D C₀'
          hC₀'.toLocallyOfFiniteType hC₀'.toQuasiCompact).hom ∧
      ∃ (j : C₀ ⟶ C₀') (g : C₀'.left ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of D.k₀))),
        IsOpenImmersion j.left ∧ DenseRange j.left ∧
        (Set.range j.left)ᶜ.Finite ∧
        g ≫ (𝔸(ULift.{u} (Fin 1); Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) = C₀'.hom ∧
        IsFinite g ∧
        ∃ U : C₀'.left.Opens, Dense (U : Set C₀'.left) ∧ Etale (U.ι ≫ g) := by
  have : ConnectedSpace (D.geometricFiber C₀).left :=
    IsConnectedCurve.connectedSpace' (D.geometricFiber C₀).hom
  have : IsAlgClosed D.k := D.isAlgClosure.isAlgClosed
  have : GeometricallyConnected C₀.hom :=
    (geometricallyConnected_iff_of_fieldExtension (k := D.k₀) (k' := D.k) C₀.left).mpr
      (GeometricallyConnected.of_connectedSpace_of_isSepClosed (D.geometricFiber C₀).hom)
  have : ConnectedSpace C₀.left := GeometricallyConnected.connectedSpace_of_subsingleton C₀.hom
  have : IsLocallyNoetherian C₀.left := LocallyOfFiniteType.isLocallyNoetherian C₀.hom
  have : IsRegular C₀.left := IsRegular.of_smooth C₀.hom
  have : IrreducibleSpace C₀.left := IsRegular.irreducibleSpace C₀.left
  have hdim : topologicalKrullDim C₀.left = 1 := by
    have heq := topologicalKrullDim_pullback_eq_of_field C₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    exact heq.symm.trans (IsConnectedCurve.krullDim_eq_one
      (f := (D.geometricFiber C₀).hom))
  have hsmooth : SmoothOfRelativeDimension 1 C₀.hom :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq C₀.hom 1).mpr hdim
  let : C₀.left.Over (Spec (.of D.k₀)) := ⟨C₀.hom⟩
  have : SmoothOfRelativeDimension 1 (C₀.left ↘ Spec (.of D.k₀)) := by
    change SmoothOfRelativeDimension 1 C₀.hom
    exact hsmooth
  have : GeometricallyConnected (C₀.left ↘ Spec (.of D.k₀)) := by
    change GeometricallyConnected C₀.hom
    infer_instance
  obtain ⟨g₀, hg₀, hfin, V, hV, hEt⟩ :=
    AffineSpace.exists_isFinite_etale_morphismRestrict_of_finite (k := D.k₀) C₀.left
  let E : 𝔸(PUnit.{u + 1}; Spec (.of D.k₀)) ≅
      𝔸(ULift.{u} (Fin 1); Spec (.of D.k₀)) :=
    AffineSpace.reindexIso _ (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit)
  let g := g₀ ≫ E.hom
  refine ⟨C₀, inferInstance, inferInstance, inferInstance, 𝟙 _, g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact denseRange_id
  · simp
  · have hE : E.hom ≫
        (𝔸(ULift.{u} (Fin 1); Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) =
        𝔸(PUnit.{u + 1}; Spec (.of D.k₀)) ↘ Spec (.of D.k₀) := by
      dsimp [E]
      rw [AffineSpace.reindexIso_hom, AffineSpace.reindex_over]
    dsimp [g]
    rw [Category.assoc, hE]
    exact hg₀.1
  · infer_instance
  · have : IsFinite g₀ := hfin
    let U : C₀.left.Opens := g₀ ⁻¹ᵁ V
    refine ⟨U, ?_, ?_⟩
    · change Dense (g₀.base ⁻¹' (V : Set _))
      have : SmoothOfRelativeDimension 1
          (𝔸(PUnit.{u + 1}; Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) :=
        AffineSpace.smoothOfRelativeDimension_one_of_isOpenImmersion (𝟙 _)
      exact dense_preimage_of_isIntegralHom C₀.hom
        (𝔸(PUnit.{u + 1}; Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) g₀
        V.isOpen hV.nonempty
    · have : Etale (g₀ ∣_ V) := hEt
      change Etale ((g₀ ⁻¹ᵁ V).ι ≫ g₀ ≫ E.hom)
      rw [← Category.assoc, ← morphismRestrict_ι g₀ V]
      infer_instance

end AlgebraicGeometry
