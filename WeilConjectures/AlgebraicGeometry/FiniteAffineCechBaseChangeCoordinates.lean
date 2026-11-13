/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechModel
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.AdditiveAlternatingCechCoordinates
import WeilConjectures.AlgebraicGeometry.FiniteAffineCechCoefficientBaseChange

/-! # Local section formulas for the pulled-back finite affine Čech model

## References

* [Stacks Project, Tag 02KE](https://stacks.math.columbia.edu/tag/02KE)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 500000 in
-- Elaborating the nested complex functors and dependent coordinate sums needs this budget.
/-- The pulled-back specified model has the ordered section formulas, naturally on all
opens and linearly over their local rings. This is a termwise statement, before homology
(Stacks, Tag 02KE). -/
theorem finiteAffineCech_baseChange_coordinates {X T : Scheme.{u}} (f : X ⟶ T)
    [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U) {r : ℕ}
    (V : Fin r → (f ⁻¹ᵁ U).toScheme.Opens) (hV : ∀ i, IsAffineOpen (V i))
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (hW : ∀ i, W₀ i = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ V i.down)) :
    let K := ((Modules.pullback g).mapHomologicalComplex _).obj
      (finiteAffineCechModel (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι) V)
    let M := (Modules.pullback g').obj F
    ∃ a : ∀ (p : ℕ) (B : T'.Opens),
      Γ(K.X (p : ℤ), B) ≃+
        (∀ t : Fin (p + 1) ↪o Fin r,
          Γ(M, alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B)),
      (∀ (p : ℕ) {B C : T'.Opens} (i : B ⟶ C)
        (s : Γ(K.X (p : ℤ), C)) (t : Fin (p + 1) ↪o Fin r),
      a p B ((K.X (p : ℤ)).presheaf.map i.op s) t =
        M.presheaf.map (homOfLE (inf_le_inf le_rfl
          ((TopologicalSpace.Opens.map f'.base).map i).le)).op (a p C s t)) ∧
      (∀ (p : ℕ) (B : T'.Opens) (b : Γ(T', B))
        (s : Γ(K.X (p : ℤ), B)) (t : Fin (p + 1) ↪o Fin r),
      a p B (b • s) t =
        X'.presheaf.map (homOfLE (show
          alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B ≤ f' ⁻¹ᵁ B
            from inf_le_right)).op (f'.app B b) • a p B s t) ∧
      (∀ (p : ℕ) (B : T'.Opens) (s : Γ(K.X (p : ℤ), B))
        (t : Fin (p + 2) ↪o Fin r),
      a (p + 1) B ((K.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B s) t =
        ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
          M.presheaf.map (homOfLE (inf_le_inf
            (alternatingCechIntersection_face_le (fun i ↦ W₀ ⟨i⟩) p t j) le_rfl)).op
              (a p B s ((Fin.succAboveOrderEmb j).trans t))) := by
  classical
  let G := (F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat
  let H := ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
      ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom) ⋙
    tilde.functor Γ(U.toScheme, ⊤) ⋙
    Modules.pullback U.toScheme.toSpecΓ ⋙ Modules.pullback g
  let L := (H.mapHomologicalComplex _).obj
    ((alternatingCechComplex V G).extend ComplexShape.embeddingUpNat)
  obtain ⟨e, en, el, ed⟩ := additive_alternatingCech_coordinates V G H
  obtain ⟨c, cn, cl, cf⟩ :=
    finiteAffineCech_coefficient_baseChange f F U hU V hV g g' f' sq W₀ hW
  refine ⟨fun p B ↦ (e p B).trans (AddEquiv.piCongrRight fun t ↦ c p t B), ?_, ?_, ?_⟩
  · intro p B C i s t
    change c p t B (e p B ((L.X (p : ℤ)).presheaf.map i.op s) t) = _
    rw [en]
    exact cn p t i _
  · intro p B b s t
    change c p t B (e p B (b • s) t) = _
    rw [el]
    exact cl p t B b _
  · intro p B s t
    change c (p + 1) t B (e (p + 1) B ((L.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B s) t) = _
    rw [ed, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul, cf]
    rfl


end AlgebraicGeometry.Scheme.Modules
