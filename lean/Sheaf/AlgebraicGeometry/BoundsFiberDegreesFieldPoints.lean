/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.FiberDegreeBound
import WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Testing fibre degree bounds on field-valued points

Source: Stacks Project, Morphisms, Lemma Tag 03J5, equivalence of (1) and (2)
(blueprint: lem-weil-pbc-fibre-degree-bound-field-points).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- A nonnegative integer bounds the fibre degrees exactly when every base change to a
field-valued point is finite and has at most that dimension of global sections, with the
algebra structure induced by the second projection.

Source: Stacks Project, Morphisms, Lemma Tag 03J5, equivalence of (1) and (2)
(blueprint: lem-weil-pbc-fibre-degree-bound-field-points).

Proof:
1. From the field-valued condition, take `K = κ(y)` and the canonical map `Spec κ(y) → Y`.
   Its pullback is the fibre at `y`, with the same second projection and algebra structure
   (def-pc-scheme-fibre, def-weil-pbc-fibre-degree-bound). Any other choice of pullback is
   isomorphic over the base; finiteness and dimension are invariant under that isomorphism
   (lem-weil-pbc-isomorphism-finite, lem-weil-pbc-finite-composition).
2. Conversely, `Spec K` has one point `ξ`, whose residue field is canonically isomorphic to
   `K`: localization at zero and quotient by zero are isomorphisms of fields. Thus its
   residue-field inclusion is an isomorphism (lem-weil-pbc-spec-residue-field-identification).
3. Set `y = g(ξ)`. The fibre degree base-change lemma identifies the fibre of the second
   projection at `ξ` as finite over `κ(ξ)`, with degree equal to that of `X_y`, hence at most
   `n` (lem-weil-pbc-fibre-degree-base-change).
4. Pullback along the isomorphism `Spec κ(ξ) → Spec K` identifies this fibre with `X_K`:
   its first projection is an isomorphism by the pullback universal property
   (def-pc-fibre-product).
5. The structure map of `X_K` factors as the inverse of that first projection, the finite
   fibre projection, and the residue-field inclusion. It is finite by finiteness of
   isomorphisms and compositions (lem-weil-pbc-isomorphism-finite,
   lem-weil-pbc-finite-composition).
6. Applying global sections to the commuting projection square gives a bijective additive
   map semilinear along `K ≃ κ(ξ)`. It transports bases, so the dimension of `Γ(X_K, 𝒪)`
   over `K` equals the fibre dimension over `κ(ξ)`, which is at most `n`. -/
theorem boundsFiberDegrees_iff_fieldPoints {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    BoundsFiberDegrees f n ↔
      ∀ (K : Type u) [Field K] (g : Spec (CommRingCat.of K) ⟶ Y),
        IsFinite (pullback.snd f g) ∧ (pullback.snd f g).finrankΓ ≤ n := by
  constructor
  · intro hf K _ g
    let ξ : Spec (CommRingCat.of K) := default
    let h := pullback.snd f g
    let φ := CommRingCat.ofHom (algebraMap K ξ.asIdeal.ResidueField)
    have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr
      ξ.asIdeal.algEquivResidueFieldOfField.bijective
    let e := asIso φ ≪≫ (Scheme.Spec.residueFieldIso (CommRingCat.of K) ξ).symm
    have hjmap : Spec.map e.hom = (Spec (CommRingCat.of K)).fromSpecResidueField ξ := by
      dsimp only [e, Iso.trans_hom, asIso_hom, Iso.symm_hom]
      rw [Spec.map_comp]
      exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField _ ξ
    have : IsIso ((Spec (CommRingCat.of K)).fromSpecResidueField ξ) := by
      rw [← hjmap]
      infer_instance
    have : IsIso (h.fiberι ξ) := by
      dsimp only [Scheme.Hom.fiberι]
      infer_instance
    obtain ⟨hq, hdeg⟩ := finite_fiber_degree_pullback f g ξ (hf (g ξ)).1
    let := hq
    have heq : inv (h.fiberι ξ) ≫ h.fiberToSpecResidueField ξ ≫ Spec.map e.hom = h := by
      rw [hjmap, ← h.fiber_fac, IsIso.inv_hom_id_assoc]
    have hfinite : IsFinite h := by
      rw [← heq]
      infer_instance
    refine ⟨hfinite, ?_⟩
    have hrank := finrankΓ_eq_of_iso h (h.fiberToSpecResidueField ξ)
      (asIso (h.fiberι ξ)).symm e (by simpa only [Iso.symm_hom, asIso_inv] using heq)
    exact hrank.le.trans (hdeg.le.trans (hf (g ξ)).2)
  · intro hf y
    exact hf (Y.residueField y) (Y.fromSpecResidueField y)

end AlgebraicGeometry.Scheme.Hom
