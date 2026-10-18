/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-!
# Projective morphisms with finite geometric fibres are finite

Source: the Weil conjectures blueprint, chapter `sec-smooth-purity`, unit `sk-prop-sf-cbc`,
lemma `lem-fin-projective-finite-fibres`; Stacks Project, Tag 02OG, using Tag 01WC
(blueprint: lem-fin-projective-finite-fibres).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A projective morphism with Noetherian target and finite geometric fibres is finite.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-projective-finite-fibres`;
Stacks Project, Tags 01WC and 02OG (blueprint: lem-fin-projective-finite-fibres).

Proof: projectivity supplies properness. For each `t`, the geometric point has image `{t}`:
its domain is the nonempty spectrum of an algebraically closed field, and its residue-field
factor maps every point to `t`. The pullback range formula therefore identifies the image
of the geometric fibre in `D` with `f ⁻¹' {t}`. This image of finitely many points is finite,
even when empty. Apply the library's proper-with-finite-fibres criterion (Tag 02OG). -/
theorem isFinite_of_isProjective_of_finite_geometricFibres
    {D T : Scheme.{u}} (f : D ⟶ T) [IsProjective f]
    [IsLocallyNoetherian T] [CompactSpace T]
    (hf : ∀ t : T, Finite ((pullback f
      (Spec.map (CommRingCat.ofHom
        (algebraMap (T.residueField t) (AlgebraicClosure (T.residueField t)))) ≫
          T.fromSpecResidueField t)) : Scheme.{u})) :
    IsFinite f := by
  apply (IsFinite.iff_isProper_and_finite_preimage_singleton f).mpr
  refine ⟨inferInstance, fun t ↦ ?_⟩
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap (T.residueField t) (AlgebraicClosure (T.residueField t)))) ≫
      T.fromSpecResidueField t
  have : Finite ((pullback f g) : Scheme.{u}) := hf t
  have hg : Set.range g = {t} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact T.fromSpecResidueField_apply t _
    · intro hx
      exact ⟨IsLocalRing.closedPoint _,
        (T.fromSpecResidueField_apply t _).trans (Set.mem_singleton_iff.mp hx).symm⟩
  rw [← hg, ← Scheme.Pullback.range_fst]
  exact Set.finite_range (pullback.fst f g)

end AlgebraicGeometry
