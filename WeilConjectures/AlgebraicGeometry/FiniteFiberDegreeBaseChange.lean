/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiberDegreeBound

/-!
# Finite fibre degrees under base change

## Main statements

* `AlgebraicGeometry.Scheme.Hom.finite_fiber_degree_pullback`: a finite fibre remains finite
  with the same degree after base change.
* `AlgebraicGeometry.Scheme.Hom.boundsFiberDegrees_pullback_snd`: the same bound works after
  base change.

## References

* Stacks Project, Tags 03J5 and 03J7
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite fibre remains finite with the same degree after arbitrary base change.
(Stacks, Tag 03J5.) -/
lemma finite_fiber_degree_pullback {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (t : T) (hf : IsFinite (f.fiberToSpecResidueField (g t))) :
    IsFinite ((pullback.snd f g).fiberToSpecResidueField t) ∧
      ((pullback.snd f g).fiberToSpecResidueField t).finrankΓ =
        (f.fiberToSpecResidueField (g t)).finrankΓ := by
  let := hf
  have H := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) t
  refine ⟨MorphismProperty.of_isPullback H hf, ?_⟩
  let : IsAffine (pullback f (S.fromSpecResidueField (g t))) :=
    isAffine_of_isAffineHom (f.fiberToSpecResidueField (g t))
  let := (f.fiberToSpecResidueField (g t)).ΓAlgebra
  let := ((pullback.snd f g).fiberToSpecResidueField t).ΓAlgebra
  let := (g.residueFieldMap t).hom.toAlgebra
  obtain ⟨e⟩ := nonempty_algEquiv_tensorProduct_Γ_of_isPullback (g.residueFieldMap t) H
  have e' : TensorProduct (S.residueField (g t)) (T.residueField t) Γ(f.fiber (g t), ⊤)
      ≃ₐ[T.residueField t] Γ((pullback.snd f g).fiber t, ⊤) := e
  change Module.finrank _ _ = Module.finrank _ _
  rw [← e'.toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange

/-- A bound on all finite fibre degrees is preserved by arbitrary base change.
(Stacks, Tag 03J7.) -/
lemma boundsFiberDegrees_pullback_snd {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (n : ℕ) (hf : BoundsFiberDegrees f n) : BoundsFiberDegrees (pullback.snd f g) n := by
  intro t
  obtain ⟨hfin, hdeg⟩ := finite_fiber_degree_pullback f g t (hf (g t)).1
  exact ⟨hfin, hdeg.le.trans (hf (g t)).2⟩

end AlgebraicGeometry.Scheme.Hom
