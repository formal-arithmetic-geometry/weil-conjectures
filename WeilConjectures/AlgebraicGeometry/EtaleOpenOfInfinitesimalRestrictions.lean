/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal

/-!
# Étale neighborhoods from quotient restrictions

## References

* Stacks Project, Tags 0GS2 and 0A43
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Étaleness on all infinitesimal restrictions yields an étale open neighborhood of
 the closed fiber (Stacks, Tag 0GS2). -/
theorem etale_open_of_infinitesimal_restrictions
    {A : Type u} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (g : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType g] [QuasiCompact g]
    (h_etale : ∀ n : ℕ, Etale (pullback.snd g (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))))) :
    ∃ W : X.Opens,
      (g : X → Y) ⁻¹' Set.range
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : _ → _) ⊆
          (W : Set X) ∧ Etale (W.ι ≫ g) := by
  let j := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  have hj := quotientBaseChange_closedImmersion_ideal f I
  have : IsClosedImmersion j := hj.1
  apply etale_on_open_of_etale_infinitesimal_neighbourhoods g j j.ker rfl
  intro n
  let jn := pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  have hjn := quotientBaseChange_closedImmersion_ideal f (I ^ (n + 1))
  have : IsClosedImmersion jn := hjn.1
  have hpow : j.ker ^ (n + 1) = jn.ker := by
    rw [hj.2.1, (quotientBaseChange_extendedIdeal_mul_pow f).2 I (n + 1)
      (Nat.le_add_left 1 n)]
    exact hjn.2.1.symm
  rw [hpow]
  have : Etale (pullback.snd g jn) := h_etale n
  let e := pullback.map g jn g jn.imageι (𝟙 X) jn.toImage (𝟙 Y)
    (by simp) (by simp)
  have : IsIso e := by dsimp [e]; infer_instance
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Etale) e]
  simpa [e] using (inferInstance : Etale (pullback.snd g jn ≫ jn.toImage))

end AlgebraicGeometry
