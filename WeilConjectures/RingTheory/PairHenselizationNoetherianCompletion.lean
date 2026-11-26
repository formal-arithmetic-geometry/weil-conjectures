/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PairHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.PairHenselizationFlatQuotients
import WeilConjectures.RingTheory.PairHenselizationCompletionData
import WeilConjectures.RingTheory.PairHenselizationCompletionFaithfullyFlat
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Noetherian henselization of a pair and its completion

The henselization of a Noetherian pair `(A, I)` is Noetherian, flat over `A`, has the same
`I`-adic completion as `A`, and maps faithfully flatly to that completion.

## Implementation details

The colimit cocone is the presentation in `pair_henselization`; its vertex is `Aʰ` and
`c.pt.hom.hom` is the structure map. The condition on every quotient projection specifies that
`θ` is the map induced by this structure map, not merely an abstract ring isomorphism.

Each étale stage is Noetherian with the same completion as `A`, so the completion maps of the
stages are flat and their colimit `Aʰ → Â` is flat. The extended ideal lies in the Jacobson
radical, which gives faithful flatness; Noetherianity of `Aʰ` follows by faithfully flat descent
from the Noetherian completion.

## References

* [Stacks, Tag 0AGV]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- The henselization `Aʰ` of a Noetherian pair is Noetherian and flat over the base, its
completion is identified with that of the base by the isomorphism `θ` induced by the structure
map, and the resulting map `Aʰ → Â` is faithfully flat. -/
theorem pair_henselization_noetherian_completion
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c) :
    IsNoetherianRing c.pt.right ∧ c.pt.hom.hom.Flat ∧
      ∃ θ : AdicCompletion I A ≃+*
          AdicCompletion (I.map c.pt.hom.hom) c.pt.right,
        (∀ (n : ℕ) (x : AdicCompletion I A) (a : A),
          AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) a →
          AdicCompletion.evalₐ (I.map c.pt.hom.hom) n (θ x) =
            Ideal.Quotient.mk ((I.map c.pt.hom.hom) ^ n) (c.pt.hom.hom a)) ∧
        (θ.symm.toRingHom.comp
            (algebraMap c.pt.right (AdicCompletion (I.map c.pt.hom.hom) c.pt.right))).comp
            c.pt.hom.hom = algebraMap A (AdicCompletion I A) ∧
        RingHom.FaithfullyFlat
          (θ.symm.toRingHom.comp
            (algebraMap c.pt.right (AdicCompletion (I.map c.pt.hom.hom) c.pt.right))) := by
  classical
  -- Only the witness and projections are needed; keep the completion data intact.
  have hflatquot := pair_henselization_flat_quotients A I c hc
  have hcompletion :=
    pair_henselization_completion_data A c.pt.right I c.pt.hom.hom hflatquot.2
  let θ := hcompletion.choose
  have hθeval := hcompletion.choose_spec.1
  have hθmap := hcompletion.choose_spec.2
  have hfaith := pair_henselization_completion_faithfullyFlat A I c hc θ hθeval
  let γ := θ.symm.toRingHom.comp
    (algebraMap c.pt.right (AdicCompletion (I.map c.pt.hom.hom) c.pt.right))
  let : Algebra c.pt.right (AdicCompletion I A) := γ.toAlgebra
  let : Module.FaithfullyFlat c.pt.right (AdicCompletion I A) := hfaith
  let := AdicCompletion.isNoetherianRing I
  have hnoeth : IsNoetherianRing c.pt.right :=
    Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (R := c.pt.right) (M := c.pt.right) (A := AdicCompletion I A)
      (isNoetherian_of_linearEquiv
        (Algebra.TensorProduct.rid c.pt.right (AdicCompletion I A)
          (AdicCompletion I A)).symm.toLinearEquiv)
  exact ⟨hnoeth, hflatquot.1, θ, hθeval, hθmap, hfaith⟩

end RingTheory
