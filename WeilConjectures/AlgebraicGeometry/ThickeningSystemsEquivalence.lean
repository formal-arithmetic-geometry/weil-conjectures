/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentThickeningSystem
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforward
import WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforwardAdic
import WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforwardLifting
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # Pushforward of coherent thickening systems is an equivalence with adic systems.

## References

* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

set_option autoImplicit false

/-- Pushforward of coherent thickening systems is an equivalence with adic systems.
-/
theorem thickeningSystems_pushforward_equivalence {A : Type v} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    [LocallyOfFiniteType f] [QuasiCompact f] (I : Ideal A)
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ,
      i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (hi₂ : ∀ n : ℕ,
      i n ≫ pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
      pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ≫
          Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))))
    (ai : ∀ n : ℕ, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (aj : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⊣
      Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))))
    [hX : IsNoetherian X]
    (hgeom : (∀ n : ℕ, IsClosedImmersion (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))) ∧
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).ker =
            (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of
            A)).inv.hom)).comap f ^ (n + 1))) :
    ∃ (Φ : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) i ⥤
          @CoherentFormalModule X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f))
        (β : ∀ n : ℕ,
          Φ ⋙ ObjectProperty.ι (IsCoherentFormalModule ((Scheme.IdealSheafData.ofIdealTop (I.map
              (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)) ⋙
            (CategoryTheory.evaluation ℕᵒᵖ X.Modules).obj (op n) ≅
          CoherentThickeningSystem.evaluation (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1)))))) i n ⋙
            Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1))))))),
        Φ.IsEquivalence ∧
        (∀ (M : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) i) (n : ℕ),
          (((Φ.obj M).obj).map (homOfLE (Nat.le_succ n)).op) ≫ (β n).hom.app M =
          (β (n + 1)).hom.app M ≫
            (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
              ((ai n).homEquiv _ _ (M.comparison n).hom) ≫
            (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
              (M.term n) ≫
            (Scheme.Modules.pushforwardCongr (hi n)).hom.app (M.term n)) := by
  have _hsecondProjection := hi₂
  have _hpushforwardAdjunction := aj
  let T : ℕ → Scheme.{v} := fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (I ^ (n + 1)))))
  let j : ∀ n, T n ⟶ X := fun n ↦ pullback.fst f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (I ^ (n + 1)))))
  let J := (Scheme.IdealSheafData.ofIdealTop (I.map
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
  have : ∀ n, IsClosedImmersion (j n) := fun n ↦ (hgeom n).1
  let P := thickeningSystemPushforward j hi ai
  have hP := thickeningSystemPushforward_fullyFaithful j hi ai
  have : P.Full := hP.1
  have : P.Faithful := hP.2
  let Φ : CoherentThickeningSystem T i ⥤ CoherentFormalModule X J :=
    ObjectProperty.lift (IsCoherentFormalModule J) P
      (thickeningSystemPushforward_isAdic j hi ai J hgeom)
  have : Φ.EssSurj := ⟨fun H ↦ by
    obtain ⟨M, ⟨e⟩⟩ := thickeningSystemPushforward_lifting j hi ai J hgeom H
    exact ⟨M, ⟨ObjectProperty.isoMk _ e⟩⟩⟩
  have : Φ.IsEquivalence := {}
  let β := fun n ↦ thickeningSystemPushforwardEvaluation j hi ai n
  refine ⟨Φ, β, inferInstance, ?_⟩
  intro M n
  change ((thickeningSystemPushforward j hi ai).obj M).map
    (homOfLE (Nat.le_succ n)).op ≫ 𝟙 _ = 𝟙 _ ≫ _
  rw [Category.comp_id, Category.id_comp]
  exact thickeningSystemPushforward_transition j hi ai M n

end
end AlgebraicGeometry
