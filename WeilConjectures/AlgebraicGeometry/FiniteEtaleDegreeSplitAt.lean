/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.FiberDegreeOfSplitCofan

/-!
# Splitting neighbourhoods with prescribed degree

## References

* Stacks Project, Tags 04HN and 03SH
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Each point of a small étale object has a neighbourhood on which a finite étale
morphism of degree `d` splits into exactly `d` clopen copies of that neighbourhood
(Stacks, Tags 04HN and 03SH). -/
theorem exists_finiteEtale_degree_split_at
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (d : ℕ) [f.IsFiniteLocallyFreeOfDegree d]
    (W : X.Etale) (w : W.left) :
    ∃ (V : X.Etale) (a : V ⟶ W) (v : V.left),
      a.left v = w ∧
      ∃ (D : ULift.{u} (Fin d) → Scheme.{u}) (i : ∀ j, D j ⟶ pullback f V.hom),
        Nonempty (IsColimit (Cofan.mk (pullback f V.hom) i)) ∧
        (∀ j, IsOpenImmersion (i j) ∧ IsClosedImmersion (i j)) ∧
        (∀ j, IsIso (i j ≫ pullback.snd f V.hom)) := by
  classical
  let p := pullback.snd f W.hom
  obtain ⟨U, g, v, hg, hv, J, D, i, hJ, hc, hi, hp⟩ :=
    finite_etale_etale_local_split p w
  let : Etale g := hg
  let : Finite J := hJ
  let : Fintype J := Fintype.ofFinite J
  have hpi (j : J) : IsIso (i j ≫ pullback.snd p g) := by
    obtain ⟨e, he⟩ := hp j
    rw [← he]
    infer_instance
  have hd : Nat.card J = d := by
    rw [← Scheme.Hom.fiberDegree_eq_nat_card_of_split_cofan
      (pullback.snd p g) D i hc hpi v]
    rw [Scheme.Hom.fiberDegree_of_isPullback p (.of_hasPullback p g) v]
    rw [Scheme.Hom.fiberDegree_of_isPullback f (.of_hasPullback f W.hom) (g v)]
    exact Scheme.Hom.IsFiniteLocallyFreeOfDegree.fiberDegree_eq _
  let V : X.Etale := Scheme.Etale.mk (g ≫ W.hom)
  let a : V ⟶ W := MorphismProperty.Over.homMk g rfl
  let e := pullbackLeftPullbackSndIso f W.hom g
  let b : ∀ j, D j ⟶ pullback f V.hom := fun j ↦ i j ≫ e.hom
  have hb : Nonempty (IsColimit (Cofan.mk (pullback f V.hom) b)) := by
    refine ⟨IsColimit.ofIsoColimit hc.some ?_⟩
    exact Cofan.ext e (fun j ↦ rfl)
  let t : ULift.{u} (Fin d) ≃ J :=
    Equiv.ulift.trans (Fintype.equivFinOfCardEq
      (show Fintype.card J = d by simpa only [Nat.card_eq_fintype_card] using hd)).symm
  refine ⟨V, a, v, hv, D ∘ t, fun j ↦ b (t j), ?_, ?_, ?_⟩
  · exact ⟨(Cofan.isColimitEquivOfEquiv t (Cofan.mk _ b)) hb.some⟩
  · intro j
    let : IsOpenImmersion (i (t j)) := (hi (t j)).1
    let : IsClosedImmersion (i (t j)) := (hi (t j)).2
    exact ⟨inferInstance, inferInstance⟩
  · intro j
    have he : b (t j) ≫ pullback.snd f V.hom =
        i (t j) ≫ pullback.snd p g := by
      change i (t j) ≫ e.hom ≫ pullback.snd f (g ≫ W.hom) = _
      rw [pullbackLeftPullbackSndIso_hom_snd]
    rw [he]
    exact hpi (t j)

end AlgebraicGeometry.Etale
